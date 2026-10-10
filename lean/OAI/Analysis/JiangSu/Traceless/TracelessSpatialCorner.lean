import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CStarAlgebras.FourEdgeGroupSurgery

namespace OAI

section

section

noncomputable section
open scoped TensorProduct InnerProductSpace
open UniformSpace.Completion

namespace CurrentMain.Spatial
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

abbrev SpatialHilbert (H K : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] :=
  UniformSpace.Completion (H ⊗[ℂ] K)

def spatialTensorOp (S : H →L[ℂ] H) (T : K →L[ℂ] K) :
    SpatialHilbert H K →L[ℂ] SpatialHilbert H K :=
  (TensorProduct.mapL S T).completion

@[simp] lemma spatialTensorOp_coe (S : H →L[ℂ] H) (T : K →L[ℂ] K) (x : H ⊗[ℂ] K) :
    spatialTensorOp S T x = (TensorProduct.mapL S T x : SpatialHilbert H K) := by
  simp [spatialTensorOp]

lemma spatialTensorOp_ext {S T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K}
    (h : ∀ x : H, ∀ y : K, S (x ⊗ₜ[ℂ] y : H ⊗[ℂ] K) = T (x ⊗ₜ[ℂ] y : H ⊗[ℂ] K)) : S = T := by
  apply ContinuousLinearMap.ext
  intro z
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq S.continuous T.continuous
  | ih z =>
    induction z using TensorProduct.inductionOn with
    | tmul x y => exact h x y
    | add x y hx hy => simpa [coe_add] using congrArg₂ (· + ·) hx hy

@[simp] lemma spatialTensorOp_zero_left (T : K →L[ℂ] K) : spatialTensorOp (0 : H →L[ℂ] H) T = 0 := by
  apply spatialTensorOp_ext; intro x y; simp
@[simp] lemma spatialTensorOp_zero_right (S : H →L[ℂ] H) : spatialTensorOp S (0 : K →L[ℂ] K) = 0 := by
  apply spatialTensorOp_ext; intro x y; simp
lemma spatialTensorOp_add_left (S₁ S₂ : H →L[ℂ] H) (T : K →L[ℂ] K) :
    spatialTensorOp (S₁+S₂) T = spatialTensorOp S₁ T + spatialTensorOp S₂ T := by
  apply spatialTensorOp_ext; intro x y; simp [TensorProduct.add_tmul, coe_add]
lemma spatialTensorOp_add_right (S : H →L[ℂ] H) (T₁ T₂ : K →L[ℂ] K) :
    spatialTensorOp S (T₁+T₂) = spatialTensorOp S T₁ + spatialTensorOp S T₂ := by
  apply spatialTensorOp_ext; intro x y; simp [TensorProduct.tmul_add, coe_add]
lemma spatialTensorOp_smul_left (c : ℂ) (S : H →L[ℂ] H) (T : K →L[ℂ] K) :
    spatialTensorOp (c • S) T = c • spatialTensorOp S T := by
  apply spatialTensorOp_ext; intro x y; simp only [spatialTensorOp_coe, TensorProduct.mapL_tmul, smul_apply]
  rw [← TensorProduct.smul_tmul', coe_smul]
lemma spatialTensorOp_smul_right (c : ℂ) (S : H →L[ℂ] H) (T : K →L[ℂ] K) :
    spatialTensorOp S (c • T) = c • spatialTensorOp S T := by
  apply spatialTensorOp_ext; intro x y; simp
lemma spatialTensorOp_mul (S₁ S₂ : H →L[ℂ] H) (T₁ T₂ : K →L[ℂ] K) :
    spatialTensorOp (S₁*S₂) (T₁*T₂) = spatialTensorOp S₁ T₁ * spatialTensorOp S₂ T₂ := by
  apply spatialTensorOp_ext; intro x y; simp

private lemma completion_opNorm_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (f : E →L[ℂ] F) : ‖f.completion‖ ≤ ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f)
  intro z
  induction z using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_le <;> fun_prop
  | ih z => simpa using f.le_opNorm z

lemma spatialTensorOp_norm_le (S : H →L[ℂ] H) (T : K →L[ℂ] K) :
    ‖spatialTensorOp S T‖ ≤ ‖S‖ * ‖T‖ :=
  (completion_opNorm_le (TensorProduct.mapL S T)).trans (TensorProduct.norm_mapL_le S T)

variable [CompleteSpace H] [CompleteSpace K]
lemma spatialTensorOp_star (S : H →L[ℂ] H) (T : K →L[ℂ] K) :
    spatialTensorOp (star S) (star T) = star (spatialTensorOp S T) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x y =>
    induction x using TensorProduct.inductionOn with
    | add x₁ x₂ h₁ h₂ => simpa [coe_add, inner_add_left, inner_add_right] using congrArg₂ (· + ·) h₁ h₂
    | tmul x₁ x₂ =>
      induction y using TensorProduct.inductionOn with
      | add y₁ y₂ h₁ h₂ => simpa [coe_add, inner_add_left, inner_add_right] using congrArg₂ (· + ·) h₁ h₂
      | tmul y₁ y₂ => simp [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
end CurrentMain.Spatial
end

section

noncomputable section
open scoped Topology InnerProductSpace

namespace CurrentMain.Compact
variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def rankOneGenerators : Set (H →L[ℂ] H) := {T | ∃ x y : H, T = InnerProductSpace.rankOne ℂ x y}

def finiteRankAlgebra : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H) :=
  NonUnitalStarAlgebra.adjoin ℂ (rankOneGenerators H)

def compactOperatorAlgebra : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H) :=
  (finiteRankAlgebra H).topologicalClosure

instance compactOperatorAlgebra_closed : IsClosed (compactOperatorAlgebra H : Set (H →L[ℂ] H)) :=
  NonUnitalStarSubalgebra.isClosed_topologicalClosure _

abbrev CompactOperators := compactOperatorAlgebra H

instance : NonUnitalCStarAlgebra (CompactOperators H) :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra (compactOperatorAlgebra H)

variable {H}
omit [CompleteSpace H] in
lemma rankOne_isCompact (x y : H) : IsCompactOperator (InnerProductSpace.rankOne ℂ x y) := by
  have h := isCompactOperator_of_locallyCompactSpace_dom (innerSL ℂ y)
  change IsCompactOperator (fun z : H => inner ℂ y z • x)
  exact h.clm_comp (ContinuousLinearMap.toSpanSingleton ℂ x)

lemma finiteRankAlgebra_compact (T : H →L[ℂ] H) (hT : T ∈ finiteRankAlgebra H) :
    IsCompactOperator T ∧ IsCompactOperator (star T : H →L[ℂ] H) := by
  induction hT using NonUnitalStarAlgebra.adjoin_induction with
  | mem T hT =>
    obtain ⟨x,y,rfl⟩ := hT
    exact ⟨rankOne_isCompact x y, by rw [ContinuousLinearMap.star_eq_adjoint, InnerProductSpace.adjoint_rankOne]; exact rankOne_isCompact y x⟩
  | zero => exact ⟨isCompactOperator_zero, by simpa using (isCompactOperator_zero : IsCompactOperator (0 : H →L[ℂ] H))⟩
  | add T S _ _ hT hS =>
    exact ⟨hT.1.add hS.1, by rw [star_add]; exact hT.2.add hS.2⟩
  | mul T S _ _ hT hS =>
    exact ⟨hT.1.comp_clm S, by rw [star_mul]; exact hS.2.comp_clm (star T)⟩
  | smul c T _ hT =>
    exact ⟨hT.1.smul c, by rw [star_smul]; exact hT.2.smul (star c)⟩
  | star T _ hT => exact ⟨hT.2, by simpa only [star_star] using hT.1⟩

theorem compactOperators_areCompact (T : CompactOperators H) : IsCompactOperator (T : H →L[ℂ] H) := by
  exact closure_minimal
    (fun operator hoperator => (finiteRankAlgebra_compact operator hoperator).1)
    isClosed_setOfPred_isCompactOperator T.2

theorem rankOne_mem_compactOperators (x y : H) :
    InnerProductSpace.rankOne ℂ x y ∈ compactOperatorAlgebra H :=
  NonUnitalStarSubalgebra.le_topologicalClosure _ (NonUnitalStarAlgebra.subset_adjoin ℂ _ ⟨x,y,rfl⟩)

abbrev StandardHilbert := lp (fun _ : ℕ => ℂ) 2

abbrev StandardCompacts := CompactOperators StandardHilbert
end CurrentMain.Compact
end

section

noncomputable section
open scoped Topology InnerProductSpace

namespace CurrentMain.Compact

def standardVector (i : ℕ) : StandardHilbert := lp.single 2 i (1 : ℂ)
lemma inner_standardVector (i j : ℕ) : inner ℂ (standardVector i) (standardVector j) = if i=j then 1 else 0 := by
  simp [standardVector, lp.inner_single_left, Pi.single_apply]
lemma norm_standardVector (i : ℕ) : ‖standardVector i‖ = 1 := by
  simp [standardVector, lp.norm_single]

def compactMatrixUnit (i j : ℕ) : StandardCompacts :=
  ⟨InnerProductSpace.rankOne ℂ (standardVector i) (standardVector j), rankOne_mem_compactOperators _ _⟩

@[simp] theorem compactMatrixUnit_star (i j : ℕ) : star (compactMatrixUnit i j) = compactMatrixUnit j i := by
  apply Subtype.ext
  exact InnerProductSpace.adjoint_rankOne _ _

@[simp] theorem compactMatrixUnit_mul (i j k l : ℕ) :
    compactMatrixUnit i j * compactMatrixUnit k l = if j=k then compactMatrixUnit i l else 0 := by
  apply Subtype.ext
  change InnerProductSpace.rankOne ℂ (standardVector i) (standardVector j) ∘L
    InnerProductSpace.rankOne ℂ (standardVector k) (standardVector l) = _
  rw [InnerProductSpace.rankOne_comp_rankOne, inner_standardVector]
  split_ifs <;> simp_all [compactMatrixUnit]

@[simp] theorem compactMatrixUnit_norm (i j : ℕ) : ‖compactMatrixUnit i j‖ = 1 := by
  change ‖InnerProductSpace.rankOne ℂ (standardVector i) (standardVector j)‖ = 1
  rw [InnerProductSpace.norm_rankOne, norm_standardVector, norm_standardVector, one_mul]

def compactProjection (s : Finset ℕ) : StandardCompacts := ∑ i ∈ s, compactMatrixUnit i i

lemma compactProjection_star (s : Finset ℕ) : star (compactProjection s) = compactProjection s := by
  simp [compactProjection]
lemma compactProjection_mul (s : Finset ℕ) : compactProjection s * compactProjection s = compactProjection s := by
  classical
  simp [compactProjection, Finset.sum_mul, Finset.mul_sum]

theorem compactProjection_compress (s : Finset ℕ) (i j : ℕ) (hi : i ∈ s) (hj : j ∈ s) :
    compactProjection s * compactMatrixUnit i j * compactProjection s = compactMatrixUnit i j := by
  classical
  simp [compactProjection, Finset.sum_mul, Finset.mul_sum, hi, hj]
end CurrentMain.Compact
end

section

noncomputable section
open scoped TensorProduct InnerProductSpace CStarAlgebra
open UniformSpace.Completion

namespace CurrentMain.Spatial
open CurrentMain.Compact

variable {A H : Type*} [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
abbrev StabilizationHilbert (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  SpatialHilbert H StandardHilbert
abbrev StabilizationOperators (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  StabilizationHilbert H →L[ℂ] StabilizationHilbert H

def spatialEntry (i j : ℕ) (a : A) : StabilizationOperators H :=
  spatialTensorOp (π a) (compactMatrixUnit i j : StandardHilbert →L[ℂ] StandardHilbert)

@[simp] lemma spatialEntry_zero (i j : ℕ) : spatialEntry π i j 0 = 0 := by simp [spatialEntry]
@[simp] lemma spatialEntry_add (i j : ℕ) (a b : A) :
    spatialEntry π i j (a+b) = spatialEntry π i j a + spatialEntry π i j b := by
  simp [spatialEntry, spatialTensorOp_add_left]
@[simp] lemma spatialEntry_smul (i j : ℕ) (c : ℂ) (a : A) :
    spatialEntry π i j (c • a) = c • spatialEntry π i j a := by
  simp [spatialEntry, spatialTensorOp_smul_left]
@[simp] lemma spatialEntry_star (i j : ℕ) (a : A) :
    star (spatialEntry π i j a) = spatialEntry π j i (star a) := by
  rw [spatialEntry, ← spatialTensorOp_star, ← map_star]
  congr 1
  exact congrArg Subtype.val (compactMatrixUnit_star i j)
@[simp] lemma spatialEntry_mul (i j k l : ℕ) (a b : A) :
    spatialEntry π i j a * spatialEntry π k l b =
      if j=k then spatialEntry π i l (a*b) else 0 := by
  rw [spatialEntry, spatialEntry, ← spatialTensorOp_mul, ← map_mul]
  have h := congrArg Subtype.val (compactMatrixUnit_mul i j k l)
  change (compactMatrixUnit i j : StandardHilbert →L[ℂ] StandardHilbert) *
    (compactMatrixUnit k l : StandardHilbert →L[ℂ] StandardHilbert) = _ at h
  rw [h]
  split_ifs <;> simp_all [spatialEntry]

end CurrentMain.Spatial
end

noncomputable section
open scoped TensorProduct InnerProductSpace CStarAlgebra Topology

namespace CurrentMain.Spatial
open CurrentMain.Compact

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))

def spatialCorner : A →⋆ₙₐ[ℂ] StabilizationOperators H where
  toFun := spatialEntry π 0 0
  map_zero' := spatialEntry_zero π 0 0
  map_add' := spatialEntry_add π 0 0
  map_smul' c a := spatialEntry_smul π 0 0 c a
  map_mul' a b := by simp
  map_star' a := by simp

lemma spatialCorner_coefficient (a : A) (x y : H) :
    inner ℂ (spatialCorner π a (x ⊗ₜ[ℂ] standardVector 0 : H ⊗[ℂ] StandardHilbert))
      (y ⊗ₜ[ℂ] standardVector 0 : H ⊗[ℂ] StandardHilbert) = inner ℂ (π a x) y := by
  simp [spatialCorner,spatialEntry,compactMatrixUnit,InnerProductSpace.rankOne_apply,
    norm_standardVector]

lemma spatialCorner_injective (hπ : Function.Injective π) : Function.Injective (spatialCorner π) := by
  intro a b hab
  apply hπ
  ext x
  apply ext_inner_right ℂ
  intro y
  rw [←spatialCorner_coefficient π a x y,←spatialCorner_coefficient π b x y,hab]

local instance : NormedStarGroup (StabilizationOperators H) where
  norm_star_le T := by
    change ‖T.adjoint‖ ≤ ‖T‖
    rw [LinearIsometryEquiv.norm_map]

local instance : ContinuousStar (StabilizationOperators H) where
  continuous_star := ContinuousLinearMap.adjoint.continuous

local instance : ContinuousMul (StabilizationOperators H) :=
  @NonUnitalSeminormedRing.toContinuousMul (StabilizationOperators H) _

local instance : IsTopologicalRing (StabilizationOperators H) :=
  @NonUnitalSeminormedRing.toIsTopologicalRing (StabilizationOperators H) _

local instance : IsSemitopologicalSemiring (StabilizationOperators H) :=
  @IsSemitopologicalRing.toIsSemitopologicalSemiring (StabilizationOperators H) _ _
    (@IsTopologicalRing.toIsSemitopologicalRing (StabilizationOperators H) _ _ inferInstance)

def spatialCompactAlgebra : NonUnitalStarSubalgebra ℂ (StabilizationOperators H) :=
  (NonUnitalStarAlgebra.adjoin ℂ {R | ∃ (a : A) (T : StandardCompacts),
    R = spatialTensorOp (π a) (T : StandardHilbert →L[ℂ] StandardHilbert)}).topologicalClosure

def elementarySet : Set (StabilizationOperators H) :=
  {R | ∃ (a : A) (T : StandardCompacts),
    R = spatialTensorOp (π a) (T : StandardHilbert →L[ℂ] StandardHilbert)}

private lemma elementary_mul {x y : StabilizationOperators H}
    (hx : x ∈ elementarySet π) (hy : y ∈ elementarySet π) : x*y ∈ elementarySet π := by
  obtain ⟨a,T,rfl⟩ := hx
  obtain ⟨b,S,rfl⟩ := hy
  refine ⟨a*b,T*S,?_⟩
  rw [map_mul]
  exact (spatialTensorOp_mul _ _ _ _).symm

private lemma elementary_star {x : StabilizationOperators H}
    (hx : x ∈ elementarySet π) : star x ∈ elementarySet π := by
  obtain ⟨a,T,rfl⟩ := hx
  refine ⟨star a,star T,?_⟩
  rw [map_star]
  exact (spatialTensorOp_star _ _).symm

private def elementarySpan : NonUnitalStarSubalgebra ℂ (StabilizationOperators H) where
  carrier := Submodule.span ℂ (elementarySet π)
  zero_mem' := Submodule.zero_mem _
  add_mem' := Submodule.add_mem _
  smul_mem' c _ hx := Submodule.smul_mem _ c hx
  mul_mem' := by
    intro x y hx hy
    induction hx using Submodule.span_induction with
    | mem x hx =>
      induction hy using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span (elementary_mul π hx hy)
      | zero => simp
      | add y z _ _ hy hz => simpa [mul_add] using Submodule.add_mem _ hy hz
      | smul c y _ hy => simpa [mul_smul_comm] using Submodule.smul_mem _ c hy
    | zero => simp
    | add x z _ _ hx hz => simpa [add_mul] using Submodule.add_mem _ hx hz
    | smul c x _ hx => simpa [smul_mul_assoc] using Submodule.smul_mem _ c hx
  star_mem' := by
    intro x hx
    change star x ∈ Submodule.span ℂ (elementarySet π)
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (elementary_star π hx)
    | zero => rw [star_zero (StabilizationOperators H)]; exact Submodule.zero_mem _
    | add x z _ _ hx hz => rw [star_add x z]; exact Submodule.add_mem _ hx hz
    | smul c x _ hx => rw [star_smul]; exact Submodule.smul_mem _ (star c) hx

lemma rankOne_compression (T : StandardHilbert →L[ℂ] StandardHilbert) :
    (compactMatrixUnit 0 0 : StandardHilbert →L[ℂ] StandardHilbert) * T *
      (compactMatrixUnit 0 0 : StandardHilbert →L[ℂ] StandardHilbert) =
    inner ℂ (standardVector 0) ((T : StandardHilbert →L[ℂ] StandardHilbert) (standardVector 0)) •
      (compactMatrixUnit 0 0 : StandardHilbert →L[ℂ] StandardHilbert) := by
  ext x
  simp [compactMatrixUnit,InnerProductSpace.rankOne_apply,smul_smul,
    mul_comm]

lemma spatialCorner_compress_elementary (a : A) (T : StandardCompacts) :
    spatialCorner π 1 * spatialTensorOp (π a) (T : StandardHilbert →L[ℂ] StandardHilbert) *
      spatialCorner π 1 =
    spatialCorner π (inner ℂ (standardVector 0) ((T : StandardHilbert →L[ℂ] StandardHilbert) (standardVector 0)) • a) := by
  change spatialTensorOp (π 1) _ * spatialTensorOp (π a) _ * spatialTensorOp (π 1) _ = _
  rw [←spatialTensorOp_mul,←spatialTensorOp_mul,←map_mul,←map_mul,one_mul,mul_one,
    rankOne_compression,spatialTensorOp_smul_right]
  exact (spatialEntry_smul π 0 0 _ a).symm

private lemma elementarySpan_compress {x : StabilizationOperators H}
    (hx : x ∈ elementarySpan π) :
    spatialCorner π 1 * x * spatialCorner π 1 ∈ Set.range (spatialCorner π) := by
  change x ∈ Submodule.span ℂ (elementarySet π) at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a,T,rfl⟩ := hx
    exact ⟨_,(spatialCorner_compress_elementary π a T).symm⟩
  | zero => exact ⟨0,by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a,ha⟩ := hx
    obtain ⟨b,hb⟩ := hy
    exact ⟨a+b,by simp [ha,hb,mul_add,add_mul]⟩
  | smul c x _ hx =>
    obtain ⟨a,ha⟩ := hx
    exact ⟨c • a,by simp [ha]⟩

theorem spatialCorner_full (hπ : Function.Injective π) {x : StabilizationOperators H}
    (hx : x ∈ spatialCompactAlgebra π)
    (hqx : spatialCorner π 1 * x * spatialCorner π 1 = x) :
    ∃ a : A, spatialCorner π a = x := by
  have hc : IsClosed (Set.range (spatialCorner π)) :=
    (NonUnitalStarAlgHom.isometry _ (spatialCorner_injective π hπ)).isClosedEmbedding.isClosed_range
  have hcomp : IsClosed {x : StabilizationOperators H |
      spatialCorner π 1 * x * spatialCorner π 1 ∈ Set.range (spatialCorner π)} := by
    exact hc.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  have hle : NonUnitalStarAlgebra.adjoin ℂ (elementarySet π) ≤ elementarySpan π := by
    apply NonUnitalStarAlgebra.adjoin_le
    intro x hx
    exact Submodule.subset_span hx
  have hm : x ∈ {x : StabilizationOperators H |
      spatialCorner π 1 * x * spatialCorner π 1 ∈ Set.range (spatialCorner π)} :=
    hcomp.closure_subset (closure_mono (fun y hy => elementarySpan_compress π (hle hy)) hx)
  change ∃ a : A, spatialCorner π a = spatialCorner π 1 * x * spatialCorner π 1 at hm
  rw [hqx] at hm
  exact hm

instance spatialCompactAlgebra_closed : IsClosed (spatialCompactAlgebra π : Set (StabilizationOperators H)) :=
  NonUnitalStarSubalgebra.isClosed_topologicalClosure _

def SpatialStabilization : Type _ := ↥(spatialCompactAlgebra π)

instance : NonUnitalCStarAlgebra (SpatialStabilization π) :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra (spatialCompactAlgebra π)

def spatialCornerInto : A →⋆ₙₐ[ℂ] SpatialStabilization π where
  toFun a := ⟨spatialCorner π a,
    NonUnitalStarSubalgebra.le_topologicalClosure _
      (NonUnitalStarAlgebra.subset_adjoin ℂ _ ⟨a,compactMatrixUnit 0 0,rfl⟩)⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ a b)
  map_mul' a b := Subtype.ext (map_mul _ a b)
  map_smul' c a := Subtype.ext (map_smul _ c a)
  map_star' a := Subtype.ext (map_star _ a)

lemma spatialCornerInto_injective (hπ : Function.Injective π) :
    Function.Injective (spatialCornerInto π) :=
  fun _ _ he => spatialCorner_injective π hπ (congrArg Subtype.val he)

theorem spatialCornerInto_full (hπ : Function.Injective π) (x : SpatialStabilization π)
    (hx : spatialCornerInto π 1*x*spatialCornerInto π 1 = x) :
    ∃ a : A, spatialCornerInto π a = x := by
  obtain ⟨a,ha⟩ := spatialCorner_full π hπ x.2 (congrArg Subtype.val hx)
  exact ⟨a,Subtype.ext ha⟩

end CurrentMain.Spatial

end
end
end
end
end
end

end OAI
