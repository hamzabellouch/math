import Mathlib
import OAI.Analysis.Crouzeix.BoundaryForms

namespace OAI

/-! Fourier. -/

noncomputable section

open MeasureTheory

open scoped InnerProductSpace lp Classical Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert.Boundary

abbrev CircleSpace := AddCircle (1 : ℝ)

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

abbrev circleMeasure : Measure CircleSpace := AddCircle.haarAddCircle

abbrev BoundaryL2 (k : ℕ) := Lp (HS k) 2 circleMeasure

def lpEntry {k : ℕ} (ij : Fin k × Fin k) : BoundaryL2 k →L[ℂ] Lp ℂ 2 circleMeasure :=
  (PiLp.proj 2 (fun _ : Fin k × Fin k => ℂ) ij).compLpL 2 circleMeasure

lemma lpEntry_apply_ae {k : ℕ} (ij : Fin k × Fin k) (u : BoundaryL2 k) :
    lpEntry ij u =ᵐ[circleMeasure] fun t => u t ij :=
  ContinuousLinearMap.coeFn_compLpL _ _

def matrixFourier {k : ℕ} (a : ℤ × (Fin k × Fin k)) : BoundaryL2 k :=
  ContinuousMap.toLp 2 circleMeasure ℂ
    ⟨fun t => fourier a.1 t • EuclideanSpace.single a.2 (1 : ℂ),
      by fun_prop⟩

lemma matrixFourier_apply_ae {k : ℕ} (a : ℤ × (Fin k × Fin k)) :
    matrixFourier a =ᵐ[circleMeasure]
      fun t => fourier a.1 t • EuclideanSpace.single a.2 (1 : ℂ) :=
  ContinuousMap.coeFn_toLp _ _

lemma inner_matrixFourier {k : ℕ} (a : ℤ × (Fin k × Fin k)) (u : BoundaryL2 k) :
    ⟪matrixFourier a, u⟫_ℂ = ⟪fourierLp 2 a.1, lpEntry a.2 u⟫_ℂ := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [matrixFourier_apply_ae a, lpEntry_apply_ae a.2 u,
    coeFn_fourierLp 2 a.1] with t hm he hf
  rw [hm, he, hf, inner_smul_left, EuclideanSpace.inner_single_left]
  simp [RCLike.inner_apply, mul_comm]

lemma lpEntry_matrixFourier {k : ℕ} (a : ℤ × (Fin k × Fin k)) (ij : Fin k × Fin k) :
    lpEntry ij (matrixFourier a) = if ij = a.2 then fourierLp 2 a.1 else 0 := by
  apply Lp.ext
  filter_upwards [lpEntry_apply_ae ij (matrixFourier a), matrixFourier_apply_ae a,
    coeFn_fourierLp 2 a.1, (Lp.coeFn_zero ℂ 2 circleMeasure)] with t he hm hf hz
  rw [he, hm]
  by_cases hij : ij = a.2
  · subst ij
    simp only [PiLp.smul_apply, PiLp.single_apply, ite_true, smul_eq_mul, mul_one]
    exact hf.symm
  · simp only [ite_eq_right hij, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul, mul_zero]
    exact hz.symm

lemma orthonormal_matrixFourier (k : ℕ) :
    Orthonormal ℂ (@matrixFourier k) := by
  rw [orthonormal_iff_ite]
  intro a b
  rw [inner_matrixFourier, lpEntry_matrixFourier]
  by_cases hab : a.2 = b.2
  · rw [ite_eq_left hab, orthonormal_iff_ite.mp orthonormal_fourier]
    simp [Prod.ext_iff, hab]
  · rw [ite_eq_right hab, inner_zero_right, ite_eq_right]
    exact fun h => hab (congrArg Prod.snd h)

lemma lpEntry_ext {k : ℕ} {u v : BoundaryL2 k}
    (h : ∀ ij, lpEntry ij u = lpEntry ij v) : u = v := by
  apply Lp.ext
  have he : ∀ᵐ t ∂circleMeasure, ∀ ij, u t ij = v t ij := by
    rw [ae_all_iff]
    intro ij
    filter_upwards [lpEntry_apply_ae ij u, lpEntry_apply_ae ij v] with t hu hv
    rw [← hu, ← hv, h ij]
  exact he.mono fun t ht => by ext ij; exact ht ij

lemma matrixFourier_orthogonal_eq_bot (k : ℕ) :
    (Submodule.span ℂ (Set.range (@matrixFourier k)))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro u hu
  change u = 0
  apply lpEntry_ext
  intro ij
  rw [map_zero]
  apply fourierBasis.repr.injective
  ext n
  rw [map_zero]
  change _ = 0
  rw [fourierBasis.repr_apply_apply, coe_fourierBasis]
  rw [← inner_matrixFourier (n,ij)]
  exact (Submodule.mem_orthogonal _ _).mp hu _ (Submodule.subset_span ⟨(n,ij), rfl⟩)

def matrixFourierBasis (k : ℕ) :
    HilbertBasis (ℤ × (Fin k × Fin k)) ℂ (BoundaryL2 k) :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_matrixFourier k) (matrixFourier_orthogonal_eq_bot k)

@[simp] lemma matrixFourierBasis_apply {k : ℕ} (a : ℤ × (Fin k × Fin k)) :
    matrixFourierBasis k a = matrixFourier a := by
  rw [matrixFourierBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]

lemma matrixFourierBasis_repr {k : ℕ} (u : BoundaryL2 k) (a : ℤ × (Fin k × Fin k)) :
    (matrixFourierBasis k).repr u a = fourierCoeff (lpEntry a.2 u) a.1 := by
  rw [HilbertBasis.repr_apply_apply, matrixFourierBasis_apply, inner_matrixFourier,
    ← coe_fourierBasis, ← HilbertBasis.repr_apply_apply, fourierBasis_repr]

def l2Mask {ι : Type*} (S : ι → Prop) : ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ) := by
  classical
  let M : ℓ²(ι, ℂ) →ₗ[ℂ] ℓ²(ι, ℂ) := {
    toFun u := ⟨fun i => if S i then u i else 0,
      (lp.memℓp u).mono' fun i => by split_ifs <;> simp⟩
    map_add' u v := by
      ext i
      change (if S i then u i + v i else 0) =
        (if S i then u i else 0) + (if S i then v i else 0)
      by_cases hi : S i <;> simp [hi]
    map_smul' c u := by ext i; by_cases hi : S i <;> simp [hi] }
  apply M.mkContinuous 1
  intro u
  rw [one_mul]
  apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
  intro i
  change ‖if S i then u i else 0‖ ≤ ‖u i‖
  split_ifs <;> simp

@[simp] lemma l2Mask_apply {ι : Type*} (S : ι → Prop) (u : ℓ²(ι, ℂ)) (i : ι) :
    l2Mask S u i = if S i then u i else 0 := by classical exact rfl

lemma l2Mask_self_adjoint {ι : Type*} (S : ι → Prop) :
    ContinuousLinearMap.adjoint (l2Mask S) = l2Mask S := by
  classical
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro u v
  simp only [lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  by_cases hi : S i <;> simp [hi]

def frequencyPart (i : Fin 3) (n : ℤ) : Prop :=
  if i = 0 then n = 0 else if i = 1 then 0 < n else n < 0

@[simp] lemma frequencyPart_zero (n : ℤ) : frequencyPart 0 n ↔ n = 0 := by
  simp [frequencyPart]

@[simp] lemma frequencyPart_pos (n : ℤ) : frequencyPart 1 n ↔ 0 < n := by
  simp [frequencyPart]

@[simp] lemma frequencyPart_neg (n : ℤ) : frequencyPart 2 n ↔ n < 0 := by
  simp [frequencyPart]

def fourierProjC (k : ℕ) (i : Fin 3) : BoundaryL2 k →L[ℂ] BoundaryL2 k :=
  ((matrixFourierBasis k).repr.symm.toContinuousLinearEquiv :
      ℓ²(ℤ × (Fin k × Fin k), ℂ) →L[ℂ] BoundaryL2 k).comp
    ((l2Mask (fun a => frequencyPart i a.1)).comp
      (matrixFourierBasis k).repr.toContinuousLinearEquiv.toContinuousLinearMap)

lemma repr_fourierProjC {k : ℕ} (i : Fin 3) (u : BoundaryL2 k)
    (a : ℤ × (Fin k × Fin k)) :
    (matrixFourierBasis k).repr (fourierProjC k i u) a =
      if frequencyPart i a.1 then (matrixFourierBasis k).repr u a else 0 := by
  classical
  simp [fourierProjC]

lemma fourierProjC_self_adjoint (k : ℕ) (i : Fin 3) :
    ContinuousLinearMap.adjoint (fourierProjC k i) = fourierProjC k i := by
  classical
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro u v
  rw [← (matrixFourierBasis k).repr.inner_map_map, lp.inner_eq_tsum]
  rw [← (matrixFourierBasis k).repr.inner_map_map u, lp.inner_eq_tsum]
  apply tsum_congr
  intro a
  rw [repr_fourierProjC, repr_fourierProjC]
  by_cases ha : frequencyPart i a.1 <;> simp [ha]

lemma fourierProjC_comp (k : ℕ) (i j : Fin 3) :
    (fourierProjC k i).comp (fourierProjC k j) =
      if i = j then fourierProjC k i else 0 := by
  classical
  apply ContinuousLinearMap.ext
  intro u
  apply (matrixFourierBasis k).repr.injective
  ext a
  dsimp only [ContinuousLinearMap.comp_apply]
  rw [repr_fourierProjC, repr_fourierProjC]
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl, repr_fourierProjC]
    split_ifs <;> rfl
  · rw [ite_eq_right hij]
    simp only [zero_apply, map_zero, lp.coeFn_zero, Pi.zero_apply]
    have hd : ¬ (frequencyPart i a.1 ∧ frequencyPart j a.1) := by
      fin_cases i <;> fin_cases j <;> simp_all <;> omega
    split_ifs <;> simp_all

lemma fourierProjC_total (k : ℕ) :
    fourierProjC k 0 + fourierProjC k 1 + fourierProjC k 2 =
      ContinuousLinearMap.id ℂ (BoundaryL2 k) := by
  classical
  apply ContinuousLinearMap.ext
  intro u
  apply (matrixFourierBasis k).repr.injective
  ext a
  simp only [add_apply, map_add, lp.coeFn_add, Pi.add_apply,
    ContinuousLinearMap.id_apply, repr_fourierProjC]
  rcases lt_trichotomy a.1 0 with hn | hn | hn
  · simp [hn, hn.ne, not_lt.mpr hn.le]
  · simp [hn]
  · simp [hn, hn.ne', not_lt.mpr hn.le]

lemma boundary_real_inner {k : ℕ} (u v : BoundaryL2 k) :
    ⟪u,v⟫_ℝ = (⟪u,v⟫_ℂ).re := by
  simp only [L2.inner_def]
  calc
    _ = ∫ t, (⟪u t,v t⟫_ℂ).re ∂circleMeasure := by
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [PiLp.inner_apply, Complex.re_sum]
      rfl
    _ = _ := integral_re (𝕜 := ℂ) (L2.integrable_inner (𝕜 := ℂ) u v)

def fourierSplitting (k : ℕ) : ThreeWaySplitting (BoundaryL2 k) where
  proj i := (fourierProjC k i).restrictScalars ℝ
  self_adjoint i := by
    symm
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro u v
    change ⟪fourierProjC k i u, v⟫_ℝ = ⟪u, fourierProjC k i v⟫_ℝ
    rw [boundary_real_inner, boundary_real_inner]
    have h := ContinuousLinearMap.adjoint_inner_left (fourierProjC k i) v u
    rw [fourierProjC_self_adjoint] at h
    exact congrArg Complex.re h
  comp i j := by
    apply ContinuousLinearMap.ext
    intro u
    have h := congrArg (fun L : BoundaryL2 k →L[ℂ] BoundaryL2 k => L u)
      (fourierProjC_comp k i j)
    split_ifs with hij <;> simpa [hij] using h
  total := by
    apply ContinuousLinearMap.ext
    intro u
    exact congrArg (fun L : BoundaryL2 k →L[ℂ] BoundaryL2 k => L u) (fourierProjC_total k)

lemma repr_lpStar {k : ℕ} (u : BoundaryL2 k) (n : ℤ) (i j : Fin k) :
    (matrixFourierBasis k).repr (lpStar u) (n,(i,j)) =
      star ((matrixFourierBasis k).repr u (-n,(j,i))) := by
  rw [matrixFourierBasis_repr, matrixFourierBasis_repr]
  simp only [fourierCoeff, neg_neg, smul_eq_mul, Complex.star_def]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [lpEntry_apply_ae (i,j) (lpStar u), lpStar_apply_ae u,
    lpEntry_apply_ae (j,i) u] with t he hs he'
  simp only [he, hs, he', toHS, ofHS,
    Matrix.conjTranspose_apply, Complex.star_def, map_mul, fourier_neg]

lemma lpStar_fourierProj_zero {k : ℕ} (u : BoundaryL2 k) :
    lpStar (fourierProjC k 0 u) = fourierProjC k 0 (lpStar u) := by
  apply (matrixFourierBasis k).repr.injective
  ext ⟨n,i,j⟩
  rw [repr_lpStar, repr_fourierProjC, repr_fourierProjC, repr_lpStar]
  simp only [frequencyPart_zero, neg_eq_zero, apply_ite (star : ℂ → ℂ), star_zero]

lemma lpStar_fourierProj_pos {k : ℕ} (u : BoundaryL2 k) :
    lpStar (fourierProjC k 1 u) = fourierProjC k 2 (lpStar u) := by
  apply (matrixFourierBasis k).repr.injective
  ext ⟨n,i,j⟩
  rw [repr_lpStar, repr_fourierProjC, repr_fourierProjC, repr_lpStar]
  simp only [frequencyPart_pos, frequencyPart_neg, neg_pos,
    apply_ite (star : ℂ → ℂ), star_zero]

def fourierInvolution (k : ℕ) : (fourierSplitting k).CompatibleInvolution where
  op := lpStar
  involutive := lpStar_lpStar
  proj_zero := lpStar_fourierProj_zero
  proj_pos := lpStar_fourierProj_pos

def matrixMean {k : ℕ} (u : BoundaryL2 k) : Matrix (Fin k) (Fin k) ℂ :=
  fun i j => ∫ t, u t (i,j) ∂circleMeasure

lemma repr_zero_eq_mean {k : ℕ} (u : BoundaryL2 k) (i j : Fin k) :
    (matrixFourierBasis k).repr u (0,(i,j)) = matrixMean u i j := by
  rw [matrixFourierBasis_repr]
  simp only [fourierCoeff, neg_zero, fourier_zero, one_smul]
  exact integral_congr_ae (lpEntry_apply_ae (i,j) u)

lemma mean_eq_zero_iff {k : ℕ} (u : BoundaryL2 k) :
    matrixMean u = 0 ↔ (fourierSplitting k).proj 0 u = 0 := by
  constructor
  · intro h
    apply (matrixFourierBasis k).repr.injective
    ext ⟨n,i,j⟩
    change (matrixFourierBasis k).repr (fourierProjC k 0 u) (n,(i,j)) = _
    rw [repr_fourierProjC, map_zero]
    change (if frequencyPart 0 n then _ else 0) = 0
    by_cases hn : n = 0
    · subst n
      simp only [frequencyPart_zero, ite_true, repr_zero_eq_mean, h, Matrix.zero_apply]
    · simp only [frequencyPart_zero, ite_eq_right hn]
  · intro h
    ext i j
    have hz := congrArg (fun v : BoundaryL2 k => (matrixFourierBasis k).repr v (0,(i,j))) h
    change (matrixFourierBasis k).repr (fourierProjC k 0 u) (0,(i,j)) = _ at hz
    simpa only [repr_fourierProjC, frequencyPart_zero, ite_true, repr_zero_eq_mean,
      map_zero, lp.coeFn_zero, Pi.zero_apply, Matrix.zero_apply] using hz

lemma norm_fourier_proj_le (k : ℕ) (i : Fin 3) :
    ‖(fourierSplitting k).proj i‖ ≤ 1 := (fourierSplitting k).norm_proj_le i

def upperTransfer {k : ℕ} (M : BoundaryL2 k →L[ℝ] BoundaryL2 k) :
    BoundaryL2 k →L[ℝ] BoundaryL2 k :=
  ((fourierSplitting k).proj 1).comp (ContinuousLinearMap.adjoint M)

lemma upperTransfer_range {k : ℕ} (M : BoundaryL2 k →L[ℝ] BoundaryL2 k) :
    ((fourierSplitting k).proj 1).comp (upperTransfer M) = upperTransfer M := by
  apply ContinuousLinearMap.ext
  intro u
  change (fourierSplitting k).proj 1 ((fourierSplitting k).proj 1 _) = _
  simp only [ThreeWaySplitting.proj_proj, ite_true]
  rfl

lemma norm_upperTransfer_le {k : ℕ} (M : BoundaryL2 k →L[ℝ] BoundaryL2 k)
    (hM : ‖M‖ ≤ 1) : ‖upperTransfer M‖ ≤ 1 := by
  calc
    _ ≤ ‖(fourierSplitting k).proj 1‖ * ‖ContinuousLinearMap.adjoint M‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul (norm_fourier_proj_le k 1)
      (by simpa only [ContinuousLinearMap.adjoint.norm_map] using hM)
      (norm_nonneg _) zero_le_one
    _ = 1 := one_mul _

def boundaryCauchyAdjoint {k : ℕ} (M : BoundaryL2 k →L[ℝ] BoundaryL2 k) :
    BoundaryL2 k →L[ℝ] BoundaryL2 k :=
  (fourierSplitting k).cauchyAdjoint (upperTransfer M)

def boundaryCauchy {k : ℕ} (M : BoundaryL2 k →L[ℝ] BoundaryL2 k) :
    BoundaryL2 k →L[ℝ] BoundaryL2 k :=
  (fourierSplitting k).proj 0 + (fourierSplitting k).proj 1 +
    ((fourierSplitting k).proj 2).comp (M.comp ((fourierSplitting k).proj 1))

lemma adjoint_boundaryCauchy {k : ℕ} (M : BoundaryL2 k →L[ℝ] BoundaryL2 k) :
    ContinuousLinearMap.adjoint (boundaryCauchy M) = boundaryCauchyAdjoint M := by
  simp only [boundaryCauchy, boundaryCauchyAdjoint, ThreeWaySplitting.cauchyAdjoint,
    upperTransfer, map_add, ContinuousLinearMap.adjoint_comp,
    ThreeWaySplitting.self_adjoint, ContinuousLinearMap.comp_assoc]

lemma adjoint_boundaryCauchyAdjoint {k : ℕ} (M : BoundaryL2 k →L[ℝ] BoundaryL2 k) :
    ContinuousLinearMap.adjoint (boundaryCauchyAdjoint M) = boundaryCauchy M := by
  rw [← adjoint_boundaryCauchy, ContinuousLinearMap.adjoint_adjoint]

lemma boundaryCauchyAdjoint_idempotent {k : ℕ} (M : BoundaryL2 k →L[ℝ] BoundaryL2 k) :
    (boundaryCauchyAdjoint M).comp (boundaryCauchyAdjoint M) = boundaryCauchyAdjoint M := by
  apply ContinuousLinearMap.ext
  intro u
  change (fourierSplitting k).cauchyAdjoint (upperTransfer M)
    ((fourierSplitting k).cauchyAdjoint (upperTransfer M) u) = _
  rw [ThreeWaySplitting.cauchyAdjoint_apply,
    ThreeWaySplitting.proj0_cauchyAdjoint (upperTransfer_range M),
    ThreeWaySplitting.proj1_cauchyAdjoint (upperTransfer_range M),
    ThreeWaySplitting.proj2_cauchyAdjoint (upperTransfer_range M), map_zero, add_zero]
  simp only [boundaryCauchyAdjoint, ThreeWaySplitting.cauchyAdjoint_apply, add_assoc]

lemma boundaryCauchy_idempotent {k : ℕ} (M : BoundaryL2 k →L[ℝ] BoundaryL2 k) :
    (boundaryCauchy M).comp (boundaryCauchy M) = boundaryCauchy M := by
  apply ContinuousLinearMap.adjoint.injective
  rw [ContinuousLinearMap.adjoint_comp, adjoint_boundaryCauchy,
    boundaryCauchyAdjoint_idempotent]

lemma boundaryCauchy_weighted_norm_sq {k : ℕ} (M : BoundaryL2 k →L[ℝ] BoundaryL2 k)
    (hM : ‖M‖ ≤ 1) (u : BoundaryL2 k) :
    ‖boundaryCauchyAdjoint M u‖ ^ 2 +
        ‖(fourierSplitting k).proj 0 (boundaryCauchyAdjoint M u)‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 :=
  ThreeWaySplitting.weighted_norm_sq (upperTransfer_range M) (norm_upperTransfer_le M hM) u

lemma boundaryCauchy_mean {k : ℕ} (M : BoundaryL2 k →L[ℝ] BoundaryL2 k) (u : BoundaryL2 k) :
    matrixMean (boundaryCauchy M u) = matrixMean u := by
  have hp : (fourierSplitting k).proj 0 (boundaryCauchy M u) =
      (fourierSplitting k).proj 0 u := by
    simp only [boundaryCauchy, add_apply, ContinuousLinearMap.comp_apply,
      map_add, ThreeWaySplitting.proj_proj, ite_true]
    simp
  ext i j
  have he := congrArg (fun v : BoundaryL2 k => (matrixFourierBasis k).repr v (0,(i,j))) hp
  change (matrixFourierBasis k).repr (fourierProjC k 0 _) (0,(i,j)) =
    (matrixFourierBasis k).repr (fourierProjC k 0 _) (0,(i,j)) at he
  simpa only [repr_fourierProjC, frequencyPart_zero, ite_true, repr_zero_eq_mean] using he

lemma boundaryCauchyAdjoint_mean {k : ℕ} (M : BoundaryL2 k →L[ℝ] BoundaryL2 k)
    (u : BoundaryL2 k) : matrixMean (boundaryCauchyAdjoint M u) = matrixMean u := by
  have hp := ThreeWaySplitting.proj0_cauchyAdjoint (upperTransfer_range M) u
  change matrixMean ((fourierSplitting k).cauchyAdjoint (upperTransfer M) u) = matrixMean u
  ext i j
  have he := congrArg (fun v : BoundaryL2 k => (matrixFourierBasis k).repr v (0,(i,j))) hp
  change (matrixFourierBasis k).repr (fourierProjC k 0 _) (0,(i,j)) =
    (matrixFourierBasis k).repr (fourierProjC k 0 _) (0,(i,j)) at he
  simpa only [repr_fourierProjC, frequencyPart_zero, ite_true, repr_zero_eq_mean] using he

theorem fourier_ordered_comparison {k : ℕ}
    (M : BoundaryL2 k →L[ℝ] BoundaryL2 k) (hM : ‖M‖ ≤ 1)
    (F : CircleSpace → Matrix (Fin k) (Fin k) ℂ)
    (hm : AEStronglyMeasurable F circleMeasure)
    (hn : ∀ᵐ t ∂circleMeasure, ‖F t‖ ≤ 1)
    (hleft : (ContinuousLinearMap.adjoint (boundaryCauchyAdjoint M)).comp
        ((lpLeft F hm hn).comp (ContinuousLinearMap.adjoint (boundaryCauchyAdjoint M))) =
      (lpLeft F hm hn).comp (ContinuousLinearMap.adjoint (boundaryCauchyAdjoint M)))
    (hright : (ContinuousLinearMap.adjoint (boundaryCauchyAdjoint M)).comp
        ((lpRight F hm hn).comp (ContinuousLinearMap.adjoint (boundaryCauchyAdjoint M))) =
      (lpRight F hm hn).comp (ContinuousLinearMap.adjoint (boundaryCauchyAdjoint M)))
    (p q r : BoundaryL2 k)
    (hpstar : ∀ᵐ t ∂circleMeasure, (ofHS (p t)).IsHermitian)
    (hqstar : ∀ᵐ t ∂circleMeasure, (ofHS (q t)).IsHermitian)
    (hp : ∀ᵐ t ∂circleMeasure, ofHS (p t) = (F t)ᴴ * ofHS (r t))
    (hq : ∀ᵐ t ∂circleMeasure, ofHS (q t) = ofHS (r t) * (F t)ᴴ)
    (hrmean : matrixMean r = 0) (hpmean : 0 < (matrixMean p).trace.re)
    (κ : ℝ) (hκ : 0 < κ)
    (hblock : let D := boundaryCauchyAdjoint M
      let pₑ := D p + lpStar (D (lpStar p))
      let qₑ := D q + lpStar (D (lpStar q))
      let rₑ := κ • D r + κ⁻¹ • lpStar (D (lpStar r))
      ∀ᵐ t ∂circleMeasure, (Matrix.fromBlocks (ofHS (pₑ t))
        (ofHS (rₑ t))ᴴ (ofHS (rₑ t)) (ofHS (qₑ t))).PosSemidef) : κ ≤ 2 := by
  apply lp_ordered_comparison (fourierSplitting k)
    lpStar_fourierProj_zero lpStar_fourierProj_pos (upperTransfer M)
    (upperTransfer_range M) (norm_upperTransfer_le M hM) F hm hn
    hleft hright p q r hpstar hqstar hp hq ((mean_eq_zero_iff r).mp hrmean) _ κ hκ hblock
  intro h
  have hz : matrixMean p = 0 := (mean_eq_zero_iff p).mpr h
  simp only [hz, Matrix.trace_zero, Complex.zero_re] at hpmean
  exact lt_irrefl 0 hpmean

end CrouzeixHilbert.Boundary

end

end OAI
