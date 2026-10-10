import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.VonNeumannAlgebra.Basic

namespace OAI

noncomputable section

namespace Invariant233.GeneralPolar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma norm_abs_apply (A : H →L[ℂ] H) (x : H) : ‖CFC.abs A x‖ = ‖A x‖ := by
  have hA : star (CFC.abs A) = CFC.abs A := (CFC.abs_nonneg A).star_eq
  have hi : inner ℂ (CFC.abs A x) (CFC.abs A x) = inner ℂ (A x) (A x) := by
    rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.adjoint_inner_left]
    change inner ℂ ((star (CFC.abs A) * CFC.abs A) x) x =
      inner ℂ ((star A * A) x) x
    rw [hA, CFC.abs_mul_abs]
  have hs : ‖CFC.abs A x‖ ^ 2 = ‖A x‖ ^ 2 := by
    simpa only [inner_self_eq_norm_sq] using congrArg (fun z : ℂ => RCLike.re z) hi
  nlinarith [norm_nonneg (CFC.abs A x), norm_nonneg (A x)]

def closedRange (B : H →L[ℂ] H) : Submodule ℂ H := B.range.topologicalClosure

instance (B : H →L[ℂ] H) : IsClosed (closedRange B : Set H) :=
  Submodule.isClosed_topologicalClosure _

def toClosedRange (B : H →L[ℂ] H) : H →L[ℂ] closedRange B :=
  B.codRestrict _ (fun x => B.range.le_topologicalClosure (B.mem_range_self x))

omit [CompleteSpace H] in
lemma toClosedRange_dense (B : H →L[ℂ] H) : DenseRange (toClosedRange B) := by
  have hd : DenseRange (Set.inclusion (B.range.le_topologicalClosure :
      (B.range : Set H) ⊆ (closedRange B : Set H))) :=
    (denseRange_inclusion_iff _).2 (by exact Set.Subset.rfl)
  have hs : Function.Surjective B.rangeRestrict := by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  exact hd.comp hs.denseRange (continuous_inclusion _)

def rangeIsometryMap (A B : H →L[ℂ] H) : closedRange B →L[ℂ] H :=
  A.toLinearMap.extendOfNorm (toClosedRange B).toLinearMap

lemma rangeIsometryMap_apply (A B : H →L[ℂ] H)
    (h : ∀ x, ‖A x‖ = ‖B x‖) (x : H) :
    rangeIsometryMap A B (toClosedRange B x) = A x := by
  apply LinearMap.extendOfNorm_eq (toClosedRange_dense B)
  refine ⟨1, fun y => ?_⟩
  change ‖A y‖ ≤ 1 * ‖B y‖
  simpa only [one_mul] using (h y).le

lemma rangeIsometryMap_norm (A B : H →L[ℂ] H)
    (h : ∀ x, ‖A x‖ = ‖B x‖) (x : closedRange B) :
    ‖rangeIsometryMap A B x‖ = ‖x‖ := by
  refine (toClosedRange_dense B).induction_on x
    (p := fun z => ‖rangeIsometryMap A B z‖ = ‖z‖) ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro y
    rw [rangeIsometryMap_apply A B h]
    exact h y

def rangeIsometry (A B : H →L[ℂ] H) (h : ∀ x, ‖A x‖ = ‖B x‖) :
    closedRange B →ₗᵢ[ℂ] H :=
  { (rangeIsometryMap A B).toLinearMap with norm_map' := rangeIsometryMap_norm A B h }

lemma rangeIsometryMap_mem (A B : H →L[ℂ] H)
    (h : ∀ x, ‖A x‖ = ‖B x‖) (x : closedRange B) :
    rangeIsometryMap A B x ∈ closedRange A := by
  refine (toClosedRange_dense B).induction_on x
    (p := fun z => rangeIsometryMap A B z ∈ closedRange A) ?_ ?_
  · exact (show IsClosed (closedRange A : Set H) from inferInstance).preimage
      (rangeIsometryMap A B).continuous
  · intro y
    rw [rangeIsometryMap_apply A B h]
    exact A.range.le_topologicalClosure (A.mem_range_self y)

lemma rangeIsometryMap_adjoint_comp (A B : H →L[ℂ] H)
    (h : ∀ x, ‖A x‖ = ‖B x‖) :
    (rangeIsometryMap A B).adjoint.comp (rangeIsometryMap A B) = 1 :=
  (rangeIsometryMap A B).norm_map_iff_adjoint_comp_self.mp
    (rangeIsometryMap_norm A B h)

lemma rangeIsometryMap_comp_adjoint (A B : H →L[ℂ] H)
    (h : ∀ x, ‖A x‖ = ‖B x‖) :
    (rangeIsometryMap A B).comp (rangeIsometryMap A B).adjoint =
      (closedRange A).starProjection := by
  ext x
  symm
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact rangeIsometryMap_mem A B h _
  · rw [closedRange, Submodule.orthogonal_closure, Submodule.mem_orthogonal]
    rintro y ⟨z, rfl⟩
    change inner ℂ (A z)
      (x - rangeIsometryMap A B ((rangeIsometryMap A B).adjoint x)) = 0
    rw [← rangeIsometryMap_apply A B h z]
    rw [inner_sub_right]
    have hi := (rangeIsometry A B h).inner_map_map (toClosedRange B z)
      ((rangeIsometryMap A B).adjoint x)
    change inner ℂ (rangeIsometryMap A B (toClosedRange B z))
      (rangeIsometryMap A B ((rangeIsometryMap A B).adjoint x)) = _ at hi
    rw [hi, ← ContinuousLinearMap.adjoint_inner_right]
    exact sub_self _

def partialIsometry (A B : H →L[ℂ] H) : H →L[ℂ] H :=
  (rangeIsometryMap A B).comp (closedRange B).orthogonalProjectionOnto

lemma partialIsometry_apply (A B : H →L[ℂ] H)
    (h : ∀ x, ‖A x‖ = ‖B x‖) (x : H) :
    partialIsometry A B (B x) = A x := by
  change rangeIsometryMap A B ((closedRange B).orthogonalProjectionOnto (B x)) = _
  have hp : (closedRange B).orthogonalProjectionOnto (B x) = toClosedRange B x :=
    (closedRange B).orthogonalProjectionOnto_mem_subspace_eq_self (toClosedRange B x)
  rw [hp, rangeIsometryMap_apply A B h]

lemma partialIsometry_initial (A B : H →L[ℂ] H)
    (h : ∀ x, ‖A x‖ = ‖B x‖) :
    star (partialIsometry A B) * partialIsometry A B =
      (closedRange B).starProjection := by
  change (partialIsometry A B).adjoint.comp (partialIsometry A B) = _
  simp only [partialIsometry, ContinuousLinearMap.adjoint_comp]
  rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc
    (rangeIsometryMap A B).adjoint, rangeIsometryMap_adjoint_comp A B h]
  simp only [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp,
    Submodule.adjoint_orthogonalProjectionOnto]
  rfl

lemma partialIsometry_final (A B : H →L[ℂ] H)
    (h : ∀ x, ‖A x‖ = ‖B x‖) :
    partialIsometry A B * star (partialIsometry A B) =
      (closedRange A).starProjection := by
  change (partialIsometry A B).comp (partialIsometry A B).adjoint = _
  simp only [partialIsometry, ContinuousLinearMap.adjoint_comp,
    Submodule.adjoint_orthogonalProjectionOnto]
  have hp : (closedRange B).orthogonalProjectionOnto.comp
      (closedRange B).subtypeL = 1 := by
    ext x
    exact congrArg (fun z : closedRange B => (z : H))
      ((closedRange B).orthogonalProjectionOnto_mem_subspace_eq_self x)
  rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc
    (closedRange B).orthogonalProjectionOnto, hp]
  simpa only [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp] using
    rangeIsometryMap_comp_adjoint A B h

lemma partialIsometry_right_support (A B : H →L[ℂ] H) :
    partialIsometry A B * (closedRange B).starProjection = partialIsometry A B := by
  ext x
  change rangeIsometryMap A B ((closedRange B).orthogonalProjectionOnto
    ((closedRange B).starProjection x)) =
      rangeIsometryMap A B ((closedRange B).orthogonalProjectionOnto x)
  congr 1
  exact (closedRange B).orthogonalProjectionOnto_mem_subspace_eq_self
    ((closedRange B).orthogonalProjectionOnto x)

omit [CompleteSpace H] in
lemma eq_on_closedRange (C D B : H →L[ℂ] H) (h : C * B = D * B)
    {x : H} (hx : x ∈ closedRange B) : C x = D x := by
  have hs : Set.range B ⊆ {x | C x = D x} := by
    rintro y ⟨z, rfl⟩
    exact congrArg (fun T : H →L[ℂ] H => T z) h
  exact closure_minimal hs (isClosed_eq C.continuous D.continuous) hx

lemma eq_of_right_support (C D B : H →L[ℂ] H) (h : C * B = D * B)
    (hC : C * (closedRange B).starProjection = C)
    (hD : D * (closedRange B).starProjection = D) : C = D := by
  ext x
  have he := eq_on_closedRange C D B h ((closedRange B).starProjection_apply_mem x)
  have hc := congrArg (fun T : H →L[ℂ] H => T x) hC
  have hd := congrArg (fun T : H →L[ℂ] H => T x) hD
  change C ((closedRange B).starProjection x) = C x at hc
  change D ((closedRange B).starProjection x) = D x at hd
  rwa [hc, hd] at he

lemma partialIsometry_commute (A B W : H →L[ℂ] H)
    (h : ∀ x, ‖A x‖ = ‖B x‖) (hWA : Commute W A) (hWB : Commute W B)
    (hWP : Commute W (closedRange B).starProjection) :
    Commute W (partialIsometry A B) := by
  have hv : partialIsometry A B * B = A := by
    ext x
    exact partialIsometry_apply A B h x
  have hp := partialIsometry_right_support A B
  apply eq_of_right_support (B := B)
  · calc
      (W * partialIsometry A B) * B = W * A := by rw [mul_assoc, hv]
      _ = A * W := hWA.eq
      _ = (partialIsometry A B * B) * W := by rw [hv]
      _ = (partialIsometry A B * W) * B := by
        rw [mul_assoc, ← hWB.eq, ← mul_assoc]
  · rw [mul_assoc, hp]
  · rw [mul_assoc, hWP.eq, ← mul_assoc, hp]

lemma closedRange_projection_mem (M : VonNeumannAlgebra H)
    (B : H →L[ℂ] H) (hB : B ∈ M) : (closedRange B).starProjection ∈ M := by
  apply (VonNeumannAlgebra.IsStarProjection.mem_iff
    isStarProjection_starProjection M).mpr
  intro W hW
  rw [Submodule.range_starProjection]
  have hi : B.range ∈ Module.End.invtSubmodule W.toLinearMap := by
    apply (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mpr
    rintro y ⟨x, rfl⟩
    refine ⟨W x, ?_⟩
    exact congrArg (fun T : H →L[ℂ] H => T x)
      ((VonNeumannAlgebra.mem_commutant_iff.mp hW) B hB)
  exact Submodule.topologicalClosure_mem_invtSubmodule hi

lemma partialIsometry_mem (M : VonNeumannAlgebra H) (A B : H →L[ℂ] H)
    (hA : A ∈ M) (hB : B ∈ M) (h : ∀ x, ‖A x‖ = ‖B x‖) :
    partialIsometry A B ∈ M := by
  rw [← M.commutant_commutant]
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro W hW
  apply (partialIsometry_commute A B W h
    ((VonNeumannAlgebra.mem_commutant_iff.mp hW) A hA).symm
    ((VonNeumannAlgebra.mem_commutant_iff.mp hW) B hB).symm
    ((VonNeumannAlgebra.mem_commutant_iff.mp hW) _
      (closedRange_projection_mem M B hB)).symm).eq

lemma abs_mem (M : VonNeumannAlgebra H) (A : H →L[ℂ] H) (hA : A ∈ M) :
    CFC.abs A ∈ M := by
  rw [← M.commutant_commutant]
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro W hW
  exact ((show Commute A W from
    (VonNeumannAlgebra.mem_commutant_iff.mp hW) A hA).cfcAbs_left
      (show Commute A (star W) from
        (VonNeumannAlgebra.mem_commutant_iff.mp (star_mem hW)) A hA)).symm.eq

lemma ker_abs (A : H →L[ℂ] H) : (CFC.abs A).ker = A.ker := by
  ext x
  change CFC.abs A x = 0 ↔ A x = 0
  rw [← norm_eq_zero, norm_abs_apply, norm_eq_zero]

lemma closedRange_abs (A : H →L[ℂ] H) : closedRange (CFC.abs A) = A.kerᗮ := by
  have hadj : (CFC.abs A).adjoint = CFC.abs A := (CFC.abs_nonneg A).star_eq
  have hc := (CFC.abs A).orthogonal_ker
  rw [ker_abs, hadj] at hc
  exact hc.symm

def polar (A : H →L[ℂ] H) : H →L[ℂ] H := partialIsometry A (CFC.abs A)

lemma polar_mul_abs (A : H →L[ℂ] H) : polar A * CFC.abs A = A := by
  ext x
  exact partialIsometry_apply A (CFC.abs A) (fun y => (norm_abs_apply A y).symm) x

lemma polar_initial (A : H →L[ℂ] H) : star (polar A) * polar A = A.kerᗮ.starProjection := by
  simpa only [polar, closedRange_abs] using
    partialIsometry_initial A (CFC.abs A) (fun y => (norm_abs_apply A y).symm)

lemma polar_final (A : H →L[ℂ] H) :
    polar A * star (polar A) = (closedRange A).starProjection :=
  partialIsometry_final A (CFC.abs A) (fun y => (norm_abs_apply A y).symm)

lemma polar_mem (M : VonNeumannAlgebra H) (A : H →L[ℂ] H) (hA : A ∈ M) : polar A ∈ M :=
  partialIsometry_mem M A (CFC.abs A) hA (abs_mem M A hA)
    (fun y => (norm_abs_apply A y).symm)

theorem trace_support_eq (M : VonNeumannAlgebra H)
    (τ : (H →L[ℂ] H) → ℂ)
    (hτ : ∀ a ∈ M, ∀ b ∈ M, τ (a * b) = τ (b * a))
    (A : H →L[ℂ] H) (hA : A ∈ M) :
    τ A.kerᗮ.starProjection = τ (closedRange A).starProjection := by
  rw [← polar_initial A, ← polar_final A]
  exact hτ _ (star_mem (polar_mem M A hA)) _ (polar_mem M A hA)

end Invariant233.GeneralPolar

end

end OAI
