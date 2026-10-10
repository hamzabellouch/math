import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FockNorm
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.HalfFilledSector
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.HubbardReduction

namespace OAI

/-! Concrete hopping blocks on the actual half-filled Fock basis. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators InnerProductSpace

section Coordinates
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

def coordinateInclusionLinear (f : α → β) :
    EuclideanSpace ℂ α →ₗ[ℂ] EuclideanSpace ℂ β := by
  classical
  exact
    { toFun := fun x => ∑ a, x a • EuclideanSpace.single (f a) 1
      map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [smul_smul, Finset.smul_sum] }

def coordinateInclusion (f : α → β) :
    EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ β :=
  LinearMap.toContinuousLinearMap (coordinateInclusionLinear f)

theorem coordinateInclusion_single [DecidableEq α] [DecidableEq β] (f : α → β) (a : α) :
    coordinateInclusion f (EuclideanSpace.single a (1 : ℂ)) =
      EuclideanSpace.single (f a) (1 : ℂ) := by
  classical
  simp [coordinateInclusion, coordinateInclusionLinear, PiLp.single_apply]
  ext b
  simp [PiLp.single_apply]

theorem coordinateInclusion_apply_image (f : α → β) (hf : Function.Injective f)
    (x : EuclideanSpace ℂ α) (a : α) : coordinateInclusion f x (f a) = x a := by
  classical
  simp [coordinateInclusion, coordinateInclusionLinear, Pi.single_apply, hf.eq_iff]

theorem coordinateInclusion_apply_outside (f : α → β)
    (x : EuclideanSpace ℂ α) (b : β) (hb : ∀ a, f a ≠ b) :
    coordinateInclusion f x b = 0 := by
  classical
  simp [coordinateInclusion, coordinateInclusionLinear,
    fun a => Ne.symm (hb a)]

theorem coordinateInclusion_norm_map (f : α → β) (hf : Function.Injective f)
    (x : EuclideanSpace ℂ α) : ‖coordinateInclusion f x‖ = ‖x‖ := by
  classical
  have hsq : ‖coordinateInclusion f x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    let S := Finset.univ.image f
    have hsum : (∑ b ∈ S, ‖coordinateInclusion f x b‖ ^ 2) =
        ∑ b, ‖coordinateInclusion f x b‖ ^ 2 := by
      apply Finset.sum_subset (Finset.subset_univ S)
      intro b _ hb
      have hout : ∀ a, f a ≠ b := by
        intro a ha
        exact hb (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ha⟩)
      rw [coordinateInclusion_apply_outside f x b hout]
      simp
    rw [← hsum]
    unfold S
    rw [Finset.sum_image]
    · simp only [coordinateInclusion_apply_image f hf]
    · intro a _ b _ hab
      exact hf hab
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

theorem coordinateInclusion_norm_le (f : α → β) (hf : Function.Injective f) :
    ‖coordinateInclusion f‖ ≤ 1 := by
  apply (coordinateInclusion f).opNorm_le_bound zero_le_one
  intro x
  rw [coordinateInclusion_norm_map f hf, one_mul]

def coordinateRestriction (f : α → β) :
    EuclideanSpace ℂ β →L[ℂ] EuclideanSpace ℂ α := (coordinateInclusion f).adjoint

@[simp] theorem coordinateRestriction_apply (f : α → β)
    (x : EuclideanSpace ℂ β) (a : α) : coordinateRestriction f x a = x (f a) := by
  classical
  have h := ContinuousLinearMap.adjoint_inner_right (coordinateInclusion f)
    (EuclideanSpace.single a (1 : ℂ)) x
  rw [coordinateInclusion_single, EuclideanSpace.inner_single_left,
    EuclideanSpace.inner_single_left] at h
  simpa only [coordinateRestriction, map_one, one_mul] using h

theorem coordinateRestriction_norm_le (f : α → β) (hf : Function.Injective f) :
    ‖coordinateRestriction f‖ ≤ 1 := by
  change ‖(coordinateInclusion f).adjoint‖ ≤ 1
  rw [LinearIsometryEquiv.norm_map]
  exact coordinateInclusion_norm_le f hf

theorem coordinateCompression_norm (R : EuclideanSpace ℂ β →L[ℂ] EuclideanSpace ℂ γ)
    (T : EuclideanSpace ℂ β →L[ℂ] EuclideanSpace ℂ β)
    (I : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ β)
    (hR : ‖R‖ ≤ 1) (hI : ‖I‖ ≤ 1) : ‖R.comp (T.comp I)‖ ≤ ‖T‖ := by
  calc
    _ ≤ ‖R‖ * ‖T.comp I‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (‖T‖ * 1) := mul_le_mul hR
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left hI (norm_nonneg _))) (norm_nonneg _) zero_le_one
    _ = _ := by ring

end Coordinates

abbrev ActualHubbardLowSpace (m : ℕ) := EuclideanSpace ℂ (SourceSpinBasis (m + 1))
abbrev ActualHubbardHighSpace (m : ℕ) := EuclideanSpace ℂ (HalfFilledHighBasis m)

def highOccupationIndex (m : ℕ) (A : HalfFilledHighBasis m) :
    Finset (Fin ((2 * m + 1) + 1)) := A.val.val

theorem highOccupationIndex_injective (m : ℕ) : Function.Injective (highOccupationIndex m) := by
  intro A B h
  apply Subtype.ext
  exact Subtype.ext h

def lowFockInclusion (m : ℕ) : ActualHubbardLowSpace m →L[ℂ] FockCoordinateSpace (2 * m + 1) :=
  coordinateInclusion (spinOccupationSet m)

def highFockInclusion (m : ℕ) : ActualHubbardHighSpace m →L[ℂ] FockCoordinateSpace (2 * m + 1) :=
  coordinateInclusion (highOccupationIndex m)

def lowFockRestriction (m : ℕ) : FockCoordinateSpace (2 * m + 1) →L[ℂ] ActualHubbardLowSpace m :=
  coordinateRestriction (spinOccupationSet m)

def highFockRestriction (m : ℕ) : FockCoordinateSpace (2 * m + 1) →L[ℂ] ActualHubbardHighSpace m :=
  coordinateRestriction (highOccupationIndex m)

theorem lowFockInclusion_norm (m : ℕ) : ‖lowFockInclusion m‖ ≤ 1 :=
  coordinateInclusion_norm_le _ (spinOccupationSet_injective m)

theorem highFockInclusion_norm (m : ℕ) : ‖highFockInclusion m‖ ≤ 1 :=
  coordinateInclusion_norm_le _ (highOccupationIndex_injective m)

theorem lowFockRestriction_norm (m : ℕ) : ‖lowFockRestriction m‖ ≤ 1 :=
  coordinateRestriction_norm_le _ (spinOccupationSet_injective m)

theorem highFockRestriction_norm (m : ℕ) : ‖highFockRestriction m‖ ≤ 1 :=
  coordinateRestriction_norm_le _ (highOccupationIndex_injective m)

variable {Edge : Type*} [Fintype Edge]

def actualHubbardCoupling (m : ℕ) (left right : Edge → Fin (m + 1)) (t : Edge → ℝ) :
    ActualHubbardLowSpace m →L[ℝ] ActualHubbardHighSpace m :=
  ((highFockRestriction m).comp
    ((fockOperator (graphHopping m left right (fun e => (t e : ℂ)))).comp
      (lowFockInclusion m))).restrictScalars ℝ

def actualHubbardHighHopping (m : ℕ) (left right : Edge → Fin (m + 1)) (t : Edge → ℝ) :
    ActualHubbardHighSpace m →L[ℝ] ActualHubbardHighSpace m :=
  ((highFockRestriction m).comp
    ((fockOperator (graphHopping m left right (fun e => (t e : ℂ)))).comp
      (highFockInclusion m))).restrictScalars ℝ

theorem actualHubbardCoupling_norm (m : ℕ) (left right : Edge → Fin (m + 1)) (t : Edge → ℝ) :
    ‖actualHubbardCoupling m left right t‖ ≤ 4 * ∑ e, |t e| := by
  unfold actualHubbardCoupling
  rw [ContinuousLinearMap.norm_restrictScalars]
  have hgraph : ‖fockOperator (graphHopping m left right (fun e => (t e : ℂ)))‖ ≤
      4 * ∑ e, |t e| := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      fockOperator_graphHopping_norm m left right (fun e => (t e : ℂ))
  exact (coordinateCompression_norm _ _ _ (highFockRestriction_norm m)
    (lowFockInclusion_norm m)).trans hgraph

theorem actualHubbardHighHopping_norm (m : ℕ) (left right : Edge → Fin (m + 1)) (t : Edge → ℝ) :
    ‖actualHubbardHighHopping m left right t‖ ≤ 4 * ∑ e, |t e| := by
  unfold actualHubbardHighHopping
  rw [ContinuousLinearMap.norm_restrictScalars]
  have hgraph : ‖fockOperator (graphHopping m left right (fun e => (t e : ℂ)))‖ ≤
      4 * ∑ e, |t e| := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      fockOperator_graphHopping_norm m left right (fun e => (t e : ℂ))
  exact (coordinateCompression_norm _ _ _ (highFockRestriction_norm m)
    (highFockInclusion_norm m)).trans hgraph

/-- The global perturbation bound with the actual Fock hopping blocks.
Its only smallness condition is the explicit polynomial edge-sum bound. -/
theorem actual_hubbard_second_order (m : ℕ) (U R : ℝ)
    (V : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hsymm : ∀ i j, V i j = V j i) (hrow : ∀ i, ∑ j, |V i j| ≤ R)
    (hUR : R < U) (left right : Edge → Fin (m + 1)) (t : Edge → ℝ)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hsmall : epsilon < 1 / 2)
    (ht : 4 * ∑ e, |t e| ≤ epsilon * (U - R)) :
    let weight : HalfFilledHighBasis m → ℝ :=
      fun A => chargePenalty U V (occupationAt m A.val.val)
    |Perturbation.blockBottom (diagonalPenalty weight)
        (actualHubbardHighHopping m left right t) (actualHubbardCoupling m left right t) -
      Perturbation.effectiveBottom (0 : ActualHubbardLowSpace m →L[ℝ] ActualHubbardLowSpace m)
        (diagonalPenalty (fun A => (weight A)⁻¹)) (actualHubbardCoupling m left right t)| ≤
      2 * (U - R) * epsilon ^ 3 := by
  exact hubbard_charge_second_order U R V (fun A : HalfFilledBasis m => occupationAt m A.val)
    hsymm hrow hUR (halfFilled_occupation_sum m)
    (actualHubbardCoupling m left right t) (actualHubbardHighHopping m left right t)
    hepsilon hsmall ((actualHubbardCoupling_norm m left right t).trans ht)
    ((actualHubbardHighHopping_norm m left right t).trans ht)

end ContinuumCoulomb.HubbardGlobal

end

end OAI
