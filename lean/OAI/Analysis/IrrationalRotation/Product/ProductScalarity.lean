import OAI.Analysis.IrrationalRotation.Product.ProductCovariance
import OAI.Analysis.IrrationalRotation.Rotation.ActualRotationCentrality
import OAI.Analysis.IrrationalRotation.Analysis.ScalarFieldLift
import OAI.Analysis.IrrationalRotation.Operators.RepresentedCommutation
import OAI.Analysis.IrrationalRotation.Product.ProductHilbert
import OAI.Analysis.IrrationalRotation.Model.OperatorProperties

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace Invariant233.ProductModel

local notation "S" => LinearIsometry.toContinuousLinearMap
  (LinearIsometryEquiv.toLinearIsometry (WeightedShift.shift 1))

theorem scalar_of_mem_factor_central (θ : ℕ → ℝ)
    (hθ : JointlyRationallyIndependent θ) (T : Hilbert →L[ℂ] Hilbert)
    (hT : T ∈ factor θ)
    (hcentral : ∀ B : Hilbert →L[ℂ] Hilbert, B ∈ factor θ → Commute T B) :
    ∃ c : ℂ, T = c • (1 : Hilbert →L[ℂ] Hilbert) := by
  obtain ⟨A, hbound, hm, hrep, huniq⟩ := exists_unique_field hT
  let b : HilbertBasis ℤ ℂ Fiber :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ Fiber)
  have hS : Commute T shiftOperator :=
    hcentral shiftOperator (subset_vonNeumannGenerated _ (Or.inl (Set.mem_singleton _)))
  have hAS : ∀ᵐ x ∂baseMeasure, Commute (A x) S :=
    DirectIntegral.ae_commute_of_represented_commute b T shiftOperator A (fun _ => S)
      hrep shiftOperator_ae hS
  let g : Base → ℂ := fun x => (AddCircle.toCircle (x 0) : ℂ)
  have hg : Measurable g := by
    exact (continuous_subtype_val.comp
      ((AddCircle.continuous_toCircle (T := (1 : ℝ))).comp
        (show Continuous (fun x : Base => x 0) from continuous_apply 0))).measurable
  have hb : ∀ x, ‖g x‖ ≤ 1 := by
    intro x
    exact (Circle.norm_coe (AddCircle.toCircle (x 0))).le
  let D := multiplier θ g 1 (by norm_num) hg hb
  have hDmem : D ∈ factor θ := by
    apply subset_vonNeumannGenerated
    exact Or.inr ⟨g, 1, by norm_num, hg, hb, rfl⟩
  have hAD : ∀ᵐ x ∂baseMeasure,
      Commute (A x) (WeightedShift.diagonal (multiplierField θ g 1 hb x)) :=
    DirectIntegral.ae_commute_of_represented_commute b T D A
      (fun x => WeightedShift.diagonal (multiplierField θ g 1 hb x))
      hrep (multiplier_ae θ g 1 (by norm_num) hg hb) (hcentral D hDmem)
  have hmeas : NullMeasurable
      (fun x => A x (lp.single 2 (0 : ℤ) (1 : ℂ)) 0) baseMeasure :=
    ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0).continuous.comp_stronglyMeasurable
      (hm (lp.single 2 (0 : ℤ) (1 : ℂ)))).measurable.nullMeasurable
  have hcov : ∀ᵐ x ∂baseMeasure, S * A (rotation θ x) = A x * S := by
    filter_upwards [field_covariance hT A hrep] with x hall
    have hx := hall 1
    have heq : rotationIterate θ 1 x = rotation θ x := by
      funext i
      simp only [rotationIterate, Int.cast_one, one_mul, rotation]
    rw [heq] at hx
    exact hx.symm
  apply DirectIntegral.scalar_of_representation_ae_scalar T A hrep
  apply WeightedShift.ae_eq_scalar_over_product_rotation θ hθ 0 A
    (multiplierField θ g 1 hb) _ hmeas hAD hAS hcov
  apply Eventually.of_forall
  intro x k
  change (AddCircle.toCircle (x 0 + (((k : ℝ) * θ 0 : ℝ) : Circle)) : ℂ) =
    (AddCircle.toCircle (x 0 + k • (θ 0 : Circle)) : ℂ)
  congr 3
  simpa only [zsmul_eq_mul] using
    (AddCircle.coe_zsmul (p := (1 : ℝ)) (n := k) (x := θ 0))

theorem factor_isFactor (θ : ℕ → ℝ) (hθ : JointlyRationallyIndependent θ) :
    IsFactor (factor θ) :=
  ⟨inferInstance, fun T hT hcentral => scalar_of_mem_factor_central θ hθ T hT hcentral⟩

end Invariant233.ProductModel

end

end OAI
