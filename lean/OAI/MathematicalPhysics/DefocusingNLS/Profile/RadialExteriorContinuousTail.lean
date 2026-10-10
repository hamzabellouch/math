import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorContinuousData
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorParameterContinuity

namespace OAI

/-! A continuous family of actual fixed-power tail solutions, with canonical polynomial data. -/

open Set
open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem exists_continuous_radialExterior_corrections (S : Set (ℂ × ℂ))
    (n j : ℕ) (m : ℂ) (δ T : ℝ) (hδ : 0 < δ) (hT : 0 ≤ T)
    (hκ : ∀ z : S, radialExteriorMatrixBound z.val.1+
      radialExteriorCutoffRate n m δ < 2*(j : ℝ))
    (hbase : ∀ (z : S) t,
      ‖boundedRadialPolynomialAfter T (radialExteriorExpansion z.val.1 n z.val.2 j) t-m‖ ≤ δ/4) :
    ∃ v : S → ℝ →ᵇ ℂ × ℂ, Continuous v ∧ ∀ z,
      let f := boundedRadialPolynomialAfter T (radialExteriorExpansion z.val.1 n z.val.2 j)
      let r := boundedRadialResidualAfter T (radialExteriorResidualQuotient z.val.1 n z.val.2 j)
      ‖v z‖ ≤ ‖r‖/(2*(j : ℝ)-
        (radialExteriorMatrixBound z.val.1+radialExteriorCutoffRate n m δ)) ∧
      (∀ t, v z t=radialExteriorTailIntegral (2*(j : ℝ))
        (fun s => radialExteriorErrorField (2*(j : ℝ)) z.val.1
          (radialExteriorCutoffPower n m δ) f r s (v z s)) t) ∧
      ∀ t, HasDerivAt (fun s => v z s)
        ((2*(j : ℝ)) • v z t+(0,-Complex.I*(Real.exp (2*t)/2 : ℝ)*(v z t).2)+
          radialExteriorErrorField (2*(j : ℝ)) z.val.1
            (radialExteriorCutoffPower n m δ) f r t (v z t)) t := by
  classical
  let f : S → ℝ →ᵇ ℂ := fun z =>
    boundedRadialPolynomialAfter T (radialExteriorExpansion z.val.1 n z.val.2 j)
  let r : S → ℝ →ᵇ ℂ × ℂ := fun z =>
    boundedRadialResidualAfter T (radialExteriorResidualQuotient z.val.1 n z.val.2 j)
  have hex (z : S) := exists_radialExterior_weighted_ODE (2*(j : ℝ))
    (radialExteriorMatrixBound z.val.1+radialExteriorCutoffRate n m δ) ‖r z‖
    (lt_of_le_of_lt (add_nonneg (radialExteriorMatrixBound_pos _).le
      (radialExteriorCutoffRate_nonneg _ _ _)) (hκ z))
    (add_nonneg (radialExteriorMatrixBound_pos _).le (radialExteriorCutoffRate_nonneg _ _ _))
    (hκ z) (norm_nonneg _)
    (radialExteriorErrorField (2*(j : ℝ)) z.val.1 (radialExteriorCutoffPower n m δ) (f z) (r z))
    (radialExteriorErrorField_continuous _ _ _ (radialExteriorCutoffPower_continuous _ _ _)
      _ (f z).continuous (r z))
    (fun t => by rw [radialExteriorErrorField_zero]; exact (r z).norm_coe_le_norm t)
    (radialExteriorErrorField_difference _ _ (radialExteriorCutoffRate_nonneg _ _ _) _ _
      (radialExteriorCutoffPower_difference n m δ hδ.le) _ _)
  choose v hv using hex
  refine ⟨v,?_,hv⟩
  exact continuous_radialExterior_corrections S n m δ (2*(j : ℝ)) hδ
    (fun z => z.val.1) continuous_subtype_val.fst
    f ((continuous_radialExteriorBase n j T hT).comp continuous_subtype_val)
    r ((continuous_radialExteriorSource n j T hT).comp continuous_subtype_val)
    hκ hbase v (fun z => (hv z).2.1)

theorem continuous_radialExterior_corrected_boundary (S : Set (ℂ × ℂ))
    (n j : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (v : S → ℝ →ᵇ ℂ × ℂ) (hv : Continuous v) :
    Continuous (fun z : S => radialPolynomialJet (radialExteriorExpansion z.val.1 n z.val.2 j) t+
      radialExteriorUnweight (2*(j : ℝ)) (v z) t) := by
  apply ((continuous_radialExteriorPolynomialJet n j t ht).comp continuous_subtype_val).add
  have he : Continuous (fun z => v z t) := by
    convert! (BoundedContinuousFunction.lipschitz_eval_const t).continuous.comp hv using 1
  change Continuous (fun z : S => Real.exp (-(2*(j : ℝ))*t) • v z t)
  exact (continuous_const : Continuous (fun _ : S => Real.exp (-(2*(j : ℝ))*t))).smul he

end DefocusingNLS

end OAI
