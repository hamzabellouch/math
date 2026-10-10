import OAI.Analysis.CircleDomains.Probability.MeasurableLinearInverse

namespace OAI

/-! Measurable zero extensions of the inverse on a Borel image piece. -/
open Set Function MeasureTheory
open scoped Topology NNReal Classical
noncomputable section
namespace CircleDomainRigidity

 def inverseOnPiece (F : ℂ → ℂ) (S T : Set ℂ) : ℂ → ℂ :=
  T.piecewise (invFunOn F S) (fun _ => 0)

lemma measurable_inverseOnPiece {F : ℂ → ℂ} {S T : Set ℂ} {K : ℝ≥0}
    (hF : AntilipschitzWith K (S.domRestrict F)) (hT : MeasurableSet T) (hTS : T ⊆ F '' S) :
    Measurable (inverseOnPiece F S T) :=
  ((inverseOn_lipschitz hF).continuousOn.mono hTS).measurable_piecewise continuousOn_const hT

lemma inverseOnPiece_eq {F : ℂ → ℂ} {S T : Set ℂ} {y : ℂ} (hy : y ∈ T) :
    inverseOnPiece F S T y = invFunOn F S y :=
  piecewise_eq_of_mem T _ _ hy

lemma measurable_inversePieceDifferential {F : ℂ → ℂ} {S T : Set ℂ} {K : ℝ≥0}
    (hF : AntilipschitzWith K (S.domRestrict F)) (hT : MeasurableSet T) (hTS : T ⊆ F '' S) :
    Measurable (fun y => (fderiv ℝ F (inverseOnPiece F S T y)).inverse) :=
  measurable_planar_linear_inverse.comp ((measurable_fderiv ℝ F).comp (measurable_inverseOnPiece hF hT hTS))

end CircleDomainRigidity

end

end OAI
