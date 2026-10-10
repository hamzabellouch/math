import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHyperbolicMeasure

namespace OAI

/-! The quotient Borel structure and intrinsic hyperbolic measure.
The measure is independent of the measurable fundamental domain. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

lemma cubicThetaQuotient_measurable_iff (S : Set CubicThetaQuotient) :
    MeasurableSet S ↔ MeasurableSet (cubicThetaQuotientMap ⁻¹' S) := by
  constructor
  · exact fun h => h.preimage cubicThetaQuotientMap_open.continuous.measurable
  · intro h
    have he : cubicThetaBorelSection ⁻¹' (cubicThetaQuotientMap ⁻¹' S)=S := by
      ext q
      change cubicThetaQuotientMap (cubicThetaBorelSection q)∈S ↔ q∈S
      rw [cubicThetaBorelSection_rightInverse q]
    rw [← he]
    exact h.preimage cubicThetaBorelSection_measurable

instance cubicThetaPrincipalPointMeasure_invariant :
    SMulInvariantMeasure cubicThetaPrincipalGroup CubicThetaPoint cubicThetaPointMeasure where
  measure_preimage_smul g _S hS :=
    SMulInvariantMeasure.measure_preimage_smul (g:cubicThetaPrincipalGroup).val hS

instance cubicThetaPrincipalGroup_countable : Countable cubicThetaPrincipalGroup := by
  let : Countable Eisenstein := coordinatesEquiv.symm.injective.countable
  let : Countable (Matrix (Fin 2) (Fin 2) Eisenstein) := by
    change Countable (Fin 2 → Fin 2 → Eisenstein)
    infer_instance
  have hi : Function.Injective (fun g : Matrix.SpecialLinearGroup (Fin 2) Eisenstein => g.val) := by
    intro g h he
    exact Subtype.ext he
  let : Countable (Matrix.SpecialLinearGroup (Fin 2) Eisenstein) := hi.countable
  have hj : Function.Injective (fun g : cubicThetaPrincipalGroup => g.val) := by
    intro g h he
    exact Subtype.ext he
  exact hj.countable

lemma cubicThetaQuotientMeasure_apply {S : Set CubicThetaQuotient} (hS : MeasurableSet S) :
    cubicThetaQuotientMeasure S=
      cubicThetaPointMeasure (cubicThetaQuotientMap ⁻¹' S ∩ cubicThetaFundamentalDomain) := by
  rw [cubicThetaQuotientMeasure,Measure.map_apply cubicThetaQuotientMap_open.continuous.measurable hS,
    Measure.restrict_apply (hS.preimage cubicThetaQuotientMap_open.continuous.measurable)]

lemma cubicThetaQuotientMeasure_independent {D : Set CubicThetaPoint}
    (hD : IsFundamentalDomain cubicThetaPrincipalGroup D cubicThetaPointMeasure) :
    cubicThetaQuotientMeasure=(cubicThetaPointMeasure.restrict D).map cubicThetaQuotientMap := by
  ext S hS
  rw [cubicThetaQuotientMeasure_apply hS,
    Measure.map_apply cubicThetaQuotientMap_open.continuous.measurable hS,
    Measure.restrict_apply (hS.preimage cubicThetaQuotientMap_open.continuous.measurable)]
  apply (cubicThetaFundamentalDomain_isFundamentalDomain cubicThetaPointMeasure).measure_set_eq hD
    (hS.preimage cubicThetaQuotientMap_open.continuous.measurable)
  intro g
  ext p
  simp only [mem_preimage,cubicThetaQuotient_covering.map_smul]

lemma cubicThetaQuotientMeasure_integral (F : CubicThetaQuotient → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ q, F q ∂cubicThetaQuotientMeasure)=
      ∫⁻ p in cubicThetaFundamentalDomain, F (cubicThetaQuotientMap p) ∂cubicThetaPointMeasure := by
  exact lintegral_map hF cubicThetaQuotientMap_open.continuous.measurable

end CubicFirstMoment

end

end OAI
