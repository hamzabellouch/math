import OAI.Analysis.IrrationalRotation.Model.MixedRadixCircle
import OAI.Analysis.IrrationalRotation.Sampling.MixedRadix
import OAI.Analysis.IrrationalRotation.Analysis.DensityTransport

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Invariant233.MixedRadix

theorem measurePreserving_unitCircle :
    MeasurePreserving (fun x : ℝ => (x : AddCircle (1 : ℝ)))
      (volume.restrict (Set.Ico 0 1)) volume := by
  rw [restrict_Ico_eq_restrict_Ioc]
  simpa using AddCircle.measurePreserving_mk (1 : ℝ) 0

theorem measurable_circleValue {r : ℕ → ℕ} (hr : ∀ n, 2 ≤ r n) :
    Measurable (@circleValue r) :=
  AddCircle.measurable_mk'.comp (measurable_ofDigits hr)

theorem measurable_circleCanonical (r : ℕ → ℕ) (hr : ∀ n, 0 < r n) :
    Measurable (circleCanonical r hr) :=
  (measurable_canonicalDigits r hr).comp
    (measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable)

theorem circleValue_circleCanonical {r : ℕ → ℕ} (hr : ∀ n, 2 ≤ r n)
    (hp : ∀ n, 0 < r n) (x : AddCircle (1 : ℝ)) :
    circleValue (circleCanonical r hp x) = x := by
  have hx : (AddCircle.equivIco (1 : ℝ) 0 x : ℝ) ∈ Set.Ico 0 1 := by
    simpa using (AddCircle.equivIco (1 : ℝ) 0 x).property
  unfold circleValue circleCanonical
  rw [ofDigits_canonicalDigits hr hx]
  exact AddCircle.coe_equivIco

theorem circleCanonical_circleValue {r : ℕ → ℕ} (hp : ∀ n, 0 < r n)
    (d : Digits r) (hnt : Nonterminal d) :
    circleCanonical r hp (circleValue d) = d := by
  have hx : ofDigits d ∈ Set.Ico (0 : ℝ) (0 + 1) := by
    simpa using ofDigits_mem_Ico hp d hnt
  unfold circleCanonical circleValue
  rw [AddCircle.equivIco_coe_eq hx]
  exact canonicalDigits_ofDigits hp d hnt

theorem circleValue_measurePreserving {r : ℕ → ℕ} (hr : ∀ n, 2 ≤ r n)
    (μ : Measure (Digits r))
    (hlaw : μ.map ofDigits = volume.restrict (Set.Ico 0 1)) :
    MeasurePreserving (@circleValue r) μ volume := by
  exact measurePreserving_unitCircle.comp ⟨measurable_ofDigits hr, hlaw⟩

theorem circle_density_transport {r : ℕ → ℕ} (hr : ∀ n, 2 ≤ r n)
    (hp : ∀ n, 0 < r n) (μ : Measure (Digits r))
    (hlaw : μ.map ofDigits = volume.restrict (Set.Ico 0 1))
    (hnt : ∀ᵐ d ∂μ, Nonterminal d) {h : Digits r → ℝ} (hh : Measurable h) :
    (μ.withDensity (fun d => ENNReal.ofReal (h d))).map circleValue =
      volume.withDensity (fun x : AddCircle (1 : ℝ) =>
        ENNReal.ofReal (h (circleCanonical r hp x))) ∧
    eLpNorm (h ∘ circleCanonical r hp) 2 volume = eLpNorm h 2 μ := by
  apply DensityTransport.real_density_transport (measurable_circleValue hr)
    (measurable_circleCanonical r hp) (circleValue_measurePreserving hr μ hlaw).map_eq
  · filter_upwards [hnt] with d hd
    exact circleCanonical_circleValue hp d hd
  · exact hh

end Invariant233.MixedRadix

end OAI
