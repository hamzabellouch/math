import OAI.Analysis.IrrationalRotation.Sampling.MixedRadixLaw
import OAI.Analysis.IrrationalRotation.Sampling.MixedRadixNonterminal
import OAI.Analysis.IrrationalRotation.Sampling.MixedRadixTransport

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Invariant233.MixedRadix

theorem digitLaw_ae_nonterminal {r : ℕ → ℕ} (hr : ∀ n, 2 ≤ r n)
    (hp : ∀ n, 0 < r n) : ∀ᵐ d ∂digitLaw r hp, Nonterminal d := by
  let : ∀ n, NeZero (r n) := fun n => ⟨ne_of_gt (hp n)⟩
  simpa only [digitLaw] using ae_nonterminal_uniformDigits hr

theorem circleValue_measurePreserving_digitLaw {r : ℕ → ℕ}
    (hr : ∀ n, 2 ≤ r n) (hp : ∀ n, 0 < r n) :
    MeasurePreserving (@circleValue r) (digitLaw r hp) volume := by
  exact circleValue_measurePreserving hr (digitLaw r hp) (map_ofDigits_eq_volume r hr)

theorem map_circleValue_digitLaw {r : ℕ → ℕ}
    (hr : ∀ n, 2 ≤ r n) (hp : ∀ n, 0 < r n) :
    (digitLaw r hp).map circleValue = volume :=
  (circleValue_measurePreserving_digitLaw hr hp).map_eq

theorem ae_circleCanonical_circleValue {r : ℕ → ℕ}
    (hr : ∀ n, 2 ≤ r n) (hp : ∀ n, 0 < r n) :
    ∀ᵐ d ∂digitLaw r hp, circleCanonical r hp (circleValue d) = d := by
  filter_upwards [digitLaw_ae_nonterminal hr hp] with d hd
  exact circleCanonical_circleValue hp d hd

theorem map_circleCanonical_volume {r : ℕ → ℕ}
    (hr : ∀ n, 2 ≤ r n) (hp : ∀ n, 0 < r n) :
    (volume : Measure (AddCircle (1 : ℝ))).map (circleCanonical r hp) =
      digitLaw r hp :=
  DensityTransport.map_inverse_eq (measurable_circleValue hr)
    (measurable_circleCanonical r hp) (map_circleValue_digitLaw hr hp)
    (ae_circleCanonical_circleValue hr hp)

theorem circleCanonical_measurePreserving {r : ℕ → ℕ}
    (hr : ∀ n, 2 ≤ r n) (hp : ∀ n, 0 < r n) :
    MeasurePreserving (circleCanonical r hp) volume (digitLaw r hp) :=
  ⟨measurable_circleCanonical r hp, map_circleCanonical_volume hr hp⟩

theorem digitLaw_circle_density_transport {r : ℕ → ℕ}
    (hr : ∀ n, 2 ≤ r n) (hp : ∀ n, 0 < r n)
    {h : Digits r → ℝ} (hh : Measurable h) :
    ((digitLaw r hp).withDensity (fun d => ENNReal.ofReal (h d))).map circleValue =
      volume.withDensity (fun x : AddCircle (1 : ℝ) =>
        ENNReal.ofReal (h (circleCanonical r hp x))) ∧
    eLpNorm (h ∘ circleCanonical r hp) 2 volume = eLpNorm h 2 (digitLaw r hp) :=
  circle_density_transport hr hp (digitLaw r hp) (map_ofDigits_eq_volume r hr)
    (digitLaw_ae_nonterminal hr hp) hh

theorem digitLaw_circle_density_transport_ae {r : ℕ → ℕ}
    (hr : ∀ n, 2 ≤ r n) (hp : ∀ n, 0 < r n)
    {h : Digits r → ℝ} (hh : AEMeasurable h (digitLaw r hp)) :
    ((digitLaw r hp).withDensity (fun d => ENNReal.ofReal (h d))).map circleValue =
      volume.withDensity (fun x : AddCircle (1 : ℝ) =>
        ENNReal.ofReal (h (circleCanonical r hp x))) ∧
    eLpNorm (h ∘ circleCanonical r hp) 2 volume = eLpNorm h 2 (digitLaw r hp) :=
  DensityTransport.real_density_transport_ae (measurable_circleValue hr)
    (measurable_circleCanonical r hp) (map_circleValue_digitLaw hr hp)
    (ae_circleCanonical_circleValue hr hp) hh

theorem memLp_circleCanonical {r : ℕ → ℕ}
    (hr : ∀ n, 2 ≤ r n) (hp : ∀ n, 0 < r n)
    {h : Digits r → ℝ} {p : ℝ≥0∞} (hh : MemLp h p (digitLaw r hp)) :
    MemLp (h ∘ circleCanonical r hp) p volume :=
  hh.comp_measurePreserving (circleCanonical_measurePreserving hr hp)

end Invariant233.MixedRadix

end OAI
