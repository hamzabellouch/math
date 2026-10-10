import OAI.Analysis.IrrationalRotation.Sampling.CharacterLawConvergence
import OAI.Analysis.IrrationalRotation.Analysis.WeakConvergenceAEContinuous

namespace OAI

noncomputable section

namespace Invariant233.CharacterLaws

open MeasureTheory Filter
open scoped Topology

theorem tendsto_integral_character_phase_of_ae_continuous
    {Z : Type*} [PseudoEMetricSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (q : ℕ → ℕ → ℕ) (m : ℕ)
    (hq : ∀ j i, 0 < q j i) (hmono : ∀ j, Monotone (q j))
    (hgap : ∀ i, i + 1 < m → Tendsto
      (fun j => (q j (i + 1) : ℝ) / (q j i : ℝ)) atTop atTop)
    {a : ℕ → Z} {b : Z} (ha : Tendsto a atTop (𝓝 b))
    {f : Z × UnitAddTorus (Fin m) → ℝ} (hf : Measurable f)
    (hc : ∀ᵐ y : UnitAddTorus (Fin m), ContinuousAt f (b, y))
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ z, |f z| ≤ B) :
    Tendsto (fun j => ∫ x : AddCircle (1 : ℝ),
      f (a j, fun i : Fin m => (q j i.val : ℤ) • x)) atTop
      (𝓝 (∫ y : UnitAddTorus (Fin m), f (b, y))) := by
  have hclaw : ∀ᵐ z ∂(haarPhaseLaw m b : Measure _), ContinuousAt f z := by
    change ∀ᵐ z ∂Measure.map (fun y : UnitAddTorus (Fin m) => (b, y)) volume,
      ContinuousAt f z
    apply (ae_map_iff
      (by fun_prop : Continuous (fun y : UnitAddTorus (Fin m) => (b, y))).measurable.aemeasurable
      (measurableSet_of_continuousAt f)).mpr
    exact hc
  have h := WeakConvergenceAEContinuous.tendsto_integral_of_ae_continuous
    (tendsto_characterPhaseLaw q m hq hmono hgap ha) hf hclaw hB hb
  have hmap (j : ℕ) :
      (∫ z, f z ∂(characterPhaseLaw (fun i : Fin m => q j i.val) (a j) : Measure _)) =
        ∫ x : AddCircle (1 : ℝ), f (a j, fun i : Fin m => (q j i.val : ℤ) • x) := by
    change (∫ z, f z ∂Measure.map
      (fun x => (a j, characterMap (fun i : Fin m => q j i.val) x)) volume) = _
    rw [integral_map
      (by fun_prop : Continuous
        (fun x => (a j, characterMap (fun i : Fin m => q j i.val) x))).measurable.aemeasurable
      hf.aestronglyMeasurable]
    rfl
  have hlim : (∫ z, f z ∂(haarPhaseLaw m b : Measure _)) =
      ∫ y : UnitAddTorus (Fin m), f (b, y) := by
    change (∫ z, f z ∂Measure.map (fun y : UnitAddTorus (Fin m) => (b, y)) volume) = _
    rw [integral_map
      (by fun_prop : Continuous (fun y : UnitAddTorus (Fin m) => (b, y))).measurable.aemeasurable
      hf.aestronglyMeasurable]
  simpa only [hmap, hlim] using h

theorem eventually_integral_character_phase_lt
    {Z : Type*} [PseudoEMetricSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (q : ℕ → ℕ → ℕ) (m : ℕ)
    (hq : ∀ j i, 0 < q j i) (hmono : ∀ j, Monotone (q j))
    (hgap : ∀ i, i + 1 < m → Tendsto
      (fun j => (q j (i + 1) : ℝ) / (q j i : ℝ)) atTop atTop)
    {a : ℕ → Z} {b : Z} (ha : Tendsto a atTop (𝓝 b))
    {f : Z × UnitAddTorus (Fin m) → ℝ} (hf : Measurable f)
    (hc : ∀ᵐ y : UnitAddTorus (Fin m), ContinuousAt f (b, y))
    {B δ : ℝ} (hB : 0 ≤ B) (hb : ∀ z, |f z| ≤ B)
    (hδ : (∫ y : UnitAddTorus (Fin m), f (b, y)) < δ) :
    ∀ᶠ j in atTop, (∫ x : AddCircle (1 : ℝ),
      f (a j, fun i : Fin m => (q j i.val : ℤ) • x)) < δ :=
  (tendsto_integral_character_phase_of_ae_continuous
    q m hq hmono hgap ha hf hc hB hb).eventually_lt_const hδ

end Invariant233.CharacterLaws

end

end OAI
