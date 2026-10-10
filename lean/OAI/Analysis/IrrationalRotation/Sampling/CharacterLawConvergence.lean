import OAI.Analysis.IrrationalRotation.Model.CharacterLaw
import OAI.Analysis.IrrationalRotation.Sampling.CharacterWeakConvergence

namespace OAI

noncomputable section

namespace Invariant233
namespace CharacterLaws

open MeasureTheory Filter
open scoped Topology

theorem tendsto_characterLaw
    (q : ℕ → ℕ → ℕ) (m : ℕ)
    (hq : ∀ j i, 0 < q j i) (hmono : ∀ j, Monotone (q j))
    (hgap : ∀ i, i + 1 < m → Tendsto
      (fun j => (q j (i + 1) : ℝ) / (q j i : ℝ)) atTop atTop) :
    Tendsto (fun j => characterLaw (fun i : Fin m => q j i.val)) atTop
      (𝓝 (torusHaar m)) := by
  apply (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mpr
  intro f
  have h := CharacterWeakConvergence.tendsto_integral_joint_characters
    q m hq hmono hgap f.toContinuousMap
  have hmap (j : ℕ) :
      (∫ y, f y ∂(characterLaw (fun i : Fin m => q j i.val) : Measure _)) =
        ∫ x : AddCircle (1 : ℝ), f (fun i : Fin m => (q j i.val : ℤ) • x) := by
    change (∫ y, f y ∂Measure.map (characterMap (fun i : Fin m => q j i.val)) volume) = _
    rw [integral_map
      (characterMap (fun i : Fin m => q j i.val)).continuous.measurable.aemeasurable
      f.continuous.aestronglyMeasurable]
    rfl
  simpa only [hmap, BoundedContinuousFunction.coe_toContinuousMap,
    torusHaar, ProbabilityMeasure.coe_mk] using h

theorem tendsto_apply_of_uniform_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : ℕ → E →L[ℂ] ℂ) (M : E →L[ℂ] ℂ)
    (hL : ∀ j, ‖L j‖ ≤ 1)
    (hconv : ∀ f, Tendsto (fun j => L j f) atTop (𝓝 (M f)))
    {f : ℕ → E} {g : E} (hf : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun j => L j (f j)) atTop (𝓝 (M g)) := by
  have hnorm : Tendsto (fun j => ‖f j - g‖) atTop (𝓝 0) := by
    have hg : Tendsto (fun _ : ℕ => g) atTop (𝓝 g) := tendsto_const_nhds
    simpa using (hf.sub hg).norm
  have hsmall : Tendsto (fun j => L j (f j - g)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun j => ?_) hnorm
    calc
      ‖L j (f j - g)‖ ≤ ‖L j‖ * ‖f j - g‖ := (L j).le_opNorm _
      _ ≤ 1 * ‖f j - g‖ := mul_le_mul_of_nonneg_right (hL j) (norm_nonneg _)
      _ = ‖f j - g‖ := one_mul _
  simpa only [map_sub, sub_add_cancel, zero_add] using hsmall.add (hconv g)

theorem tendsto_integral_character_phase
    {Z : Type*} [TopologicalSpace Z]
    (q : ℕ → ℕ → ℕ) (m : ℕ)
    (hq : ∀ j i, 0 < q j i) (hmono : ∀ j, Monotone (q j))
    (hgap : ∀ i, i + 1 < m → Tendsto
      (fun j => (q j (i + 1) : ℝ) / (q j i : ℝ)) atTop atTop)
    {a : ℕ → Z} {b : Z} (ha : Tendsto a atTop (𝓝 b))
    (f : C(Z × UnitAddTorus (Fin m), ℂ)) :
    Tendsto (fun j => ∫ x : AddCircle (1 : ℝ),
      f (a j, fun i : Fin m => (q j i.val : ℤ) • x)) atTop
      (𝓝 (∫ y : UnitAddTorus (Fin m), f (b, y))) := by
  let : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=
    circleHaar.property
  let L : ℕ → C(UnitAddTorus (Fin m), ℂ) →L[ℂ] ℂ :=
    fun j => CharacterWeakConvergence.pullbackIntegral volume
      (characterMap (fun i : Fin m => q j i.val))
  let M : C(UnitAddTorus (Fin m), ℂ) →L[ℂ] ℂ :=
    CharacterWeakConvergence.pullbackIntegral volume (ContinuousMap.id _)
  exact tendsto_apply_of_uniform_bound L M
    (fun j => CharacterWeakConvergence.pullbackIntegral_norm_le volume _)
    (fun g => CharacterWeakConvergence.tendsto_integral_joint_characters
      q m hq hmono hgap g)
    (f.curry.continuous.tendsto b |>.comp ha)

theorem integral_characterPhaseLaw {Z : Type*} [TopologicalSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] {m : ℕ} (q : Fin m → ℕ) (a : Z)
    (f : C(Z × UnitAddTorus (Fin m), ℂ)) :
    (∫ z, f z ∂(characterPhaseLaw q a : Measure _)) =
      ∫ x : AddCircle (1 : ℝ), f (a, characterMap q x) := by
  change (∫ z, f z ∂Measure.map (fun x => (a, characterMap q x)) volume) = _
  rw [integral_map
    (by fun_prop : Continuous (fun x => (a, characterMap q x))).measurable.aemeasurable
    f.continuous.aestronglyMeasurable]

theorem integral_haarPhaseLaw {Z : Type*} [TopologicalSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] (m : ℕ) (a : Z)
    (f : C(Z × UnitAddTorus (Fin m), ℂ)) :
    (∫ z, f z ∂(haarPhaseLaw m a : Measure _)) =
      ∫ y : UnitAddTorus (Fin m), f (a, y) := by
  change (∫ z, f z ∂Measure.map (fun y : UnitAddTorus (Fin m) => (a, y)) volume) = _
  rw [integral_map
    (by fun_prop : Continuous (fun y : UnitAddTorus (Fin m) => (a, y))).measurable.aemeasurable
    f.continuous.aestronglyMeasurable]

theorem tendsto_characterPhaseLaw
    {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (q : ℕ → ℕ → ℕ) (m : ℕ)
    (hq : ∀ j i, 0 < q j i) (hmono : ∀ j, Monotone (q j))
    (hgap : ∀ i, i + 1 < m → Tendsto
      (fun j => (q j (i + 1) : ℝ) / (q j i : ℝ)) atTop atTop)
    {a : ℕ → Z} {b : Z} (ha : Tendsto a atTop (𝓝 b)) :
    Tendsto (fun j => characterPhaseLaw (fun i : Fin m => q j i.val) (a j)) atTop
      (𝓝 (haarPhaseLaw m b)) := by
  apply (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mpr
  intro f
  have h := tendsto_integral_character_phase q m hq hmono hgap ha f.toContinuousMap
  simpa only [← BoundedContinuousFunction.coe_toContinuousMap,
    integral_characterPhaseLaw, integral_haarPhaseLaw, characterMap, ContinuousMap.coe_mk] using h

end CharacterLaws
end Invariant233

end

end OAI
