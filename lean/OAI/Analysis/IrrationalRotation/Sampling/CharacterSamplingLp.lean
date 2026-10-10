import OAI.Analysis.IrrationalRotation.Sampling.CharacterSamplingTests
import OAI.Analysis.IrrationalRotation.Analysis.SquaredIntegralLp

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology BigOperators

namespace Invariant233.CharacterSampling

local instance characterSamplingLpCircleProbability :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨by simp [AddCircle.measure_univ]⟩

lemma measurable_average (m : ℕ) (powers : Finset ℕ) (endpoint : Bool) :
    Measurable (fun p : (Fin m → ℝ) × UnitAddTorus (Fin m) =>
      average m powers endpoint p.1 p.2) := by
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro n hn
  apply Finset.measurable_prod
  intro i hi
  exact (measurable_kernel endpoint m).comp
    ((measurable_representative.comp ((measurable_pi_apply i).comp measurable_snd)).prodMk
      (measurable_const.mul ((measurable_pi_apply i).comp measurable_fst)))

theorem memLp_samplingError_comp {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {m : ℕ} (hm : 200 ≤ m)
    (powers : Finset ℕ) (endpoint : Bool) (p : ℝ≥0∞)
    {F : X → (Fin m → ℝ) × UnitAddTorus (Fin m)} (hF : Measurable F) :
    MemLp (fun x => average m powers endpoint (F x).1 (F x).2 - 1) p μ := by
  apply MemLp.of_bound
    (((measurable_average m powers endpoint).comp hF).sub_const 1).aestronglyMeasurable
    (((m : ℝ) ^ (13 / 5 : ℝ)) ^ m + 1)
  apply Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs]
  calc
    _ ≤ |average m powers endpoint (F x).1 (F x).2| + |(1 : ℝ)| := abs_sub _ _
    _ = average m powers endpoint (F x).1 (F x).2 + 1 := by
      rw [abs_of_nonneg (average_nonneg hm powers endpoint _ _), abs_one]
    _ ≤ _ := add_le_add (average_le_height hm powers endpoint _ _) le_rfl

theorem tendsto_eLpNorm_samplingError {m : ℕ} (hm : 200 ≤ m)
    (powers : Finset ℕ) (endpoint : Bool)
    (q : ℕ → ℕ → ℕ) (hq : ∀ j i, 0 < q j i) (hmono : ∀ j, Monotone (q j))
    (hgap : ∀ i, i + 1 < m → Tendsto
      (fun j => (q j (i + 1) : ℝ) / (q j i : ℝ)) atTop atTop)
    {phase : ℕ → Fin m → ℝ} {target : Fin m → ℝ}
    (hphase : Tendsto phase atTop (𝓝 target))
    (hcut : ∀ n ∈ powers, ∀ i, Int.fract ((n : ℝ) * target i) ≠ 0) :
    Tendsto (fun j => eLpNorm (fun x : UnitAddCircle =>
      average m powers endpoint (phase j)
        (fun i : Fin m => (q j i.val : ℤ) • x) - 1) 2 volume) atTop
      (𝓝 (eLpNorm (fun y : UnitAddTorus (Fin m) =>
        average m powers endpoint target y - 1) 2 volume)) := by
  apply SquaredIntegralLp.tendsto_eLpNorm_two_of_integral_sq
  · intro index
    have continuousPair : Continuous (fun x : UnitAddCircle =>
        (phase index, fun i : Fin m => (q index i.val : ℤ) • x)) :=
      continuous_const.prodMk (continuous_pi fun i => continuous_const_smul _)
    exact (((measurable_average m powers endpoint).comp
      continuousPair.measurable).sub_const 1).aestronglyMeasurable
  · exact (((measurable_average m powers endpoint).comp
      (measurable_const.prodMk measurable_id)).sub_const 1).aestronglyMeasurable
  · intro j
    have hc : Continuous (fun x : UnitAddCircle =>
        (phase j, fun i : Fin m => (q j i.val : ℤ) • x)) :=
      continuous_const.prodMk (continuous_pi fun i => continuous_const_smul _)
    exact integrable_squaredError_comp (μ := volume) hm powers endpoint
      (F := fun x : UnitAddCircle =>
        (phase j, fun i : Fin m => (q j i.val : ℤ) • x)) hc.measurable
  · exact integrable_squaredError_comp (μ := volume) hm powers endpoint
      (F := fun y : UnitAddTorus (Fin m) => (target, y))
      (measurable_const.prodMk measurable_id)
  · exact tendsto_integral_squaredError hm powers endpoint q hq hmono hgap hphase hcut

theorem eventually_eLpNorm_samplingError_lt {m : ℕ} (hm : 200 ≤ m)
    (powers : Finset ℕ) (endpoint : Bool)
    (q : ℕ → ℕ → ℕ) (hq : ∀ j i, 0 < q j i) (hmono : ∀ j, Monotone (q j))
    (hgap : ∀ i, i + 1 < m → Tendsto
      (fun j => (q j (i + 1) : ℝ) / (q j i : ℝ)) atTop atTop)
    {phase : ℕ → Fin m → ℝ} {target : Fin m → ℝ}
    (hphase : Tendsto phase atTop (𝓝 target))
    (hcut : ∀ n ∈ powers, ∀ i, Int.fract ((n : ℝ) * target i) ≠ 0)
    {δ : ℝ} (hδ : eLpNorm (fun y : UnitAddTorus (Fin m) =>
      average m powers endpoint target y - 1) 2 volume < ENNReal.ofReal δ) :
    ∀ᶠ j in atTop, eLpNorm (fun x : UnitAddCircle =>
      average m powers endpoint (phase j)
        (fun i : Fin m => (q j i.val : ℤ) • x) - 1) 2 volume < ENNReal.ofReal δ :=
  (tendsto_eLpNorm_samplingError hm powers endpoint q hq hmono hgap hphase hcut).eventually_lt_const hδ

end Invariant233.CharacterSampling

end

end OAI
