import OAI.Analysis.IrrationalRotation.Sampling.CharacterSamplingLp
import OAI.Analysis.IrrationalRotation.Sampling.CharacterSamplingRealization

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace Invariant233.CharacterSampling

local instance characterSamplingLpRealizationCircleProbability :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨by simp [AddCircle.measure_univ]⟩

theorem exists_realized_sampling_block_L2 {θ : ℝ} (hθ : Irrational θ)
    {m : ℕ} (hm : 200 ≤ m) (target : Fin m → ℝ)
    (htarget0 : ∀ i, 0 < target i) (htarget1 : ∀ i, target i < 1)
    {q₀ : ℕ} (hq₀ : 0 < q₀) (R : ℝ)
    (U : Set (Fin m → ℝ)) (hU : U ∈ 𝓝 target)
    (r : ℕ) (powers : Fin r → Finset ℕ) (δ : Fin r → Bool → ℝ)
    (hδ : ∀ k endpoint, 0 < δ k endpoint)
    (hcut : ∀ k, ∀ n ∈ powers k, ∀ i, Int.fract ((n : ℝ) * target i) ≠ 0)
    (hbound : ∀ k endpoint,
      eLpNorm (fun y : UnitAddTorus (Fin m) =>
        average m (powers k) endpoint target y - 1) 2 volume < ENNReal.ofReal (δ k endpoint)) :
    ∃ q : ℕ → ℕ,
      q 0 = q₀ ∧ (∀ i, 0 < q i) ∧ StrictMono q ∧
      (∀ i, q i ∣ q (i + 1)) ∧
      (∀ i < m, R ≤ (q (i + 1) : ℝ) / (q i : ℝ)) ∧
      (fun i : Fin m => Int.fract ((q (i.val + 1) : ℝ) * θ)) ∈ U ∧
      ∀ k endpoint,
        eLpNorm (fun x : UnitAddCircle => average m (powers k) endpoint
          (fun i : Fin m => Int.fract ((q (i.val + 1) : ℝ) * θ))
          (fun i : Fin m => (q (i.val + 1) : ℤ) • x) - 1) 2 volume <
            ENNReal.ofReal (δ k endpoint) := by
  have hsq : ∀ k endpoint,
      (∫ y : UnitAddTorus (Fin m), squaredError m (powers k) endpoint (target, y)) <
        (δ k endpoint) ^ 2 := by
    intro k endpoint
    have hint := integrable_squaredError_comp (μ := volume) hm (powers k) endpoint
      (F := fun y : UnitAddTorus (Fin m) => (target, y))
      (measurable_const.prodMk measurable_id)
    exact (SquaredIntegralLp.eLpNorm_two_lt_ofReal_iff_integral_sq_lt volume
      (fun y : UnitAddTorus (Fin m) => average m (powers k) endpoint target y - 1)
      (((measurable_average m (powers k) endpoint).comp
        (measurable_const.prodMk measurable_id)).sub_const 1).aestronglyMeasurable
      hint (hδ k endpoint)).mp (hbound k endpoint)
  obtain ⟨q, hzero, hpos, hstrict, hdiv, hratio, hUq, hsqQ⟩ :=
    exists_realized_sampling_block hθ hm target htarget0 htarget1 hq₀ R U hU
      r powers (fun k endpoint => (δ k endpoint) ^ 2) hcut hsq
  refine ⟨q, hzero, hpos, hstrict, hdiv, hratio, hUq, ?_⟩
  intro k endpoint
  have hc : Continuous (fun x : UnitAddCircle =>
      ((fun i : Fin m => Int.fract ((q (i.val + 1) : ℝ) * θ)),
        fun i : Fin m => (q (i.val + 1) : ℤ) • x)) :=
    continuous_const.prodMk (continuous_pi fun i => continuous_zsmul _)
  have hint := integrable_squaredError_comp (μ := volume) hm (powers k) endpoint
    (F := fun x : UnitAddCircle =>
      ((fun i : Fin m => Int.fract ((q (i.val + 1) : ℝ) * θ)),
        fun i : Fin m => (q (i.val + 1) : ℤ) • x)) hc.measurable
  exact (SquaredIntegralLp.eLpNorm_two_lt_ofReal_iff_integral_sq_lt volume
    (fun x : UnitAddCircle => average m (powers k) endpoint
      (fun i : Fin m => Int.fract ((q (i.val + 1) : ℝ) * θ))
      (fun i : Fin m => (q (i.val + 1) : ℤ) • x) - 1)
    (((measurable_average m (powers k) endpoint).comp
      hc.measurable).sub_const 1).aestronglyMeasurable
    hint (hδ k endpoint)).mpr (hsqQ k endpoint)

end Invariant233.CharacterSampling

end

end OAI
