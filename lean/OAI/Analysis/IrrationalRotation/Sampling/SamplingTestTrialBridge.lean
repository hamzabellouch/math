import OAI.Analysis.IrrationalRotation.Sampling.SamplingTestLimit
import OAI.Analysis.IrrationalRotation.Sampling.TrialSamplingSelection

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Invariant233.SamplingTests

@[simp] lemma average_eq_trialAverage (endpoint : Bool) (m : ℕ) (s : Finset ℕ)
    (τ : Fin m → ℝ) (y : UnitAddTorus (Fin m)) :
    average endpoint m m s (τ,y) = TrialSampling.average m s endpoint τ y := rfl

@[simp] lemma spatialLaw_eq_volume (m : ℕ) :
    TrialSampling.spatialLaw m = (volume : Measure (UnitAddTorus (Fin m))) := rfl

lemma squaredError_eq_lintegral (endpoint : Bool) (m : ℕ) (s : Finset ℕ)
    (τ : Fin m → ℝ) :
    TrialSampling.squaredError m s endpoint τ =
      ∫⁻ y : UnitAddTorus (Fin m), ENNReal.ofReal (errorSq endpoint m m s (τ,y)) := rfl

lemma integrable_errorSq_comp {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (endpoint : Bool) {m : ℕ} (hm : 0 < m)
    (d : ℕ) (s : Finset ℕ) (a : X → (Fin d → ℝ) × UnitAddTorus (Fin d))
    (ha : Measurable a) : Integrable (fun x => errorSq endpoint m d s (a x)) μ := by
  apply Integrable.of_bound ((measurable_errorSq endpoint m d s).comp ha).aestronglyMeasurable
    ((((m : ℝ)^2 / CircleParameterData.kernelWidth m) ^ d + 1) ^ 2)
  exact Filter.Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs, Function.comp_apply] using (errorSq_bounds endpoint hm d s (a x)).2

lemma squaredError_eq_ofReal_integral (endpoint : Bool) {m : ℕ} (hm : 0 < m)
    (s : Finset ℕ) (τ : Fin m → ℝ) :
    TrialSampling.squaredError m s endpoint τ =
      ENNReal.ofReal (∫ y : UnitAddTorus (Fin m), errorSq endpoint m m s (τ,y)) := by
  let : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin m))) :=
    (CharacterLaws.torusHaar m).property
  rw [squaredError_eq_lintegral]
  symm
  exact ofReal_integral_eq_lintegral_ofReal
    (integrable_errorSq_comp volume endpoint hm m s (fun y => (τ,y))
      (measurable_const.prodMk measurable_id))
    (Filter.Eventually.of_forall fun y => (errorSq_bounds endpoint hm m s (τ,y)).1)

lemma eLpNorm_error_sq_eq_ofReal_integral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (endpoint : Bool) {m : ℕ} (hm : 0 < m)
    (d : ℕ) (s : Finset ℕ) (a : X → (Fin d → ℝ) × UnitAddTorus (Fin d))
    (ha : Measurable a) :
    eLpNorm (fun x => average endpoint m d s (a x) - 1) 2 μ ^ 2 =
      ENNReal.ofReal (∫ x, errorSq endpoint m d s (a x) ∂μ) := by
  have h := eLpNorm_nnreal_pow_eq_lintegral
    (f := fun x => average endpoint m d s (a x) - 1) (μ := μ)
    (p := (2 : NNReal)) (by norm_num)
    (((measurable_average endpoint m d s).comp ha).sub measurable_const).aestronglyMeasurable
  norm_num only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_two] at h
  rw [h, ofReal_integral_eq_lintegral_ofReal
    (integrable_errorSq_comp μ endpoint hm d s a ha)
    (Filter.Eventually.of_forall fun x => (errorSq_bounds endpoint hm d s (a x)).1)]
  apply lintegral_congr
  intro x
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  rfl

lemma eLpNorm_error_lt_iff_integral_lt {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (endpoint : Bool) {m : ℕ} (hm : 0 < m)
    (d : ℕ) (s : Finset ℕ) (a : X → (Fin d → ℝ) × UnitAddTorus (Fin d))
    (ha : Measurable a) {r : ℝ} (hr : 0 < r) :
    eLpNorm (fun x => average endpoint m d s (a x) - 1) 2 μ < ENNReal.ofReal r ↔
      (∫ x, errorSq endpoint m d s (a x) ∂μ) < r ^ 2 := by
  have hpow := ENNReal.rpow_lt_rpow_iff
    (x := eLpNorm (fun x => average endpoint m d s (a x) - 1) 2 μ)
    (y := ENNReal.ofReal r) (z := (2 : ℝ)) (by norm_num)
  rw [ENNReal.rpow_two, ENNReal.rpow_two,
    eLpNorm_error_sq_eq_ofReal_integral μ endpoint hm d s a ha,
    ← ENNReal.ofReal_pow hr.le] at hpow
  rw [ENNReal.ofReal_lt_ofReal_iff (sq_pos_of_pos hr)] at hpow
  exact hpow.symm

theorem exists_character_sampling_block_L2 {ι : Type*} [Finite ι]
    {θ : ℝ} (hθ : Irrational θ) {m : ℕ} (hm : 200 ≤ m)
    (s : ι → Finset ℕ) (τ : Fin m → ℝ) (hτ : ∀ i, 0 < τ i ∧ τ i < 1)
    (hphase : ∀ r, ∀ n ∈ s r, ∀ i, Int.fract ((n : ℝ) * τ i) ≠ 0)
    (ρ : ι → Bool → ℝ) (hρ : ∀ r endpoint, 0 < ρ r endpoint)
    (htests : ∀ r endpoint, TrialSampling.squaredError m (s r) endpoint τ <
      ENNReal.ofReal ((ρ r endpoint) ^ 2))
    (U : Set (Fin m → ℝ)) (hU : U ∈ 𝓝 τ) (R : ℝ)
    {q₀ : ℕ} (hq₀ : 0 < q₀) :
    ∃ q : ℕ → ℕ, q 0 = q₀ ∧ (∀ i, 0 < q i) ∧ StrictMono q ∧
      (∀ i, q i ∣ q (i + 1)) ∧
      (∀ i < m, R ≤ (q (i + 1) : ℝ) / q i) ∧
      (fun i : Fin m => Int.fract ((q (i.val + 1) : ℝ) * θ)) ∈ U ∧
      ∀ r endpoint, eLpNorm (fun x : Circle =>
        TrialSampling.average m (s r) endpoint
          (fun i : Fin m => Int.fract ((q (i.val + 1) : ℝ) * θ))
          (fun i : Fin m => (q (i.val + 1) : ℤ) • x) - 1) 2 circleMeasure <
            ENNReal.ofReal (ρ r endpoint) := by
  have hreal (r : ι) (endpoint : Bool) :
      (∫ y : UnitAddTorus (Fin m), errorSq endpoint m m (s r) (τ,y)) <
        (ρ r endpoint)^2 := by
    have h := htests r endpoint
    rw [squaredError_eq_ofReal_integral endpoint (by omega)] at h
    exact (ENNReal.ofReal_lt_ofReal_iff (sq_pos_of_pos (hρ r endpoint))).mp h
  obtain ⟨q, hzero, hpos, hstrict, hdiv, hgap, hUq, hsq⟩ :=
    exists_character_sampling_block hθ hm m s τ hτ hphase
      (fun r e => (ρ r e)^2) hreal U hU R hq₀
  refine ⟨q, hzero, hpos, hstrict, hdiv, hgap, hUq, ?_⟩
  intro r endpoint
  have hmap : Measurable (fun x : Circle =>
      ((fun i : Fin m => Int.fract ((q (i.val + 1) : ℝ) * θ)),
       (fun i : Fin m => (q (i.val + 1) : ℤ) • x))) := by fun_prop
  exact (eLpNorm_error_lt_iff_integral_lt volume endpoint (by omega) m (s r)
    _ hmap (hρ r endpoint)).mpr (hsq r endpoint)

end Invariant233.SamplingTests

end

end OAI
