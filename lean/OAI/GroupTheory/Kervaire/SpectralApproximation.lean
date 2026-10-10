import OAI.GroupTheory.Kervaire.TraceCalculus

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology

namespace KervaireSpectral
open KervaireTraceCalculus KervaireScalarPhase
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The Mercator logarithm is continuous on the unitary spectrum. -/
def spectralLog (U : Operator H) (hU : U ∈ unitary (Operator H)) (a : ℂ)
    (ha : ‖a‖ < 1) : C(spectrum ℂ U, ℂ) :=
  ⟨fun z => -Complex.log (1 - a * z), by
    apply Continuous.neg
    apply Continuous.clog
    · fun_prop
    · intro z
      apply Complex.mem_slitPlane_iff.mpr
      exact Or.inl (re_one_sub_mul_pos ha
        (CStarRing.norm_of_mem_unitary
          (spectrum_subset_unitary_of_mem_unitary hU z.property)).le)⟩

/-- Uniform absolute convergence of the Mercator expansion in continuous calculus. -/
theorem hasSum_spectralLog (U : Operator H) (hU : U ∈ unitary (Operator H))
    {a : ℂ} (ha : ‖a‖ < 1) :
    HasSum (fun n : ℕ => (a ^ (n+1) / (n+1)) •
      ((ContinuousMap.id ℂ).restrict (spectrum ℂ U)) ^ (n+1)) (spectralLog U hU a ha) := by
  let Z : C(spectrum ℂ U, ℂ) := (ContinuousMap.id ℂ).restrict (spectrum ℂ U)
  have hZ : ‖Z‖ ≤ 1 := by
    apply (Z.norm_le zero_le_one).mpr
    intro z
    exact (CStarRing.norm_of_mem_unitary
      (spectrum_subset_unitary_of_mem_unitary hU z.property)).le
  have hs : Summable (fun n : ℕ => (a ^ (n+1) / (n+1)) • Z ^ (n+1)) := by
    apply Summable.of_norm_bounded
      ((summable_geometric_of_lt_one (norm_nonneg a) ha).comp_injective
        (fun i j h => Nat.add_right_cancel h))
    intro n
    rw [norm_smul]
    calc
      ‖a ^ (n+1) / (n+1)‖ * ‖Z ^ (n+1)‖ ≤ ‖a‖ ^ (n+1) * 1 :=
        mul_le_mul (norm_log_coeff_le a n)
          ((norm_pow_le' Z (Nat.succ_pos n)).trans
            (by simpa using pow_le_pow_left₀ (norm_nonneg Z) hZ (n+1)))
          (norm_nonneg _) (by positivity)
      _ = ‖a‖ ^ (n+1) := mul_one _
  have he : (∑' n : ℕ, (a ^ (n+1) / (n+1)) • Z ^ (n+1)) = spectralLog U hU a ha := by
    ext z
    have h := (ContinuousMap.evalCLM ℂ z).map_tsum hs
    rw [ContinuousMap.evalCLM_apply] at h
    rw [h]
    have haz : ‖a * (z : ℂ)‖ < 1 := by
      rw [norm_mul, CStarRing.norm_of_mem_unitary
        (spectrum_subset_unitary_of_mem_unitary hU z.property), mul_one]
      exact ha
    change (∑' n : ℕ, (a ^ (n+1) / (n+1)) * (z : ℂ) ^ (n+1)) =
      -Complex.log (1 - a * z)
    convert (Complex.hasSum_taylorSeries_neg_log' haz).tsum_eq using 1
    apply tsum_congr
    intro n
    rw [mul_pow, div_mul_eq_mul_div]
  exact he ▸ hs.hasSum

/-- Applying any continuous functional to the convergent spectral logarithm
 commutes with its Mercator expansion. -/
theorem traceLog_eq_calculus (U : Operator H) (hU : U ∈ unitary (Operator H))
    (τ : Operator H →L[ℂ] ℂ) {a : ℂ} (ha : ‖a‖ < 1) :
    let hN := isStarNormal_of_mem_unitary hU
    traceLog τ a U = τ (cfcHom hN (spectralLog U hU a ha)) := by
  let hN := isStarNormal_of_mem_unitary hU
  have hc := (hasSum_spectralLog U hU ha).map (cfcHom hN) (cfcHom_continuous hN)
  have ht := hc.map τ τ.continuous
  apply HasSum.tsum_eq
  convert ht using 1
  ext n
  simp [map_smul, map_pow, cfcHom_id]

/-- The regularized scalar phase is continuous on the unitary spectrum. -/
def spectralSmooth (U : Operator H) (hU : U ∈ unitary (Operator H))
    (a : ℂ) (ha : ‖a‖ < 1) : C(spectrum ℂ U, ℝ) :=
  ⟨fun z => smoothPhase a z, by
    have hc : Continuous (fun z : spectrum ℂ U =>
        1 / 2 - (spectralLog U hU a ha z).im / Real.pi) := by
      exact continuous_const.sub
        ((Complex.continuous_im.comp (spectralLog U hU a ha).continuous).div_const _)
    simpa [spectralLog, smoothPhase, Complex.log_im, sub_eq_add_neg, neg_div]
      using hc⟩

@[simp] theorem complexify_one {X : Type*} [TopologicalSpace X] :
    complexify (1 : C(X, ℝ)) = 1 := by ext; simp [complexify]

/-- The mass of a vector spectral measure is its value at the identity. -/
theorem integral_one_vectorMeasure (U : Operator H) [IsStarNormal U] (ξ : H) :
    ∫ _z : spectrum ℂ U, (1 : ℝ) ∂vectorMeasure U ξ = (vectorCLM ξ 1).re := by
  simpa using integral_vectorMeasure U ξ (1 : C(spectrum ℂ U, ℝ))

/-- Continuous-calculus and scalar-measure versions of the regularization agree. -/
theorem smoothTrace_vectorCLM (U : Operator H) (hU : U ∈ unitary (Operator H))
    (ξ : H) {a : ℂ} (ha : ‖a‖ < 1) :
    let _ := isStarNormal_of_mem_unitary hU
    smoothTrace (vectorCLM ξ) a U =
      ∫ z : spectrum ℂ U, smoothPhase a z ∂vectorMeasure U ξ := by
  let hN := isStarNormal_of_mem_unitary hU
  have hi := integrable_continuous_map U ξ (spectralLog U hU a ha)
  have he : (fun z : spectrum ℂ U => smoothPhase a z) =
      (fun z => 1 / 2 - (spectralLog U hU a ha z).im / Real.pi) := by
    funext z
    simp [spectralLog, smoothPhase, Complex.log_im, sub_eq_add_neg, neg_div]
  have him : Integrable (fun z => (spectralLog U hU a ha z).im) (vectorMeasure U ξ) :=
    Complex.imCLM.integrable_comp hi
  have hhalf : (∫ _z : spectrum ℂ U, (1 / 2 : ℝ) ∂vectorMeasure U ξ) =
      (vectorCLM ξ 1).re / 2 := by
    rw [integral_div, integral_one_vectorMeasure]
  change smoothTrace (vectorCLM ξ) a U = _
  rw [he, integral_sub (integrable_const _) (him.div_const _), hhalf, integral_div]
  have himint := Complex.imCLM.integral_comp_comm hi
  change (∫ z, (spectralLog U hU a ha z).im ∂vectorMeasure U ξ) = _ at himint
  rw [himint, integral_vectorMeasure_complex]
  exact congrArg (fun z : ℂ => (vectorCLM ξ 1).re / 2 - z.im / Real.pi)
    (traceLog_eq_calculus U hU (vectorCLM ξ) ha)

/-- Dominated convergence reaches the exact value zero at the phase cut. -/
theorem tendsto_smoothTrace_vectorCLM (U : Operator H) (hU : U ∈ unitary (Operator H))
    (ξ : H) :
    let _ := isStarNormal_of_mem_unitary hU
    Tendsto (fun n => smoothTrace (vectorCLM ξ) (cutApproach (cutTime n)) U)
      atTop (𝓝 (vectorPhase U ξ)) := by
  let hN := isStarNormal_of_mem_unitary hU
  have he (n : ℕ) := smoothTrace_vectorCLM U hU ξ (norm_cutApproach_cutTime_lt_one n)
  simp_rw [he]
  apply tendsto_integral_of_dominated_convergence (fun _ => 1)
  · intro n
    exact (spectralSmooth U hU _ (norm_cutApproach_cutTime_lt_one n)).continuous.aestronglyMeasurable
  · exact integrable_const _
  · intro n
    apply Filter.Eventually.of_forall
    intro z
    have hz := CStarRing.norm_of_mem_unitary
      (spectrum_subset_unitary_of_mem_unitary hU z.property)
    rw [Real.norm_eq_abs, abs_of_nonneg
      ((smoothPhase_mem_Icc (norm_cutApproach_cutTime_lt_one n) hz.le).1)]
    exact (smoothPhase_mem_Icc (norm_cutApproach_cutTime_lt_one n) hz.le).2
  · apply Filter.Eventually.of_forall
    intro z
    exact tendsto_smoothPhase_cutTime (CStarRing.norm_of_mem_unitary
      (spectrum_subset_unitary_of_mem_unitary hU z.property))

end KervaireSpectral

end

end OAI
