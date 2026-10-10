import OAI.Analysis.IrrationalRotation.Model.MixedRadixProbability
import OAI.Analysis.IrrationalRotation.Sampling.MixedRadix
import OAI.Analysis.IrrationalRotation.Sampling.FinitePrefixLaw
import OAI.Analysis.IrrationalRotation.Analysis.UniformQuantization
import OAI.Analysis.IrrationalRotation.Analysis.LimitLaw

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal BigOperators Classical

namespace Invariant233.MixedRadix

instance digitLaw_isProbability (r : ℕ → ℕ) (hr : ∀ n, 0 < r n) :
    IsProbabilityMeasure (digitLaw r hr) := by
  unfold digitLaw
  infer_instance

theorem measurable_prefix_sum (r : ℕ → ℕ) (N : ℕ) :
    Measurable (fun d : Digits r => ∑ n ∈ Finset.range N, term d n) := by
  apply Finset.measurable_sum
  intro n hn
  exact ((measurable_of_finite (fun a : Fin (r n) => (a : ℝ))).comp
    (measurable_pi_apply n)).div_const _

theorem tendsto_prefix_sum {r : ℕ → ℕ} (hr : ∀ n, 0 < r n) (d : Digits r) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, term d n) atTop (𝓝 (ofDigits d)) :=
  (summable_terms hr d).hasSum.tendsto_sum_nat

theorem tendsto_quantized_prefix {r : ℕ → ℕ} (hr : ∀ n, 2 ≤ r n) {x : ℝ}
    (hx : x ∈ Ico (0 : ℝ) 1) :
    Tendsto (fun N => (⌊(denominator r N : ℝ) * x⌋₊ : ℝ) /
      (denominator r N : ℝ)) atTop (𝓝 x) := by
  let hp : ∀ n, 0 < r n := fun n => lt_of_lt_of_le (by decide : 0 < 2) (hr n)
  have heq : (fun N => (⌊(denominator r N : ℝ) * x⌋₊ : ℝ) /
      (denominator r N : ℝ)) =
      (fun N => ∑ n ∈ Finset.range N, term (canonicalDigits r hp x) n) := by
    funext N
    have hq : (denominator r N : ℝ) ≠ 0 :=
      ne_of_gt (by exact_mod_cast denominator_pos hp N)
    have h := denominator_mul_prefix hp (canonicalDigits r hp x) N
    rw [prefixRank_canonicalDigits hp hx N] at h
    exact (eq_div_iff hq).mpr (by simpa [mul_comm] using h) |>.symm
  rw [heq]
  have hrec : ofDigits (canonicalDigits r hp x) = x := ofDigits_canonicalDigits hr hx
  simpa only [hrec] using tendsto_prefix_sum hp (canonicalDigits r hp x)

theorem map_prefixRank_uniform (r : ℕ → ℕ) (hr : ∀ n, 0 < r n) (N : ℕ) [NeZero (denominator r N)] :
    (digitLaw r hr).map
      (fun d => finitePrefixRankEquiv r hr N (fun i : Fin N => d i)) =
      (PMF.uniformOfFintype (Fin (denominator r N))).toMeasure := by
  let : ∀ n, NeZero (r n) := fun n => ⟨ne_of_gt (hr n)⟩
  let : NeZero (denominator r N) := ⟨ne_of_gt (denominator_pos hr N)⟩
  let E := finitePrefixRankEquiv r hr N
  have hp : (digitLaw r hr).map (fun d (i : Fin N) => d i) =
      (PMF.uniformOfFintype ((i : Fin N) → Fin (r i))).toMeasure := by
    unfold digitLaw
    exact FiniteUniformLaw.infinitePi_fin_uniform (fun n => Fin (r n)) N
  have hm : Measurable (fun d : Digits r => fun i : Fin N => d i) :=
    Measurable.of_eval (fun index => measurable_pi_apply (index : ℕ))
  change (digitLaw r hr).map (E ∘ (fun d (i : Fin N) => d i)) = _
  rw [← Measure.map_map (measurable_of_finite E) hm, hp]
  exact FiniteUniformLaw.map_equiv E

theorem prefix_sum_eq_normalized_rank (r : ℕ → ℕ) (hr : ∀ n, 0 < r n)
    (N : ℕ) (d : Digits r) :
    (∑ n ∈ Finset.range N, term d n) =
      ((finitePrefixRankEquiv r hr N (fun i : Fin N => d i) : ℕ) : ℝ) /
        (denominator r N : ℝ) := by
  rw [finitePrefixRankEquiv_val]
  have heq : prefixRank (extendPrefix r hr N (fun i : Fin N => d i)) N =
      prefixRank d N := by
    apply prefixRank_congr
    intro n hn
    simp [hn]
  rw [heq]
  have hq : (denominator r N : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast denominator_pos hr N)
  exact (eq_div_iff hq).mpr (by simpa [mul_comm] using denominator_mul_prefix hr d N)

theorem map_prefix_sum_eq_quantized (r : ℕ → ℕ) (hr : ∀ n, 0 < r n) (N : ℕ) :
    (digitLaw r hr).map (fun d => ∑ n ∈ Finset.range N, term d n) =
      (volume.restrict (Ico (0 : ℝ) 1)).map
        (fun x => (⌊(denominator r N : ℝ) * x⌋₊ : ℝ) / (denominator r N : ℝ)) := by
  let : ∀ n, NeZero (r n) := fun n => ⟨ne_of_gt (hr n)⟩
  let : NeZero (denominator r N) := ⟨ne_of_gt (denominator_pos hr N)⟩
  let R : Digits r → Fin (denominator r N) :=
    fun d => finitePrefixRankEquiv r hr N (fun i : Fin N => d i)
  let g : Fin (denominator r N) → ℝ := fun a => (a : ℝ) / (denominator r N : ℝ)
  have hR : Measurable R := (measurable_of_finite (finitePrefixRankEquiv r hr N)).comp
    (Measurable.of_eval (fun index : Fin N => measurable_pi_apply (index : ℕ)))
  have hg : Measurable g := measurable_of_finite _
  have heq : (fun d => ∑ n ∈ Finset.range N, term d n) = g ∘ R := by
    funext d
    exact prefix_sum_eq_normalized_rank r hr N d
  rw [heq, ← Measure.map_map hg hR]
  have hRlaw : (digitLaw r hr).map R =
      (PMF.uniformOfFintype (Fin (denominator r N))).toMeasure :=
    map_prefixRank_uniform r hr N
  rw [hRlaw, ← UniformQuantization.map_quantize_uniform (denominator r N),
    Measure.map_map hg (UniformQuantization.measurable_quantize _)]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ico] with x hx
  have hq : (0 : ℝ) < denominator r N := by exact_mod_cast denominator_pos hr N
  have hfloor : ⌊(denominator r N : ℝ) * x⌋₊ < denominator r N :=
    (Nat.floor_lt (mul_nonneg hq.le hx.1)).mpr (by nlinarith [hx.2])
  simp [g, UniformQuantization.quantize, Nat.mod_eq_of_lt hfloor]

theorem map_ofDigits_eq_volume (r : ℕ → ℕ) (hr : ∀ n, 2 ≤ r n) :
    (digitLaw r (fun n => lt_of_lt_of_le (by decide : 0 < 2) (hr n))).map ofDigits =
      volume.restrict (Ico (0 : ℝ) 1) := by
  let hp : ∀ n, 0 < r n := fun n => lt_of_lt_of_le (by decide : 0 < 2) (hr n)
  let μ := digitLaw r hp
  let ν := (volume : Measure ℝ).restrict (Ico (0 : ℝ) 1)
  have : IsProbabilityMeasure ν := ⟨by simp [ν]⟩
  have : IsProbabilityMeasure μ := digitLaw_isProbability r hp
  have hX : ∀ N, AEMeasurable (fun d : Digits r => ∑ n ∈ Finset.range N, term d n) μ :=
    fun N => (measurable_prefix_sum r N).aemeasurable
  have hY : ∀ N, AEMeasurable
      (fun x : ℝ => (⌊(denominator r N : ℝ) * x⌋₊ : ℝ) / (denominator r N : ℝ)) ν := by
    intro N
    exact (((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      (measurable_const.mul measurable_id).nat_floor).div_const _).aemeasurable
  have hZ : AEMeasurable (ofDigits : Digits r → ℝ) μ :=
    (continuous_ofDigits hr).measurable.aemeasurable
  have hW : AEMeasurable (id : ℝ → ℝ) ν := measurable_id.aemeasurable
  have hXZ : ∀ᵐ d ∂μ, Tendsto (fun N => ∑ n ∈ Finset.range N, term d n)
      atTop (𝓝 (ofDigits d)) := Filter.Eventually.of_forall (tendsto_prefix_sum hp)
  have hYW : ∀ᵐ x ∂ν, Tendsto
      (fun N => (⌊(denominator r N : ℝ) * x⌋₊ : ℝ) / (denominator r N : ℝ))
      atTop (𝓝 (id x)) := by
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ico] with x hx
    exact tendsto_quantized_prefix hr hx
  have h := Invariant233.map_eq_of_ae_limits_of_map_eq hX hY hZ hW hXZ hYW
    (map_prefix_sum_eq_quantized r hp)
  simpa only [Measure.map_id] using h

end Invariant233.MixedRadix

end

end OAI
