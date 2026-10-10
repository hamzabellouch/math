import OAI.Analysis.IrrationalRotation.Couplings.CircleCouplingLaw
import OAI.Analysis.IrrationalRotation.Sampling.MixedRadixNonterminal

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData OneCoordinateCoupling

lemma initial_digit_singleton {p : CircleParameterData}
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) (i : ℕ)
    (d : Fin (MixedRadix.radices p.q i)) :
    (initialLaw.map (observedDigit p hr side i)) {d} =
      (MixedRadix.radices p.q i : ℝ≥0∞)⁻¹ := by
  let : NeZero (MixedRadix.radices p.q i) := ⟨Nat.ne_of_gt (hr i)⟩
  rw [initialLaw, Measure.map_map (measurable_observedDigit hr side i)
    (show Measurable (fun x : ℝ => ((none : Label), (x, x))) from by fun_prop)]
  cases side <;>
    change (baseLaw.map (UniformQuantization.quantize _)) {d} = _
  all_goals rw [baseLaw_eq_restrict]; exact UniformQuantization.map_quantize_singleton _ d

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

lemma observed_singleton_le_half (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) (i : ℕ)
    (d : Fin (MixedRadix.radices p.q i)) :
    ((coordinateLaw p j i).map (observedDigit p hr side i)) {d} ≤ (2 : ℝ≥0∞)⁻¹ := by
  let : NeZero (MixedRadix.radices p.q i) := ⟨Nat.ne_of_gt (hr i)⟩
  by_cases hi : i = 0
  · rw [coordinateLaw, ite_eq_left hi, initial_digit_singleton]
    exact ENNReal.inv_le_inv.mpr (by exact_mod_cast
      (MixedRadix.radices_ge_two hp.q_pos hp.frequency_increasing hp.frequency_divisible i))
  obtain ⟨s, hs, his⟩ := p.exists_mem_block hp.m_pos i (by omega)
  have hidx := p.blockIndex_eq_of_mem hp.m_pos his
  have hm : (100 : ℝ) ≤ p.m s := by exact_mod_cast (show 100 ≤ p.m s by have := hp.m_ge_200 s hs; omega)
  have ha := hp.coupling_a_bounds s hs
  have hb := hp.coupling_b_bounds s hs
  have hκ := CircleParameterLaws.coupling_kappa_bounds s hs
  have ht := tag_bounds j s
  have h20 : (20 : ℝ) ≤ MixedRadix.radices p.q i := by
    have hN := hp.coupling_radix_ge_N hs his
    have hK : (100 : ℝ) ≤ p.K s := by exact_mod_cast hp.coupling_K_ge s hs
    dsimp [N] at hN
    nlinarith
  rw [coordinateLaw, ite_eq_right hi, hidx]
  have hfst := Measure.fst_map_prodMk (μ := rawLaw (kappa s) (p.m s) (p.a s) (p.b s) (tag j s))
    (X := observedDigit p hr side i) (measurable_observedDigit hr side i) measurable_fst
  rw [← hfst]
  change (digitJoint side (MixedRadix.radices p.q i) (kappa s) (p.m s) (p.a s) (p.b s) (tag j s)).fst {d} ≤ _
  rw [digitJoint_fst_singleton hm ha.1 ha.2 hb.1 hb.2]
  calc
    _ ≤ 10 * baseLaw (bin _ d) := digitWeight_total_le_ten hκ.1 hκ.2 hm ha.1 ha.2 hb.1 hb.2 ht.1 ht.2 side _ d
    _ = 10 * (MixedRadix.radices p.q i : ℝ≥0∞)⁻¹ := by rw [baseLaw_bin]
    _ ≤ 10 * (20 : ℝ≥0∞)⁻¹ := mul_le_mul_right (ENNReal.inv_le_inv.mpr (by exact_mod_cast h20)) 10
    _ = _ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num

lemma ae_nonterminal_digits (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) :
    ∀ᵐ ω ∂law p j, MixedRadix.Nonterminal (digits p hr side ω) := by
  let := coordinateLaw_isProbabilityMeasure hp j
  let s : ℕ → Set CoordinateSample := fun i =>
    {z | ¬(observedDigit p hr side i z : ℕ) + 1 < MixedRadix.radices p.q i}
  have heq (i : ℕ) : s i = observedDigit p hr side i ⁻¹'
      {⟨MixedRadix.radices p.q i - 1, by have := hr i; omega⟩} := by
    ext z
    simp only [s, mem_ofPred_eq, mem_preimage, mem_singleton_iff, Fin.ext_iff]
    have := (observedDigit p hr side i z).isLt
    omega
  have hs (i : ℕ) : MeasurableSet (s i) := by
    rw [heq]
    exact (measurable_observedDigit hr side i) (measurableSet_singleton _)
  have hprob (i : ℕ) : coordinateLaw p j i (s i) ≤ (2 : ℝ≥0∞)⁻¹ := by
    rw [heq, ← Measure.map_apply (measurable_observedDigit hr side i) (measurableSet_singleton _)]
    exact observed_singleton_le_half hp j hr side i _
  have hnull := infinitePi_eventually_mem_null (coordinateLaw p j) s hs
    (by norm_num : (2 : ℝ≥0∞)⁻¹ < 1) hprob
  rw [ae_iff]
  simpa only [law, MixedRadix.Nonterminal, digits, mem_ofPred_eq,
    not_forall, not_exists, not_and, s] using hnull

end Invariant233.CircleCoupling

end

end OAI
