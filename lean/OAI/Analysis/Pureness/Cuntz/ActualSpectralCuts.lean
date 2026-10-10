import OAI.Analysis.Pureness.Divisibility.CutoffRank
import OAI.Analysis.Pureness.Cuntz.SmoothedIntegerCuts

namespace OAI
namespace CuntzPureness
open Filter Topology
open scoped ComplexOrder CStarAlgebra ENNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

noncomputable def positiveIntegerCut (c : A) (j : ℕ) : A :=
  cfc (fun t : ℝ => max (t - ((j : ℝ) + 1)) 0) c

lemma positiveIntegerCut_nonneg (c : A) (j : ℕ) : 0 ≤ positiveIntegerCut c j :=
  cfc_nonneg (fun _ _ => le_max_right _ _)

lemma positiveIntegerCut_eq_posPart (c : A) (hc : 0 ≤ c) (j : ℕ) :
    positiveIntegerCut c j = (c - (((j : ℝ) + 1) • (1 : A)))⁺ := by
  have heq : cfc (fun t : ℝ => t - ((j : ℝ) + 1)) c = c - (((j : ℝ) + 1) • (1 : A)) := by
    rw [cfc_sub (fun t : ℝ => t) (fun _ => (j : ℝ) + 1) c,
      cfc_id' ℝ c hc.isSelfAdjoint, cfc_const _ c hc.isSelfAdjoint, Algebra.algebraMap_eq_smul_one]
  rw [CFC.posPart_def, cfcₙ_eq_cfc (hf0 := by simp), ← heq]
  rw [← cfc_comp (fun t : ℝ => t⁺) (fun t => t - ((j : ℝ) + 1)) c hc.isSelfAdjoint]
  rfl

lemma spectralApproxUnit_positiveIntegerCut (c : A) (hc : 0 ≤ c) (j n : ℕ) :
    spectralApproxUnit (positiveIntegerCut c j) n =
      cfc (fun t : ℝ => min (((n : ℝ) + 1) * max (t - ((j : ℝ) + 1)) 0) 1) c := by
  unfold spectralApproxUnit positiveIntegerCut
  rw [← cfc_comp _ _ c hc.isSelfAdjoint]
  rfl

lemma smoothedIntegerCut_cfc (c : A) (hc : 0 ≤ c) (l n : ℕ) :
    cfc (smoothedIntegerCutCount l ((n : ℝ) + 1)) c =
      ∑ j ∈ Finset.range l, spectralApproxUnit (positiveIntegerCut c j) n := by
  calc
    _ = ∑ j ∈ Finset.range l,
        cfc (fun t : ℝ => min (((n : ℝ) + 1) * max (t - ((j : ℝ) + 1)) 0) 1) c := by
      have heq : smoothedIntegerCutCount l ((n : ℝ) + 1) =
          ∑ j ∈ Finset.range l, (fun t : ℝ => min (((n : ℝ) + 1) * max (t - ((j : ℝ) + 1)) 0) 1) := by
        funext t
        simp only [smoothedIntegerCutCount, Finset.sum_apply]
      rw [heq]
      exact cfc_sum _ c (Finset.range l)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (spectralApproxUnit_positiveIntegerCut c hc j n).symm

lemma smoothedIntegerCut_operator_bounds (c : A) (hc : 0 ≤ c) (l : ℕ) (hl : ‖c‖ ≤ l) (n : ℕ) :
    (∑ j ∈ Finset.range l, spectralApproxUnit (positiveIntegerCut c j) n) ≤ c ∧
      c ≤ (∑ j ∈ Finset.range l, spectralApproxUnit (positiveIntegerCut c j) n) +
        spectralApproxUnit c n + (1 / ((n : ℝ) + 1)) • (1 : A) := by
  have hs (t : ℝ) (ht : t ∈ spectrum ℝ c) : 0 ≤ t ∧ t ≤ l := by
    refine ⟨spectrum_nonneg_of_nonneg hc ht, ?_⟩
    have hn : ‖t‖ ≤ ‖c‖ := by
      simpa only [cfc_id' ℝ c hc.isSelfAdjoint] using norm_apply_le_norm_cfc (fun t : ℝ => t) c ht
    exact (le_abs_self t).trans (hn.trans hl)
  have hf : Continuous (smoothedIntegerCutCount l ((n : ℝ) + 1)) := by
    unfold smoothedIntegerCutCount
    fun_prop
  constructor
  · calc
      _ = cfc (smoothedIntegerCutCount l ((n : ℝ) + 1)) c := (smoothedIntegerCut_cfc c hc l n).symm
      _ ≤ cfc (fun t : ℝ => t) c := by
        apply cfc_mono (hf := hf.continuousOn) (hg := continuousOn_id)
        intro t ht
        exact sub_nonneg.mp (smoothedIntegerCutCount_bounds l ((n : ℝ) + 1) t (by positivity) (hs t ht).1 (hs t ht).2).1
      _ = c := cfc_id' ℝ c hc.isSelfAdjoint
  · have heq : cfc (fun t => smoothedIntegerCutCount l ((n : ℝ) + 1) t +
          min (((n : ℝ) + 1) * t) 1 + 1 / ((n : ℝ) + 1)) c =
        (∑ j ∈ Finset.range l, spectralApproxUnit (positiveIntegerCut c j) n) +
          spectralApproxUnit c n + (1 / ((n : ℝ) + 1)) • (1 : A) := by
      rw [cfc_add_const (1 / ((n : ℝ) + 1))
        (fun t => smoothedIntegerCutCount l ((n : ℝ) + 1) t + min (((n : ℝ) + 1) * t) 1) c
        (hf := by fun_prop) (ha := hc.isSelfAdjoint)]
      rw [cfc_add c (smoothedIntegerCutCount l ((n : ℝ) + 1))
        (fun t => min (((n : ℝ) + 1) * t) 1) (hf := hf.continuousOn) (hg := by fun_prop),
        smoothedIntegerCut_cfc c hc l n, Algebra.algebraMap_eq_smul_one]
      rfl
    calc
      c = cfc (fun t : ℝ => t) c := (cfc_id' ℝ c hc.isSelfAdjoint).symm
      _ ≤ cfc (fun t => smoothedIntegerCutCount l ((n : ℝ) + 1) t +
          min (((n : ℝ) + 1) * t) 1 + 1 / ((n : ℝ) + 1)) c := by
        apply cfc_mono (hf := continuousOn_id) (hg := by fun_prop)
        intro t ht
        change t ≤ _
        have hb := (smoothedIntegerCutCount_bounds l ((n : ℝ) + 1) t (by positivity) (hs t ht).1 (hs t ht).2).2
        linarith
      _ = _ := heq

lemma spectralApproxUnit_trace_tendsto_realRank (τ : TracialState A) (h : A) (hh : 0 ≤ h) :
    Tendsto (fun n => (τ.functional (spectralApproxUnit h n)).re) atTop
      (𝓝 (normalizedRootRank τ h).toReal) := by
  have hfinite : normalizedRootRank τ h ≠ ∞ :=
    ne_of_lt ((normalizedRootRank_le_one τ h hh).trans_lt ENNReal.one_lt_top)
  have ht := (ENNReal.tendsto_toReal hfinite).comp (spectralApproxUnit_trace_tendsto_rank τ h hh)
  exact ht.congr' (Eventually.of_forall fun n => ENNReal.toReal_ofReal
    (Complex.nonneg_iff.mp (τ.functional.map_nonneg (spectralApproxUnit_nonneg h hh n))).1)

theorem actual_spectral_integer_approximation (τ : TracialState A) (c : A) (hc : 0 ≤ c)
    (l : ℕ) (hl : ‖c‖ ≤ l) :
    0 ≤ (τ.functional c).re - ∑ j ∈ Finset.range l, (normalizedRootRank τ (positiveIntegerCut c j)).toReal ∧
      (τ.functional c).re - ∑ j ∈ Finset.range l, (normalizedRootRank τ (positiveIntegerCut c j)).toReal ≤
        (normalizedRootRank τ c).toReal := by
  have hsum := tendsto_finsetSum (Finset.range l) (fun j _ =>
    spectralApproxUnit_trace_tendsto_realRank τ (positiveIntegerCut c j) (positiveIntegerCut_nonneg c j))
  have hzero : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    convert tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop (1 : ℝ)
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)) using 1
    funext n
    simp only [Function.comp_apply, one_div]
  have hlow (n : ℕ) : (∑ j ∈ Finset.range l, (τ.functional (spectralApproxUnit (positiveIntegerCut c j) n)).re)
      ≤ (τ.functional c).re := by
    have hb : τ.functional (∑ j ∈ Finset.range l, spectralApproxUnit (positiveIntegerCut c j) n) ≤
        τ.functional c := τ.functional.monotone (smoothedIntegerCut_operator_bounds c hc l hl n).1
    simpa only [map_sum, Complex.re_sum] using (Complex.le_def.mp hb).1
  have hupp (n : ℕ) : (τ.functional c).re ≤
      (∑ j ∈ Finset.range l, (τ.functional (spectralApproxUnit (positiveIntegerCut c j) n)).re) +
        (τ.functional (spectralApproxUnit c n)).re + 1 / ((n : ℝ) + 1) := by
    have hb : τ.functional c ≤ τ.functional
        ((∑ j ∈ Finset.range l, spectralApproxUnit (positiveIntegerCut c j) n) +
          spectralApproxUnit c n + (1 / ((n : ℝ) + 1)) • (1 : A)) :=
      τ.functional.monotone (smoothedIntegerCut_operator_bounds c hc l hl n).2
    simpa only [map_add, map_sum, τ.functional.map_smul_of_tower, τ.normalized,
      Complex.add_re, Complex.re_sum, Complex.smul_re, Complex.one_re, smul_eq_mul, mul_one] using
      (Complex.le_def.mp hb).1
  constructor
  · exact sub_nonneg.mpr (le_of_tendsto hsum (Eventually.of_forall hlow))
  · have hlim := (hsum.add (spectralApproxUnit_trace_tendsto_realRank τ c hc)).add hzero
    have hb := (isClosed_Ici : IsClosed (Set.Ici (τ.functional c).re)).mem_of_tendsto
      hlim (Eventually.of_forall hupp)
    simp only [Set.mem_Ici, add_zero] at hb
    linarith
end CuntzPureness

end OAI
