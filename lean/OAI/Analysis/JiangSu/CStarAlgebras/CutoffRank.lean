import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks

namespace OAI

section

namespace Pureness
open Filter Topology
open scoped NNReal ENNReal ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

noncomputable def spectralApproxUnit (h : A) (n : ℕ) : A :=
  cfc (fun t : ℝ => min (((n : ℝ) + 1) * t) 1) h

lemma spectralApproxUnit_nonneg (h : A) (hh : 0 ≤ h) (n : ℕ) :
    0 ≤ spectralApproxUnit h n := by
  apply cfc_nonneg
  intro t ht
  exact le_min (mul_nonneg (by positivity) (spectrum_nonneg_of_nonneg hh ht)) zero_le_one

lemma spectralApproxUnit_norm_le (h : A) (hh : 0 ≤ h) (n : ℕ) :
    ‖spectralApproxUnit h n‖ ≤ 1 := by
  apply norm_cfc_le zero_le_one
  intro t ht
  rw [Real.norm_eq_abs, abs_of_nonneg
    (le_min (mul_nonneg (by positivity) (spectrum_nonneg_of_nonneg hh ht)) zero_le_one)]
  exact min_le_right _ _

lemma spectralApproxUnit_le_one (h : A) (hh : 0 ≤ h) (n : ℕ) :
    spectralApproxUnit h n ≤ 1 :=
  (CStarAlgebra.norm_le_one_iff_of_nonneg _ (spectralApproxUnit_nonneg h hh n)).mp
    (spectralApproxUnit_norm_le h hh n)

lemma spectralApproxUnit_mem (h : A) (hh : 0 ≤ h) (n : ℕ) :
    spectralApproxUnit h n ∈ hereditaryCarrier h := by
  unfold spectralApproxUnit
  rw [← cfcₙ_eq_cfc (hf0 := by simp)]
  change cfcₙ _ h ∈ hereditarySubalgebra h hh
  exact cfcₙ_mem _ (self_mem_hereditary h hh : h ∈ hereditarySubalgebra h hh)

lemma scalar_cutoff_error_bound (p t : ℝ) (hp : 0 < p) (ht : 0 ≤ t) :
    |min (p * t) 1 * t - t| ≤ 1 / p := by
  rcases le_total (p * t) 1 with hle | hge
  · rw [min_eq_left hle, abs_of_nonpos (by nlinarith)]
    calc
      _ ≤ t := by nlinarith [mul_nonneg (mul_nonneg hp.le ht) ht]
      _ ≤ 1 / p := (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hle)
  · rw [min_eq_right hge, one_mul, sub_self, abs_zero]
    positivity

lemma spectralApproxUnit_mul_tendsto (h : A) (hh : 0 ≤ h) :
    Tendsto (fun n => spectralApproxUnit h n * h) atTop (𝓝 h) := by
  have hbound (n : ℕ) : ‖spectralApproxUnit h n * h - h‖ ≤ 1 / ((n : ℝ) + 1) := by
    have heq : cfc (fun t : ℝ => min (((n : ℝ) + 1) * t) 1 * t - t) h =
        spectralApproxUnit h n * h - h := by
      rw [cfc_sub (fun t : ℝ => min (((n : ℝ) + 1) * t) 1 * t) (fun t => t) h,
        cfc_mul (fun t : ℝ => min (((n : ℝ) + 1) * t) 1) (fun t => t) h,
        cfc_id' ℝ h hh.isSelfAdjoint]
      rfl
    rw [← heq]
    apply norm_cfc_le (by positivity)
    intro t ht
    exact scalar_cutoff_error_bound _ t (by positivity) (spectrum_nonneg_of_nonneg hh ht)
  have hi : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    convert tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop (1 : ℝ)
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)) using 1
    funext n
    simp only [Function.comp_apply, one_div]
  have hz : Tendsto (fun n => spectralApproxUnit h n * h - h) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun n => norm_nonneg _) hbound hi)
  simpa only [sub_add_cancel, zero_add] using hz.add_const h

omit [PartialOrder A] [StarOrderedRing A] in
lemma contractive_mul_hereditary_tendsto (h c : A) (hc : c ∈ hereditaryCarrier h)
    (e : ℕ → A) (he : ∀ n, ‖e n‖ ≤ 1)
    (ht : Tendsto (fun n => e n * h) atTop (𝓝 h)) :
    Tendsto (fun n => e n * c) atTop (𝓝 c) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨d, ⟨w, rfl⟩, hd⟩ := Metric.mem_closure_iff.mp hc (ε / 4) (by positivity)
  have ht' : Tendsto (fun n => e n * (h * w * h)) atTop (𝓝 (h * w * h)) := by
    simpa only [mul_assoc] using (ht.mul_const w).mul_const h
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.mp ht' (ε / 2) (by positivity)
  refine ⟨J, fun n hn => ?_⟩
  have hsmall := hJ n hn
  simp only [dist_eq_norm] at hd hsmall ⊢
  have heq : e n * c - c = e n * (c - h * w * h) +
      (e n * (h * w * h) - h * w * h) + (h * w * h - c) := by noncomm_ring
  rw [heq]
  calc
    _ ≤ ‖e n * (c - h * w * h)‖ + ‖e n * (h * w * h) - h * w * h‖ + ‖h * w * h - c‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖e n‖ * ‖c - h * w * h‖ + ‖e n * (h * w * h) - h * w * h‖ + ‖h * w * h - c‖ := by
      gcongr
      exact norm_mul_le _ _
    _ < ε := by
      rw [norm_sub_rev (h * w * h) c]
      nlinarith [he n, norm_nonneg (c - h * w * h)]

lemma spectralApproxUnit_monotone (h : A) (hh : 0 ≤ h) : Monotone (spectralApproxUnit h) := by
  intro n m hnm
  apply cfc_mono (f := fun t : ℝ => min (((n : ℝ) + 1) * t) 1)
    (g := fun t : ℝ => min (((m : ℝ) + 1) * t) 1) (hf := by fun_prop) (hg := by fun_prop)
  intro t ht
  apply min_le_min_right
  apply mul_le_mul_of_nonneg_right _ (spectrum_nonneg_of_nonneg hh ht)
  exact_mod_cast Nat.add_le_add_right hnm 1

noncomputable def cutoffTraceSup (τ : TracialState A) (h : A) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal (τ.functional (spectralApproxUnit h n)).re

lemma cutoffTraceSup_eq_rank (τ : TracialState A) (h : A) (hh : 0 ≤ h) :
    cutoffTraceSup τ h = normalizedRootRank τ h := by
  apply le_antisymm
  · apply iSup_le
    intro n
    exact trace_le_rank_of_mem_hereditary τ h _ hh (spectralApproxUnit_mem h hh n)
      (spectralApproxUnit_le_one h hh n)
  · apply iSup_le
    intro j
    have ht : Tendsto (fun n => spectralApproxUnit h n * normalizedRoot h j)
        atTop (𝓝 (normalizedRoot h j)) :=
      contractive_mul_hereditary_tendsto h _
        (normalizedRoot_mem_hereditary hh (self_mem_hereditary h hh) hh j)
        (spectralApproxUnit h) (spectralApproxUnit_norm_le h hh) (spectralApproxUnit_mul_tendsto h hh)
    have hτ : Tendsto (fun n => ENNReal.ofReal
        (τ.functional (spectralApproxUnit h n * normalizedRoot h j)).re) atTop
        (𝓝 (ENNReal.ofReal (τ.functional (normalizedRoot h j)).re)) :=
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (Complex.continuous_re.continuousAt.tendsto.comp
          ((map_continuous τ.functional).continuousAt.tendsto.comp ht))
    apply le_of_tendsto hτ
    apply Eventually.of_forall
    intro n
    calc
      _ ≤ ENNReal.ofReal (τ.functional (spectralApproxUnit h n)).re :=
        ENNReal.ofReal_le_ofReal (Complex.le_def.mp
          (trace_mul_contraction_le τ _ _ (spectralApproxUnit_nonneg h hh n)
            (normalizedRoot_le_one h hh j))).1
      _ ≤ cutoffTraceSup τ h := le_iSup (fun n => ENNReal.ofReal (τ.functional (spectralApproxUnit h n)).re) n

theorem spectralApproxUnit_trace_tendsto_rank (τ : TracialState A) (h : A) (hh : 0 ≤ h) :
    Tendsto (fun n => ENNReal.ofReal (τ.functional (spectralApproxUnit h n)).re)
      atTop (𝓝 (normalizedRootRank τ h)) := by
  rw [← cutoffTraceSup_eq_rank τ h hh]
  apply tendsto_atTop_iSup
  intro n m hnm
  exact ENNReal.ofReal_le_ofReal
    (Complex.le_def.mp (τ.functional.monotone (spectralApproxUnit_monotone h hh hnm))).1

end Pureness
end

section

namespace Pureness

noncomputable def integerCutCount (l : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range l, if (j : ℝ) + 1 < t then 1 else 0

theorem integerCutCount_bounds (l : ℕ) (t : ℝ) (ht : 0 ≤ t) (hl : t ≤ l) :
    0 ≤ t - integerCutCount l t ∧
      t - integerCutCount l t ≤ if 0 < t then 1 else 0 := by
  induction l with
  | zero =>
    have h : t = 0 := le_antisymm (by simpa using hl) ht
    subst t
    simp [integerCutCount]
  | succ l ih =>
    by_cases htl : t ≤ (l : ℝ)
    · have hlast : ¬ (l : ℝ) + 1 < t := by linarith
      simpa only [integerCutCount, Finset.sum_range_succ, ite_eq_right hlast, add_zero] using ih htl
    · have hlt : (l : ℝ) < t := lt_of_not_ge htl
      have hpos : 0 < t := lt_of_le_of_lt (Nat.cast_nonneg l) hlt
      have hlast : ¬ (l : ℝ) + 1 < t := by exact not_lt_of_ge (by simpa using hl)
      have hcount : integerCutCount l t = l := by
        unfold integerCutCount
        have hone : ∀ j ∈ Finset.range l, (if (j : ℝ) + 1 < t then (1 : ℝ) else 0) = 1 := by
          intro j hj
          have hjl : j + 1 ≤ l := Nat.succ_le_of_lt (Finset.mem_range.mp hj)
          have hjlr : (j : ℝ) + 1 ≤ l := by exact_mod_cast hjl
          simp [lt_of_le_of_lt hjlr hlt]
        rw [Finset.sum_congr rfl hone]
        simp
      have hnext : integerCutCount (l + 1) t = l := by
        simpa only [integerCutCount, Finset.sum_range_succ, ite_eq_right hlast, add_zero] using hcount
      rw [hnext, ite_eq_left hpos]
      constructor <;> push_cast at hl <;> linarith

theorem integerCutCount_zero (l : ℕ) : integerCutCount l 0 = 0 := by
  unfold integerCutCount
  apply Finset.sum_eq_zero
  intro j hj
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  simp [show ¬ (j : ℝ) + 1 < 0 by linarith]

theorem integerCutCount_at_positive_integer (l k : ℕ) (hk : 1 ≤ k) (hkl : k ≤ l) :
    (k : ℝ) - integerCutCount l k = 1 := by
  have hset : integerCutCount l k = ∑ j ∈ Finset.range l, if j < k - 1 then (1 : ℝ) else 0 := by
    unfold integerCutCount
    apply Finset.sum_congr rfl
    intro j hj
    have heq : (j : ℝ) + 1 < k ↔ j < k - 1 := by
      constructor
      · intro h
        have : j + 1 < k := by exact_mod_cast h
        omega
      · intro h
        have : j + 1 < k := by omega
        exact_mod_cast this
    simp only [heq]
  rw [hset]
  have hs : (∑ j ∈ Finset.range l, if j < k - 1 then (1 : ℝ) else 0) = k - 1 := by
    rw [← Finset.sum_filter]
    have hf : (Finset.range l).filter (fun j => j < k - 1) = Finset.range (k - 1) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [hf]
    simp [Nat.cast_sub hk]
  rw [hs]
  linarith

end Pureness
end

end OAI
