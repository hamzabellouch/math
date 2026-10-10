import OAI.Analysis.MarkovType.WalkLandmarks
import OAI.Analysis.MarkovType.PrefixIndicators
import OAI.Analysis.MarkovType.NormCompression
import OAI.Analysis.MarkovType.AlternatingNorm
import OAI.Analysis.MarkovType.IntegerCocycle

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

def walkAlphaPoint (n : ℕ) (s : Letter) (j : Fin (walkWindowLength n)) :
    ↥(walkLandmarks n) :=
  ⟨alpha s + (j.val : ℝ), alpha_shift_mem_walkLandmarks n s j⟩

def walkBetaPoint (n : ℕ) (s : Letter) (j : Fin (walkWindowLength n)) :
    ↥(walkLandmarks n) :=
  ⟨beta s + (j.val : ℝ), beta_shift_mem_walkLandmarks n s j⟩

def positiveWalkLabel {n B : ℕ} (C : Chart (walkLandmarks n) B) (s : Letter) : C00 :=
  ∑ j : Fin (walkWindowLength n),
    (C00.basis (C (walkAlphaPoint n s j)).val -
      C00.basis (C (walkBetaPoint n s j)).val)

def rawWalkLabel {n B : ℕ} (C : Chart (walkLandmarks n) B) (s : Letter)
    (C' : Chart (walkLandmarks n) B) : C00 :=
  if s.2 then positiveWalkLabel C s else -positiveWalkLabel C' s.inv

theorem rawWalkLabel_odd {n B : ℕ} (C C' : Chart (walkLandmarks n) B)
    (s : Letter) : rawWalkLabel C' s.inv C = -rawWalkLabel C s C' := by
  rcases s with ⟨i, b⟩
  cases b <;> simp [rawWalkLabel, Letter.inv]

theorem walkEndpoint_rank_pair {n B : ℕ} (C : Chart (walkLandmarks n) B)
    (s : Letter) (j : Fin (walkWindowLength n)) :
    (C (walkAlphaPoint n s j)).val < (C (walkBetaPoint n s j)).val := by
  apply C.strictMono
  change alpha s + (j.val : ℝ) < beta s + (j.val : ℝ)
  simpa only [add_comm] using
    (add_lt_add_right (alpha_lt_beta s) (j.val : ℝ))

theorem walkEndpoint_rank_next {n B : ℕ} (C : Chart (walkLandmarks n) B)
    (s : Letter) (i j : Fin (walkWindowLength n)) (hij : i < j) :
    (C (walkBetaPoint n s i)).val < (C (walkAlphaPoint n s j)).val := by
  apply C.strictMono
  change beta s + (i.val : ℝ) < alpha s + (j.val : ℝ)
  have hstep : i.val + 1 ≤ j.val := Nat.succ_le_of_lt hij
  have hstepR : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by exact_mod_cast hstep
  linarith [alpha_pos s, beta_lt_one s]

theorem positiveWalkLabel_norm (N : OrderedNorm) {n B : ℕ}
    (C : Chart (walkLandmarks n) B) (s : Letter) :
    N (positiveWalkLabel C s) = N.alternatingNorm (walkWindowLength n) := by
  exact N.alternatingPairs_norm
    (fun j => (C (walkAlphaPoint n s j)).val)
    (fun j => (C (walkBetaPoint n s j)).val)
    (walkEndpoint_rank_pair C s) (walkEndpoint_rank_next C s)

theorem rawWalkLabel_norm (N : OrderedNorm) {n B : ℕ}
    (C C' : Chart (walkLandmarks n) B) (s : Letter) :
    N (rawWalkLabel C s C') = N.alternatingNorm (walkWindowLength n) := by
  cases hs : s.2 <;>
    simp only [rawWalkLabel, hs, Bool.false_eq_true, ite_false, ite_true,
      OrderedNorm.neg, positiveWalkLabel_norm]

theorem rawWalkLabel_norm_pos (N : OrderedNorm) {n B : ℕ}
    (C C' : Chart (walkLandmarks n) B) (s : Letter) :
    0 < N (rawWalkLabel C s C') := by
  rw [rawWalkLabel_norm]
  apply N.alternatingNorm_pos
  simp [walkWindowLength]

theorem positiveWalkLabel_supportedBelow {n B : ℕ}
    (C : Chart (walkLandmarks n) B) (s : Letter) :
    C00.SupportedBelow (positiveWalkLabel C s) B := by
  classical
  intro k hk
  simp only [positiveWalkLabel, Finsupp.finsetSum_apply, Finsupp.sub_apply]
  apply Finset.sum_eq_zero
  intro j _
  have ha : (C (walkAlphaPoint n s j)).val ≠ k :=
    ne_of_lt (lt_of_lt_of_le (C (walkAlphaPoint n s j)).isLt hk)
  have hb : (C (walkBetaPoint n s j)).val ≠ k :=
    ne_of_lt (lt_of_lt_of_le (C (walkBetaPoint n s j)).isLt hk)
  simp [C00.basis, ha, hb]

theorem rawWalkLabel_supportedBelow {n B : ℕ}
    (C C' : Chart (walkLandmarks n) B) (s : Letter) :
    C00.SupportedBelow (rawWalkLabel C s C') B := by
  intro k hk
  cases hs : s.2 <;>
    simp only [rawWalkLabel, hs, Bool.false_eq_true, ite_false, ite_true,
      Finsupp.neg_apply, positiveWalkLabel_supportedBelow C s k hk,
      positiveWalkLabel_supportedBelow C' s.inv k hk, neg_zero]

theorem rawWalkLabel_support_subset {n B : ℕ}
    (C C' : Chart (walkLandmarks n) B) (s : Letter) :
    (rawWalkLabel C s C').support ⊆ Finset.range B := by
  intro k hk
  apply Finset.mem_range.mpr
  by_contra h
  exact (Finsupp.mem_support_iff.mp hk)
    (rawWalkLabel_supportedBelow C C' s k (Nat.le_of_not_gt h))

theorem positiveWalkLabel_prefix_bound {n B : ℕ}
    (C : Chart (walkLandmarks n) B) (s : Letter) :
    prefixCut (positiveWalkLabel C s) B = 0 := by
  rw [positiveWalkLabel, prefixCut_finset_sum]
  apply Finset.sum_eq_zero
  intro j _
  simp only [prefixCut_sub, prefixCut_basis,
    ite_eq_left (C (walkAlphaPoint n s j)).isLt,
    ite_eq_left (C (walkBetaPoint n s j)).isLt, sub_self]

theorem rawWalkLabel_prefix_bound {n B : ℕ}
    (C C' : Chart (walkLandmarks n) B) (s : Letter) :
    prefixCut (rawWalkLabel C s C') B = 0 := by
  cases hs : s.2 <;>
    simp only [rawWalkLabel, hs, Bool.false_eq_true, ite_false, ite_true,
      prefixCut_neg, positiveWalkLabel_prefix_bound, neg_zero]

theorem rawWalkLabel_total_zero {n B : ℕ}
    (C C' : Chart (walkLandmarks n) B) (s : Letter) :
    (rawWalkLabel C s C').sum (fun _ a => a) = 0 := by
  classical
  change (∑ k ∈ (rawWalkLabel C s C').support, (rawWalkLabel C s C') k) = 0
  calc
    (∑ k ∈ (rawWalkLabel C s C').support, (rawWalkLabel C s C') k) =
        prefixCut (rawWalkLabel C s C') B := by
      unfold prefixCut
      apply Finset.sum_subset (rawWalkLabel_support_subset C C' s)
      intro k _ hk
      exact Finsupp.notMem_support_iff.mp hk
    _ = 0 := rawWalkLabel_prefix_bound C C' s

theorem positiveWalkLabel_prefix {n B : ℕ}
    (C : Chart (walkLandmarks n) B) (s : Letter) (y : ↥(walkLandmarks n)) :
    prefixCut (positiveWalkLabel C s) ((C y).val + 1) =
      ∑ j : Fin (walkWindowLength n),
        PrefixIndicators.halfOpen (alpha s + (j.val : ℝ))
          (beta s + (j.val : ℝ)) y := by
  rw [positiveWalkLabel, prefixCut_finset_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply prefixCut_chart_basis_sub
  change alpha s + (j.val : ℝ) < beta s + (j.val : ℝ)
  simpa only [add_comm] using
    (add_lt_add_right (alpha_lt_beta s) (j.val : ℝ))

theorem positiveWalkLabel_prefix_indicator {n B : ℕ}
    (C : Chart (walkLandmarks n) B) (s : Letter) (y : ↥(walkLandmarks n))
    (hy0 : 0 < (y : ℝ)) (hyL : (y : ℝ) < (walkWindowLength n : ℝ)) :
    prefixCut (positiveWalkLabel C s) ((C y).val + 1) = (arcIndicator s y : ℝ) := by
  classical
  rw [positiveWalkLabel_prefix]
  calc
    (∑ j : Fin (walkWindowLength n),
        PrefixIndicators.halfOpen (alpha s + (j.val : ℝ))
          (beta s + (j.val : ℝ)) y) = PrefixIndicators.periodic (alpha s) (beta s) y :=
      PrefixIndicators.sum_halfOpen_eq_periodic (alpha_pos s) (beta_lt_one s)
        (walkWindowLength n) hy0 hyL
    _ = (arcIndicator s y : ℝ) := by
      simp only [PrefixIndicators.periodic, arcIndicator, arc, periodicIco,
        Set.mem_ofPred_eq]
      split_ifs with membership <;> norm_num [membership]

theorem rawWalkLabel_prefix_eq_chi {n B : ℕ}
    (C C' : Chart (walkLandmarks n) B) (s : Letter)
    (y y' : ↥(walkLandmarks n))
    (hgood : Chart.Good (letterOrderIso s) C C')
    (hmove : letterOrderIso s (y' : ℝ) = (y : ℝ))
    (hy0 : 0 < (y : ℝ)) (hyL : (y : ℝ) < (walkWindowLength n : ℝ))
    (hy'0 : 0 < (y' : ℝ)) (hy'L : (y' : ℝ) < (walkWindowLength n : ℝ)) :
    prefixCut (rawWalkLabel C s C') ((C y).val + 1) = (chi s y : ℝ) := by
  have hmem : letterOrderIso s (y' : ℝ) ∈ walkLandmarks n := by
    rw [hmove]
    exact y.property
  have hpoint : (⟨letterOrderIso s (y' : ℝ), hmem⟩ : ↥(walkLandmarks n)) = y :=
    Subtype.ext hmove
  have hrank : C' y' = C y := by
    simpa only [hpoint] using hgood y' hmem
  cases hs : s.2
  · have hinverse : (letterOrderIso s).symm (y : ℝ) = (y' : ℝ) := by
      apply (letterOrderIso s).injective
      rw [OrderIso.apply_symm_apply, hmove]
    have hc := arcIndicator_inv_symm s (y : ℝ)
    rw [hinverse] at hc
    have hcR : -(arcIndicator s.inv (y' : ℝ) : ℝ) = (chi s (y : ℝ) : ℝ) := by
      rw [hc]
      simp only [chi, negativeIndicator, hs, Bool.false_eq_true, ite_false,
        Int.cast_sub, Int.cast_one]
      ring
    simp only [rawWalkLabel, hs, Bool.false_eq_true, ite_false, prefixCut_neg]
    rw [← hrank, positiveWalkLabel_prefix_indicator C' s.inv y' hy'0 hy'L]
    exact hcR
  · simpa [rawWalkLabel, hs, chi, negativeIndicator] using
      positiveWalkLabel_prefix_indicator C s y hy0 hyL

end MarkovSuperreflexivity

end

end OAI
