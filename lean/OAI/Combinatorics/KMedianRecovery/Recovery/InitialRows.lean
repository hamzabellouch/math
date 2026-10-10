import Mathlib
import OAI.Combinatorics.KMedianRecovery.Sampling.PrefixData

namespace OAI

namespace MetricKMedianRecovery.PhaseUpperBracket
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

omit [DecidableEq X] in
lemma payment_small (loc : D → X) (F W : Finset X) (v z M : ℝ)
    (hv : 0 ≤ v) (hvsmall : v < 1/6) (hM : 0 ≤ M) (hz : z ≤ M)
    (hW : W ⊆ F) (hdiam : ∀ i ∈ F, ∀ j, dist i (loc j) ≤ M)
    (i : X) (tau : D → ℝ)
    (hadm : admissibleBids loc (1-3*v) (1+v^2) v z W i tau) :
    openingPayment loc (1-3*v) z W i tau ≤ (Fintype.card D:ℝ)*((1+v^2)*M) := by
  classical
  have ht : 0 ≤ 1-3*v := by linarith only [hvsmall]
  have ht1 : 1-3*v ≤ 1 := by linarith only [hv]
  have hK : 0 ≤ 1+v^2 := by positivity
  have hKM : M ≤ (1+v^2)*M := by nlinarith only [mul_nonneg (sq_nonneg v) hM]
  unfold openingPayment
  calc
    _ ≤ ∑ _ : D, (1+v^2)*M := by
      apply Finset.sum_le_sum
      intro j _
      apply max_le _ (by positivity)
      have hd := mul_nonneg ht (dist_nonneg : 0 ≤ dist i (loc j))
      split_ifs with ha
      · exact (sub_le_self _ hd).trans ((hadm j ha).2.1.trans (mul_le_mul_of_nonneg_left hz hK))
      · obtain ⟨f,hf⟩ := inactive_nonempty loc (1-3*v) z W j ha
        have hn : nearestDistance (loc j) W ≤ M :=
          (nearestDistance_le_mem (loc j) W f hf).trans (by rw [dist_comm]; exact hdiam f (hW hf) j)
        have hh := mul_le_mul_of_nonneg_right ht1 (nearestDistance_nonneg (loc j) W)
        linarith only [hn,hh,hd,hKM]
    _ = _ := by simp

omit [DecidableEq X] in
lemma small_impossible [Nonempty D] (loc : D → X) (F W : Finset X) (v z M : ℝ)
    (hv : 0 < v) (hvsmall : v < 1/6) (hM : 0 < M) (hz : z ≤ M)
    (hW : W ⊆ F) (hdiam : ∀ i ∈ F, ∀ j, dist i (loc j) ≤ M) (i : X) :
    ¬etaOpenable loc F W (1-3*v) (1+v^2) v z (8*(Fintype.card D:ℝ)*M) 0 i := by
  rintro ⟨tau,hb,hpay,_⟩
  have hp := payment_small loc F W v z M hv.le hvsmall hM.le hz hW hdiam i tau hb
  simp only [mul_zero,sub_zero] at hpay
  have hn : 0 < (Fintype.card D:ℝ) := by exact_mod_cast Fintype.card_pos
  have hv2 : v^2 < 1/36 := by nlinarith
  have hg : (1+v^2)*M < 8*M := by nlinarith
  have hh := mul_lt_mul_of_pos_left hg hn
  nlinarith only [hp,hpay,hh]

omit [DecidableEq X] in
lemma inactive_impossible [Nonempty D] (loc : D → X) (F W : Finset X) (v z M : ℝ)
    (hv : 0 ≤ v) (hvsmall : v < 1/6) (hM : 0 < M) (hz : M ≤ z)
    (hne : W.Nonempty) (hW : W ⊆ F)
    (hdiam : ∀ i ∈ F, ∀ j, dist i (loc j) ≤ M) (i : X) :
    ¬etaOpenable loc F W (1-3*v) (1+v^2) v z (8*(Fintype.card D:ℝ)*M) 0 i := by
  classical
  rintro ⟨tau,_,hpay,_⟩
  have ht : 0 ≤ 1-3*v := by linarith only [hvsmall]
  have ht1 : 1-3*v ≤ 1 := by linarith only [hv]
  have hnear : ∀ j, nearestDistance (loc j) W ≤ M := by
    intro j
    obtain ⟨f,hf⟩ := hne
    exact (nearestDistance_le_mem (loc j) W f hf).trans (by rw [dist_comm]; exact hdiam f (hW hf) j)
  have hact : ∀ j, ¬activeAt loc (1-3*v) z W j := by
    intro j ha
    have hh := ((activeAt_iff loc (1-3*v) z W j ht hne).mp ha)
    have hh' := mul_le_mul_of_nonneg_right ht1 (nearestDistance_nonneg (loc j) W)
    linarith only [hz,hh,hh',hnear j]
  have hp : openingPayment loc (1-3*v) z W i tau ≤ (Fintype.card D:ℝ)*M := by
    unfold openingPayment
    calc
      _ ≤ ∑ _ : D, M := by
        apply Finset.sum_le_sum
        intro j _
        rw [ite_eq_right (hact j)]
        apply max_le _ hM.le
        have hh := mul_le_mul_of_nonneg_right ht1 (nearestDistance_nonneg (loc j) W)
        have hd := mul_nonneg ht (dist_nonneg : 0 ≤ dist i (loc j))
        linarith only [hh,hd,hnear j]
      _ = _ := by simp
  have hn : 0 < (Fintype.card D:ℝ) := by exact_mod_cast Fintype.card_pos
  simp only [mul_zero,sub_zero] at hpay
  nlinarith only [hpay,hp,mul_pos hn hM]

lemma prefix_invariant [Nonempty D] (loc : D → X) (F Q : Finset X) (v z M : ℝ)
    (hv : 0 < v) (hvsmall : v < 1/6) (hM : 0 < M)
    (hdiam : ∀ i ∈ F, ∀ j, dist i (loc j) ≤ M)
    (hQ : Q ⊆ F) (hc : Q.card ≤ 1) (hz : Q.Nonempty → M ≤ z)
    (H : List X) (h : Prefix loc F ∅ v z (8*(Fintype.card D:ℝ)*M) 0 Q H) :
    (Q ∪ H.toFinset) ⊆ F ∧ (Q ∪ H.toFinset).card ≤ 1 ∧
      ((Q ∪ H.toFinset).Nonempty → M ≤ z) := by
  induction h with
  | nil => simpa using And.intro hQ (And.intro hc hz)
  | @cons Q i H hi htail ih =>
    have hentry : i ∈ F ∧ ∃ W : Finset X, Q ⊆ W ∧ W ⊆ F ∧
        etaOpenable loc F W (1-3*v) (1+v^2) v z (8*(Fintype.card D:ℝ)*M) 0 i := by
      simpa only [Finset.notMem_empty,Finset.union_empty,false_or] using hi.2
    obtain ⟨hiF,W,hQW,hWF,hop⟩ := hentry
    have hz' : M < z := lt_of_not_ge (fun hz' => small_impossible loc F W v z M hv hvsmall hM hz' hWF hdiam i hop)
    have he : Q = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact inactive_impossible loc F W v z M hv.le hvsmall hM (hz ⟨x,hx⟩)
        ⟨x,hQW hx⟩ hWF hdiam i hop
    have hh := ih (Finset.insert_subset hiF hQ) (by simp [he]) (fun _ => hz'.le)
    simpa only [List.toFinset_cons,Finset.union_insert,Finset.insert_union] using hh

lemma history_invariant [Nonempty D] (loc : D → X) (F : Finset X) (v M : ℝ)
    (hv : 0 < v) (hvsmall : v < 1/6) (hM : 0 < M)
    (hdiam : ∀ i ∈ F, ∀ j, dist i (loc j) ≤ M)
    (q : ℕ) (Q : Finset X) (hQ : Q ⊆ F) (hc : Q.card ≤ 1)
    (hz : Q.Nonempty → M ≤ (1+v^2)^q) (T : List (List X))
    (h : History loc F ∅ v (8*(Fintype.card D:ℝ)*M) 0 q Q T) :
    (after Q T) ⊆ F ∧ (after Q T).card ≤ 1 := by
  induction h with
  | nil => exact ⟨hQ,hc⟩
  | @cons q Q H T hhead htail ih =>
    obtain ⟨hsub,hcard,hphase⟩ := prefix_invariant loc F Q v _ M hv hvsmall hM hdiam hQ hc hz H hhead.1
    apply ih hsub hcard
    intro hne
    exact (hphase hne).trans (pow_le_pow_right₀ (by nlinarith only [sq_nonneg v]) (by omega))

theorem attains_high [Nonempty D] (loc : D → X) (F : Finset X) (v M : ℝ)
    (hv : 0 < v) (hvsmall : v < 1/6) (hM : 0 < M)
    (hdiam : ∀ i ∈ F, ∀ j, dist i (loc j) ≤ M) {n c : ℕ}
    (h : Attains loc F ∅ ∅ v (8*(Fintype.card D:ℝ)*M) 0 n c) : c ≤ 1 := by
  obtain ⟨T,_,hh,_,hc⟩ := h
  have hs := history_invariant loc F v M hv hvsmall hM hdiam 0 ∅ (Finset.empty_subset _)
    (by simp) (by simp) T hh
  rw [← hc,Finset.inter_eq_left.mpr hs.1]
  exact hs.2

end MetricKMedianRecovery.PhaseUpperBracket

namespace MetricKMedianRecovery.PhaseInitialBracket
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeInvariant
universe uD uX
variable {D : Type uD} {X : Type uX} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

lemma empty_prefix (loc : D → X) (F B : Finset X) (v lam eta : ℝ) (hlam : 0 ≤ lam)
    (hfar : ∀ i ∈ F, ∀ j, 1 ≤ dist i (loc j)) :
    PrefixData loc F B v lam eta 0 [] := by
  refine ⟨rfl,History.nil _ _,by simp,?_⟩
  intro i hi
  have he : bidRow loc (1-3*v) ((1+v^2)^0) ∅ i = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    simp only [clippedAt,Finset.not_nonempty_empty,↓reduceIte,pow_zero]
    exact max_eq_right (by linarith only [hfar i hi j])
  simpa only [after,he] using hlam

end MetricKMedianRecovery.PhaseInitialBracket

end OAI
