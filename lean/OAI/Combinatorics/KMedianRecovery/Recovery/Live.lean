import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.ImagePhaseUnion

namespace OAI

namespace MetricKMedianRecovery.HistoryPhaseBound
open PhaseHistoryTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def Live (loc : D → X) (v : ℝ) : ℕ → Finset X → List (List X) → Prop
  | _,_,[] => True
  | q,Q,H::T => (∃ j, activeAt loc (1-3*v) ((1+v^2)^q) Q j) ∧
      Live loc v (q+1) (Q ∪ H.toFinset) T

noncomputable def limit (v Z : ℝ) : ℕ := ⌈Real.log Z / Real.log (1+v^2)⌉₊+1

lemma limit_threshold (v Z : ℝ) (hv : 0 < v) (hZ : 0 < Z) :
    Z < (1+v^2)^(limit v Z) := by
  have hK : 1 < 1+v^2 := by nlinarith
  have hlog := Real.log_pos hK
  have hceil := Nat.le_ceil (Real.log Z / Real.log (1+v^2))
  have hq : Real.log Z / Real.log (1+v^2) < (limit v Z : ℝ) := by
    simp only [limit,Nat.cast_add,Nat.cast_one]
    linarith
  have hmul := (div_lt_iff₀ hlog).mp hq
  apply (Real.log_lt_log_iff hZ (pow_pos (by positivity : 0 < 1+v^2) _)).mp
  simpa only [Real.log_pow] using hmul

omit [DecidableEq X] in
lemma active_bound (loc : D → X) (F Q : Finset X) (hF : F.Nonempty)
    (v lam M z : ℝ) (ht : 0 ≤ 1-3*v)
    (hrow : ∀ i ∈ F, bidRow loc (1-3*v) z Q i ≤ lam)
    (hM : ∀ i ∈ F, ∀ j, dist i (loc j) ≤ M)
    (ha : ∃ j, activeAt loc (1-3*v) z Q j) : z ≤ M+lam := by
  obtain ⟨j,hj⟩ := ha
  obtain ⟨i,hi⟩ := hF
  have hc := clippedAt_of_active loc (1-3*v) z Q j ht hj
  have hsum : max (clippedAt loc (1-3*v) z Q j-dist i (loc j)) 0 ≤
      bidRow loc (1-3*v) z Q i :=
    Finset.single_le_sum (fun a _ => le_max_right
      (clippedAt loc (1-3*v) z Q a-dist i (loc a)) 0) (Finset.mem_univ j)
  rw [hc] at hsum
  have hh := (le_max_left (z-dist i (loc j)) 0).trans (hsum.trans (hrow i hi))
  linarith only [hh,hM i hi j]

theorem length_bound (loc : D → X) (F B Q : Finset X) (hF : F.Nonempty)
    (v lam M Z : ℝ) (hv : 0 < v) (hvsmall : v < 1/6) (hlam : 0 < lam)
    (hM : ∀ i ∈ F, ∀ j, dist i (loc j) ≤ M) (hZ : 0 < Z) (hZbound : M+lam ≤ Z)
    (eta : ℝ) (q : ℕ) (T : List (List X))
    (hrow : ∀ i ∈ F, bidRow loc (1-3*v) ((1+v^2)^q) Q i ≤ lam)
    (hq : q ≤ limit v Z) (hh : History loc F B v lam eta q Q T)
    (hlive : Live loc v q Q T) : q+T.length ≤ limit v Z := by
  induction hh with
  | nil => simpa using hq
  | @cons q Q H T hhead htail ih =>
    have hphase := active_bound loc F Q hF v lam M ((1+v^2)^q)
      (by linarith only [hvsmall]) hrow hM hlive.1
    have hq' : q+1 ≤ limit v Z := by
      by_contra hn
      have hle : limit v Z ≤ q := by omega
      have hp : (1+v^2)^(limit v Z) ≤ (1+v^2)^q :=
        pow_le_pow_right₀ (by nlinarith : 1 ≤ 1+v^2) hle
      have hlt := limit_threshold v Z hv hZ
      linarith
    have hi := ih (advance_rows loc F B Q v lam eta q H hv hvsmall hlam hrow hhead)
      hq' hlive.2
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm 1] using hi

omit [Fintype D] [PseudoMetricSpace X] in

theorem free_count (F Q : Finset X) (T : List (List X)) (b : ℕ)
    (hb : ∀ H ∈ T, (H.toFinset \ F).card ≤ b) :
    (after Q T \ F).card ≤ (Q \ F).card+b*T.length := by
  induction T generalizing Q with
  | nil => simp [after]
  | cons H T ih =>
    have ht := ih (Q ∪ H.toFinset) (fun G hG => hb G (List.mem_cons_of_mem H hG))
    have hH := hb H (List.mem_cons_self)
    have hs : ((Q ∪ H.toFinset) \ F).card ≤ (Q \ F).card+(H.toFinset \ F).card := by
      rw [Finset.union_sdiff_distrib]
      exact Finset.card_union_le _ _
    simp only [after,List.length_cons]
    calc
      (after (Q ∪ H.toFinset) T \ F).card ≤ ((Q ∪ H.toFinset) \ F).card+b*T.length := ht
      _ ≤ (Q \ F).card+b+b*T.length := by omega
      _ = (Q \ F).card+b*(T.length+1) := by ring

theorem uniform_copy_bound (loc : D → X) (F B : Finset X) (hF : F.Nonempty)
    (v lam M Z : ℝ) (hv : 0 < v) (hvsmall : v < 1/6) (hlam : 0 < lam)
    (hM : ∀ i ∈ F, ∀ j, dist i (loc j) ≤ M) (hZ : 0 < Z) (hZbound : M+lam ≤ Z)
    (eta : ℝ) (T : List (List X))
    (hfar : ∀ j, ∀ i ∈ F, 1 ≤ dist i (loc j))
    (hh : History loc F B v lam eta 0 ∅ T) (hlive : Live loc v 0 ∅ T)
    (hthree : ∀ H ∈ T, (H.toFinset \ F).card ≤ 3) :
    T.length ≤ limit v Z ∧ (after ∅ T \ F).card ≤ 3*limit v Z := by
  have hrow : ∀ i ∈ F, bidRow loc (1-3*v) ((1+v^2)^0) ∅ i ≤ lam := by
    intro i hi
    have he : bidRow loc (1-3*v) ((1+v^2)^0) ∅ i = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      simp only [clippedAt,Finset.not_nonempty_empty,↓reduceIte,pow_zero]
      exact max_eq_right (by linarith only [hfar j i hi])
    rw [he]
    exact hlam.le
  have hlen : T.length ≤ limit v Z := by
    simpa using length_bound loc F B ∅ hF v lam M Z hv hvsmall hlam hM hZ hZbound
      eta 0 T hrow (Nat.zero_le _) hh hlive
  refine ⟨hlen,?_⟩
  have hc := free_count F ∅ T 3 hthree
  simp only [Finset.empty_sdiff,Finset.card_empty,zero_add] at hc
  exact hc.trans (Nat.mul_le_mul_left 3 hlen)

lemma limit_upper (v Z : ℝ) (hv : 0 < v) (hZ : 1 ≤ Z) :
    (limit v Z : ℝ) < Real.log Z / Real.log (1+v^2)+2 := by
  have hK : 1 < 1+v^2 := by nlinarith
  have hn : 0 ≤ Real.log Z / Real.log (1+v^2) :=
    div_nonneg (Real.log_nonneg hZ) (Real.log_pos hK).le
  have hc := Nat.ceil_lt_add_one hn
  simp only [limit,Nat.cast_add,Nat.cast_one]
  linarith

theorem polynomial_limit_bound (v M N C : ℝ) (p : ℕ)
    (hv : 0 < v) (hN : 3 ≤ N) (hC : 1 ≤ C) (hM : 1 ≤ M)
    (hupper : M ≤ C*N^p) :
    (3*limit v (M+8*N*M) : ℝ) <
      3*((Real.log (9*C)+(p+1)*Real.log N)/Real.log (1+v^2)+2) := by
  have hNp : 0 < N := by linarith
  have hCp : 0 < C := by linarith
  have hMp : 0 < M := by linarith
  have hZ : 1 ≤ M+8*N*M := by nlinarith
  have hupper' : M+8*N*M ≤ 9*C*N^(p+1) := by
    calc
      M+8*N*M = (1+8*N)*M := by ring
      _ ≤ (9*N)*(C*N^p) := by gcongr; nlinarith
      _ = 9*C*N^(p+1) := by rw [pow_succ]; ring
  have hlog := Real.log_le_log (by linarith : 0 < M+8*N*M) hupper'
  have hlogeq : Real.log (9*C*N^(p+1)) = Real.log (9*C)+(p+1)*Real.log N := by
    rw [Real.log_mul (mul_pos (by norm_num) hCp).ne' (pow_pos hNp _).ne',Real.log_pow]
    simp only [Nat.cast_add,Nat.cast_one]
  rw [hlogeq] at hlog
  have hK : 0 < Real.log (1+v^2) := Real.log_pos (by nlinarith)
  have hl := limit_upper v (M+8*N*M) hv hZ
  have hdiv := div_le_div_of_nonneg_right hlog hK.le
  linarith

end MetricKMedianRecovery.HistoryPhaseBound

end OAI
