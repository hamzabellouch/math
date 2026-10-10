import Mathlib
import OAI.Combinatorics.KMedianRecovery.Algorithms.FinalBudgetPos
import OAI.Combinatorics.KMedianRecovery.Recovery.Project

namespace OAI

namespace MetricKMedianRecovery.PhaseOriginalLedger
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeInvariant
  PhaseTerminalProducer HistoryPhaseBound PhaseMergeCertificate
universe uD uX
variable {D : Type uD} {X : Type uX} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def Dual (loc : D → X) (F : Finset X) (v lam : ℝ) (alpha : D → ℝ) : Prop :=
  (∀ j, 0 < alpha j) ∧
  (∀ i ∈ F, (∑ j, max (alpha j-2*dist i (loc j)) 0) ≤ lam) ∧
  (∀ (C : Finset D), C.Nonempty → ∀ i ∈ F, ∀ b : ℝ, 0 < b →
    0 < (∑ j ∈ C, dist i (loc j)) → lam ≤ b*(∑ j ∈ C, dist i (loc j)) →
    v^2 ≤ strictnessGap b/(6*(b+2)) →
    (∑ j ∈ C, alpha j) ≤ lam+(2-strictnessGap b/2)*(∑ j ∈ C, dist i (loc j)))

def Ledger (loc : D → X) (F : Finset X) (v lam eta : ℝ)
    (paid bound : ℕ) : Prop :=
  ∃ (S : Finset X) (Q : ℝ) (alpha : D → ℝ),
    S ⊆ F ∧ S.Nonempty ∧ S.card ≤ bound ∧ 0 ≤ Q ∧
    (∑ j, nearestDistance (loc j) S) ≤ Q ∧ Dual loc F v lam alpha ∧
    (1-3*v)*Q+(paid:ℝ)*(lam-(Fintype.card D:ℝ)*eta) ≤ ∑ j, alpha j

omit [DecidableEq X] in
lemma enlarged_ledger [Nonempty D] {loc : D → X} {F : Finset X}
    {v eta lo hi M U : ℝ} {k : ℕ} (hk : 0 < k)
    (h : EnlargedOutput loc F v eta lo hi M U k) :
    ∃ lam, lo ≤ lam ∧ lam ≤ hi ∧
      Ledger loc F v lam eta k (k+3*(limit v (M+hi)+1)) := by
  classical
  obtain ⟨Y,m,d,e,he,B,lam,P,⟨g⟩,hd,hl,hu,hp,ht,hcount,hcopies,alpha,hpos,hdual,hpay,hstrict⟩ := h
  let := m
  let := d
  have hne : (after ∅ P).Nonempty := by
    by_contra hn
    have hz := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [hz,Finset.empty_inter,Finset.card_empty] at hcount
    omega
  obtain ⟨S,hSF,hS,hcard,hcost⟩ := g.original_projection e he hp.after_subset hne
  refine ⟨lam,hl,hu,S,∑ j, nearestDistance (e (loc j)) (after ∅ P),alpha,
    hSF,hS,?_,?_,Finset.sum_le_sum (fun j _ => hcost j),?_,?_⟩
  · rw [hcount] at hcard
    exact hcard.trans (Nat.add_le_add_left hcopies k)
  · exact Finset.sum_nonneg (fun j _ => nearestDistance_nonneg _ _)
  · refine ⟨hpos,?_,?_⟩
    · intro i hi
      have hh := hdual (e i) (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
      simpa only [he] using hh
    · intro C hC i hi b hb hP hprice hsmall
      have hP' : 0 < ∑ j ∈ C, dist (e i) (e (loc j)) := by simpa only [he] using hP
      have hprice' : lam ≤ b*(∑ j ∈ C, dist (e i) (e (loc j))) := by
        simpa only [he] using hprice
      have hh := hstrict C hC (e i) (Finset.mem_image.mpr ⟨i,hi,rfl⟩) b hb hP' hprice' hsmall
      simpa only [he] using hh
  · simpa only [hcount] using hpay

lemma small_ledger [Nonempty D] {loc : D → X} {F : Finset X}
    {v lam M hi : ℝ} {k : ℕ} {P : List (List X)} (hlam : 0 ≤ lam)
    (hp : PrefixData loc F ∅ v lam 0 (limit v (M+hi)+1) P)
    (ht : ∀ j, ¬activeAt loc (1-3*v) ((1+v^2)^(limit v (M+hi))) (after ∅ P) j)
    (hk : (after ∅ P).card ≤ k) (hb : Budget loc F (after ∅ P) v lam 0) :
    Ledger loc F v lam 0 0 k := by
  obtain ⟨alpha,hpos,hdual,hpay,hstrict⟩ := hb
  have hsub : after ∅ P ⊆ F := by simpa only [Finset.union_empty] using hp.after_subset
  have hne : (after ∅ P).Nonempty := by
    by_contra hn
    have hz := Finset.not_nonempty_iff_eq_empty.mp hn
    have h := ht (Classical.arbitrary D)
    simp [hz,activeAt] at h
  refine ⟨after ∅ P,∑ j, nearestDistance (loc j) (after ∅ P),alpha,hsub,hne,hk,
    Finset.sum_nonneg (fun j _ => nearestDistance_nonneg _ _),le_rfl,
    ⟨hpos,hdual,hstrict⟩,?_⟩
  simp only [Nat.cast_zero,zero_mul,add_zero]
  simp only [mul_zero,sub_zero] at hpay
  have hcharge : 0 ≤ ((after ∅ P ∩ F).card:ℝ)*lam := mul_nonneg (Nat.cast_nonneg _) hlam
  linarith only [hpay,hcharge]

theorem produce [Nonempty D] (loc : D → X) (F : Finset X) (v eta : ℝ)
    (lo M : ℚ) (k N : ℕ) (hv : 0 < v) (hvsmall : v < 1/6)
    (heta : 0 ≤ eta) (hprec : (1:ℝ)/2^N ≤ eta)
    (hlo : 0 < lo) (hM : 0 < M) (hN : 3 ≤ N) (hnN : Fintype.card D ≤ N)
    (hk : 2 ≤ k) (hlohi : lo ≤ 8*(Fintype.card D:ℚ)*M)
    (hF : F.Nonempty) (hfar : ∀ i ∈ F, ∀ j, 1 ≤ dist i (loc j))
    (hdiam : ∀ i ∈ F, ∀ j, dist i (loc j) ≤ (M:ℝ)) :
    Ledger loc F v (lo:ℝ) 0 0 k ∨
      ∃ lam, (lo:ℝ) ≤ lam ∧ lam ≤ 8*(Fintype.card D:ℝ)*(M:ℝ) ∧
        Ledger loc F v lam eta k
          (k+3*(limit v ((M:ℝ)+8*(Fintype.card D:ℝ)*(M:ℝ))+1)) := by
  rcases PhaseMergeCertificate.produce loc F v eta lo M k N hv hvsmall heta hprec hlo hM
    hN hnN hk hlohi hF hfar hdiam with ⟨P,hp,ht,hcard,hb⟩ | h
  · exact Or.inl (small_ledger (by exact_mod_cast hlo.le) hp ht hcard hb)
  · exact Or.inr (enlarged_ledger (by omega) h)

end MetricKMedianRecovery.PhaseOriginalLedger

end OAI
