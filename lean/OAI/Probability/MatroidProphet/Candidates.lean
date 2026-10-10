import OAI.Probability.MatroidProphet.Information
import OAI.Probability.MatroidProphet.FiniteBits
import OAI.Probability.MatroidProphet.Pivots.GreedyScan

namespace OAI

open Finset Set

namespace MatroidProphet
namespace Candidates

variable {n : ℕ}

def prior (time : Fin n → ℕ) (H : Finset (Fin n)) (e : Fin n) : Set (Fin n) :=
  {f | f ∈ H ∧ time f < time e}

noncomputable def greedy (M : Matroid (Fin n)) (time : Fin n → ℕ)
    (H : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact H.filter fun e => e ∉ M.closure (prior time H e)

noncomputable def candidates (M : Matroid (Fin n)) (time : Fin n → ℕ)
    (V H : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact (V \ H).filter fun e => e ∉ M.closure (prior time H e)

lemma prior_insert_self (time : Fin n → ℕ) (H : Finset (Fin n)) (e : Fin n) :
    prior time (insert e H) e = prior time H e := by
  ext f
  simp only [prior, Set.mem_ofPred_eq, Finset.mem_insert]
  constructor
  · rintro ⟨rfl | hf, hlt⟩
    · exact (lt_irrefl _ hlt).elim
    · exact ⟨hf, hlt⟩
  · rintro ⟨hf, hlt⟩
    exact ⟨Or.inr hf, hlt⟩

lemma prior_mono (time : Fin n → ℕ) {H V : Finset (Fin n)} (h : H ⊆ V)
    (e : Fin n) : prior time H e ⊆ prior time V e :=
  fun _ hf => ⟨h hf.1, hf.2⟩

lemma greedy_indep (M : Matroid (Fin n)) (time : Fin n → ℕ)
    (ht : Function.Injective time) (H : Finset (Fin n))
    (hground : ∀ e ∈ H, e ∈ M.E) : M.Indep (greedy M time H : Set (Fin n)) := by
  classical
  let label : H → Fin n := Subtype.val
  let arrival : H → ℕ := fun e => time e.val
  have htime : Function.Injective arrival := fun _ _ h => Subtype.ext (ht h)
  have hp (e : H) : label '' {p : H | arrival p < arrival e} = prior time H e.val := by
    ext f
    simp [label, arrival, prior, and_comm]
  have hi := Pivots.keptOccurrences_indep M label arrival (fun e => hground e.val e.property) htime
  have heq : label '' (Pivots.keptOccurrences M label arrival : Set H) =
      (greedy M time H : Set (Fin n)) := by
    ext e
    simp only [Set.mem_image, Finset.mem_coe, Pivots.keptOccurrences, Finset.mem_filter,
      Finset.mem_univ, true_and, greedy]
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact ⟨f.property, by simpa only [hp] using hf⟩
    · rintro ⟨he, hp'⟩
      refine ⟨⟨e, he⟩, ?_, rfl⟩
      simpa only [hp] using hp'
  rwa [heq] at hi

lemma greedy_sdiff_subset_candidates (M : Matroid (Fin n)) (time : Fin n → ℕ)
    (V H : Finset (Fin n)) (hHV : H ⊆ V) :
    greedy M time V \ H ⊆ candidates M time V H := by
  classical
  intro e he
  rcases Finset.mem_sdiff.mp he with ⟨heG, heH⟩
  rcases Finset.mem_filter.mp heG with ⟨heV, hecl⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_sdiff.mpr ⟨heV, heH⟩, ?_⟩
  exact fun h => hecl (M.closure_subset_closure (prior_mono time hHV e) h)

lemma expectation_sum (q : Fin n → ℝ) (V I : Finset (Fin n))
    (f : Fin n → Finset (Fin n) → ℝ) :
    bitsExpectation q V (fun H => ∑ e ∈ I, f e H) =
      ∑ e ∈ I, bitsExpectation q V (f e) := by
  simp only [bitsExpectation, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma expectation_not_mem (q : Fin n → ℝ) (V : Finset (Fin n))
    (e : Fin n) (he : e ∈ V) (c : ℝ) :
    bitsExpectation q V (fun H => if e ∉ H then c else 0) = (1 - q e) * c := by
  have hno : bitsExpectation q (V.erase e) (fun H => if e ∉ H then c else 0) = c := by
    calc
      _ = bitsExpectation q (V.erase e) (fun _ => c) := by
        apply bitsExpectation_congr
        intro H hH
        have heH : e ∉ H := fun hh => (Finset.mem_erase.mp (hH hh)).1 rfl
        simp [heH]
      _ = c := bitsExpectation_const q _ c
  have hyes : bitsExpectation q (V.erase e) (fun H => if e ∉ insert e H then c else 0) = 0 := by
    simp only [Finset.mem_insert_self, not_true_eq_false, ite_false]
    exact bitsExpectation_const q _ 0
  calc
    _ = bitsExpectation q (insert e (V.erase e)) (fun H => if e ∉ H then c else 0) := by
      rw [Finset.insert_erase he]
    _ = (1 - q e) * c := by
      rw [bitsExpectation_insert q _ e (by simp), hno, hyes]
      ring

lemma expectation_sdiff_fair (V I : Finset (Fin n)) (hIV : I ⊆ V) (w : Weights n) :
    bitsExpectation (fun _ => (1 / 2 : ℝ)) V (fun H => ∑ e ∈ I \ H, w e) =
      (∑ e ∈ I, w e) / 2 := by
  classical
  have hsum (H : Finset (Fin n)) :
      (∑ e ∈ I \ H, w e) = ∑ e ∈ I, if e ∉ H then w e else 0 := by
    rw [Finset.sdiff_eq_filter, Finset.sum_filter]
  simp_rw [hsum]
  rw [expectation_sum]
  calc
    (∑ e ∈ I, bitsExpectation (fun _ => (1 / 2 : ℝ)) V
        (fun H => if e ∉ H then w e else 0)) =
        ∑ e ∈ I, (1 - (1 / 2 : ℝ)) * w e := by
      apply Finset.sum_congr rfl
      intro e he
      exact expectation_not_mem _ V e (hIV he) (w e)
    _ = (∑ e ∈ I, w e) / 2 := by
      rw [← Finset.mul_sum]
      ring

lemma greedy_sdiff_indep (M : Matroid (Fin n)) (time : Fin n → ℕ)
    (ht : Function.Injective time) (V H : Finset (Fin n))
    (hground : ∀ e ∈ V, e ∈ M.E) :
    M.Indep (greedy M time V \ H : Set (Fin n)) := by
  apply (greedy_indep M time ht V hground).subset
  intro e he
  exact he.1

lemma expectation_greedy_sdiff_fair (M : Matroid (Fin n)) (time : Fin n → ℕ)
    (V : Finset (Fin n)) (w : Weights n) :
    bitsExpectation (fun _ => (1 / 2 : ℝ)) V (fun H => ∑ e ∈ greedy M time V \ H, w e) =
      (∑ e ∈ greedy M time V, w e) / 2 := by
  classical
  apply expectation_sdiff_fair
  exact Finset.filter_subset _ _

lemma expectation_fair_balance (V : Finset (Fin n)) (e : Fin n) (he : e ∈ V)
    (p : Finset (Fin n) → Prop) [DecidablePred p] (hp : ∀ H, p (insert e H) ↔ p H) (c : ℝ) :
    bitsExpectation (fun _ => (1 / 2 : ℝ)) V
        (fun H => if e ∈ H then 0 else if p H then c else 0) =
      bitsExpectation (fun _ => (1 / 2 : ℝ)) V
        (fun H => if e ∈ H then (if p H then c else 0) else 0) := by
  classical
  let q : Fin n → ℝ := fun _ => 1 / 2
  let f : Finset (Fin n) → ℝ := fun H => if p H then c else 0
  have heH : ∀ H ⊆ V.erase e, e ∉ H := by
    intro H hH he'
    exact (Finset.mem_erase.mp (hH he')).1 rfl
  have hn0 : bitsExpectation q (V.erase e)
      (fun H => if e ∈ H then 0 else if p H then c else 0) =
        bitsExpectation q (V.erase e) f := by
    apply bitsExpectation_congr
    intro H hH
    simp [heH H hH, f]
  have hn1 : bitsExpectation q (V.erase e)
      (fun H => if e ∈ insert e H then 0 else if p (insert e H) then c else 0) = 0 := by
    simp only [Finset.mem_insert_self, ite_true]
    exact bitsExpectation_const q _ 0
  have hy0 : bitsExpectation q (V.erase e)
      (fun H => if e ∈ H then (if p H then c else 0) else 0) = 0 := by
    calc
      _ = bitsExpectation q (V.erase e) (fun _ => 0) := by
        apply bitsExpectation_congr
        intro H hH
        simp [heH H hH]
      _ = 0 := bitsExpectation_const q _ 0
  have hy1 : bitsExpectation q (V.erase e)
      (fun H => if e ∈ insert e H then (if p (insert e H) then c else 0) else 0) =
        bitsExpectation q (V.erase e) f := by
    apply bitsExpectation_congr
    intro H _
    simp [hp H, f]
  change bitsExpectation q V _ = bitsExpectation q V _
  conv_lhs => rw [← Finset.insert_erase he]
  conv_rhs => rw [← Finset.insert_erase he]
  rw [bitsExpectation_insert q _ e (by simp),
    bitsExpectation_insert q _ e (by simp), hn0, hn1, hy0, hy1]
  dsimp [q]
  ring

lemma expectation_candidates_eq_greedy (M : Matroid (Fin n)) (time : Fin n → ℕ)
    (V : Finset (Fin n)) (w : Weights n) :
    bitsExpectation (fun _ => (1 / 2 : ℝ)) V
        (fun H => ∑ e ∈ candidates M time V H, w e) =
      bitsExpectation (fun _ => (1 / 2 : ℝ)) V
        (fun H => ∑ e ∈ greedy M time H, w e) := by
  classical
  let p : Fin n → Finset (Fin n) → Prop := fun e H => e ∉ M.closure (prior time H e)
  have hc (H : Finset (Fin n)) :
      (∑ e ∈ candidates M time V H, w e) =
        ∑ e ∈ V, if e ∈ H then 0 else if p e H then w e else 0 := by
    simp [candidates, Finset.sdiff_eq_filter, Finset.sum_filter, p]
  have hg (H : Finset (Fin n)) (hH : H ⊆ V) :
      (∑ e ∈ greedy M time H, w e) =
        ∑ e ∈ V, if e ∈ H then (if p e H then w e else 0) else 0 := by
    have hset : greedy M time H = V.filter (fun e => e ∈ H ∧ p e H) := by
      ext e
      simp only [greedy, Finset.mem_filter, p]
      constructor
      · intro he
        exact ⟨hH he.1, he⟩
      · intro he
        exact he.2
    rw [hset, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : e ∈ H <;> simp [he]
  calc
    _ = bitsExpectation (fun _ => (1 / 2 : ℝ)) V
        (fun H => ∑ e ∈ V, if e ∈ H then 0 else if p e H then w e else 0) := by
      apply bitsExpectation_congr
      intro H _
      exact hc H
    _ = ∑ e ∈ V, bitsExpectation (fun _ => (1 / 2 : ℝ)) V
        (fun H => if e ∈ H then 0 else if p e H then w e else 0) := expectation_sum _ _ _ _
    _ = ∑ e ∈ V, bitsExpectation (fun _ => (1 / 2 : ℝ)) V
        (fun H => if e ∈ H then (if p e H then w e else 0) else 0) := by
      apply Finset.sum_congr rfl
      intro e he
      apply expectation_fair_balance V e he (p e) _ (w e)
      intro H
      simp [p, prior_insert_self]
    _ = bitsExpectation (fun _ => (1 / 2 : ℝ)) V
        (fun H => ∑ e ∈ V, if e ∈ H then (if p e H then w e else 0) else 0) :=
      (expectation_sum _ _ _ _).symm
    _ = _ := by
      apply bitsExpectation_congr
      intro H hH
      exact (hg H hH).symm

theorem expectation_candidates_le_optimum (M : Matroid (Fin n)) (time : Fin n → ℕ)
    (ht : Function.Injective time) (V : Finset (Fin n))
    (hground : ∀ e ∈ V, e ∈ M.E) (w : Weights n) :
    bitsExpectation (fun _ => (1 / 2 : ℝ)) V
        (fun H => ∑ e ∈ candidates M time V H, w e) ≤ optimum M w := by
  rw [expectation_candidates_eq_greedy]
  calc
    _ ≤ bitsExpectation (fun _ => (1 / 2 : ℝ)) V (fun _ => optimum M w) := by
      apply bitsExpectation_mono _ (by intro e; norm_num) (by intro e; norm_num)
      intro H hH
      exact sum_le_optimum M w _ (greedy_indep M time ht H (fun e he => hground e (hH he)))
    _ = _ := bitsExpectation_const _ _ _

end Candidates
end MatroidProphet

end OAI
