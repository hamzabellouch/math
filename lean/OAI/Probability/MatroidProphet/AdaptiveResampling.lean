import OAI.Probability.MatroidProphet.FiniteBits

namespace OAI

namespace MatroidProphet
open Finset
variable {α β : Type*} [DecidableEq α]

lemma bitsExpectation_mul_left (q : α → ℝ) (V : Finset α) (c : ℝ) (f : Finset α → ℝ) :
    bitsExpectation q V (fun S => c * f S) = c * bitsExpectation q V f := by
  simp only [bitsExpectation, mul_sum]
  apply sum_congr rfl
  intro S hS
  ring

lemma bitsExpectation_mul_right (q : α → ℝ) (V : Finset α) (c : ℝ) (f : Finset α → ℝ) :
    bitsExpectation q V (fun S => f S * c) = bitsExpectation q V f * c := by
  simp only [bitsExpectation, sum_mul]
  apply sum_congr rfl
  intro S hS
  ring

inductive RevealTree (α β : Type*) where
  | leaf (value : β)
  | query (e : α) (no yes : RevealTree α β)

def RevealTree.Fresh : RevealTree α β → Finset α → Prop
  | .leaf _, _ => True
  | .query e no yes, V => e ∈ V ∧ no.Fresh (V.erase e) ∧ yes.Fresh (V.erase e)

def RevealTree.run : RevealTree α β → Finset α → β
  | .leaf value, _ => value
  | .query e no yes, S => if e ∈ S then yes.run (S.erase e) else no.run (S.erase e)

def RevealTree.queried : RevealTree α β → Finset α → Finset α
  | .leaf _, _ => ∅
  | .query e no yes, S => insert e (if e ∈ S then yes.queried (S.erase e) else no.queried (S.erase e))

def RevealTree.hybrid : RevealTree α β → Finset α → Finset α → Finset α
  | .leaf _, S, _ => S
  | .query e no yes, S, T =>
      let H := if e ∈ S then yes.hybrid (S.erase e) (T.erase e)
        else no.hybrid (S.erase e) (T.erase e)
      if e ∈ T then insert e H else H

lemma RevealTree.queried_subset (tree : RevealTree α β) (V S : Finset α) (fresh : tree.Fresh V) :
    tree.queried S ⊆ V := by
  induction tree generalizing V S with
  | leaf value => exact empty_subset V
  | query e no yes ihn ihy =>
    rcases fresh with ⟨he, hn, hy⟩
    apply insert_subset he
    by_cases heS : e ∈ S
    · simpa [queried, heS] using (ihy (V.erase e) (S.erase e) hy).trans (erase_subset e V)
    · simpa [queried, heS] using (ihn (V.erase e) (S.erase e) hn).trans (erase_subset e V)

lemma RevealTree.run_query_no (e : α) (no yes : RevealTree α β) (S : Finset α) (he : e ∉ S) :
    (RevealTree.query e no yes).run S = no.run S := by simp [run, he]

lemma RevealTree.run_query_yes (e : α) (no yes : RevealTree α β) (S : Finset α) (he : e ∉ S) :
    (RevealTree.query e no yes).run (insert e S) = yes.run S := by simp [run, he]

lemma RevealTree.hybrid_query (e : α) (no yes : RevealTree α β) (S T : Finset α)
    (heS : e ∉ S) (heT : e ∉ T) :
    (RevealTree.query e no yes).hybrid S T = no.hybrid S T ∧
    (RevealTree.query e no yes).hybrid S (insert e T) = insert e (no.hybrid S T) ∧
    (RevealTree.query e no yes).hybrid (insert e S) T = yes.hybrid S T ∧
    (RevealTree.query e no yes).hybrid (insert e S) (insert e T) = insert e (yes.hybrid S T) := by
  simp [hybrid, heS, heT]

lemma RevealTree.mean_run_query (q : α → ℝ) (V : Finset α) (e : α)
    (no yes : RevealTree α β) (φ : β → ℝ) (he : e ∈ V) :
    bitsExpectation q V (fun S => φ ((RevealTree.query e no yes).run S)) =
      (1-q e) * bitsExpectation q (V.erase e) (fun S => φ (no.run S)) +
        q e * bitsExpectation q (V.erase e) (fun S => φ (yes.run S)) := by
  have hs := bitsExpectation_insert q (V.erase e) e (notMem_erase e V)
    (fun S => φ ((RevealTree.query e no yes).run S))
  rw [insert_erase he] at hs
  rw [hs]
  congr 1
  · congr 1
    apply bitsExpectation_congr
    intro S hS
    rw [run_query_no _ _ _ _ (fun heS => notMem_erase e V (hS heS))]
  · congr 1
    apply bitsExpectation_congr
    intro S hS
    rw [run_query_yes _ _ _ _ (fun heS => notMem_erase e V (hS heS))]

theorem RevealTree.hybrid_independent (tree : RevealTree α β)
    (q : α → ℝ) (V : Finset α) (fresh : tree.Fresh V)
    (φ : β → ℝ) (ψ : Finset α → ℝ) :
    bitsExpectation q V (fun S => bitsExpectation q V (fun T => φ (tree.run S) * ψ (tree.hybrid S T))) =
      bitsExpectation q V (fun S => φ (tree.run S)) * bitsExpectation q V ψ := by
  induction tree generalizing V ψ with
  | leaf value =>
    simp only [run, hybrid, bitsExpectation_const]
    exact bitsExpectation_mul_left q V (φ value) ψ
  | query e no yes ihn ihy =>
    rcases fresh with ⟨he, hn, hy⟩
    let W := V.erase e
    have heW : e ∉ W := notMem_erase e V
    have hWV : insert e W = V := insert_erase he
    have hsplit (S : Finset α) := bitsExpectation_insert q W e heW
      (fun T => φ ((RevealTree.query e no yes).run S) * ψ ((RevealTree.query e no yes).hybrid S T))
    have hNo : bitsExpectation q W (fun S => bitsExpectation q V
        (fun T => φ ((RevealTree.query e no yes).run S) * ψ ((RevealTree.query e no yes).hybrid S T))) =
        (1-q e) * bitsExpectation q W (fun S => bitsExpectation q W
          (fun T => φ (no.run S) * ψ (no.hybrid S T))) +
        q e * bitsExpectation q W (fun S => bitsExpectation q W
          (fun T => φ (no.run S) * ψ (insert e (no.hybrid S T)))) := by
      rw [← bitsExpectation_mul_left, ← bitsExpectation_mul_left, ← bitsExpectation_add]
      apply bitsExpectation_congr
      intro S hS
      have heS : e ∉ S := fun hs => heW (hS hs)
      have h := hsplit S
      rw [hWV] at h
      rw [h]
      congr 1
      · congr 1
        apply bitsExpectation_congr
        intro T hT
        have heT : e ∉ T := fun ht => heW (hT ht)
        rw [run_query_no _ _ _ _ heS, (hybrid_query e no yes S T heS heT).1]
      · congr 1
        apply bitsExpectation_congr
        intro T hT
        have heT : e ∉ T := fun ht => heW (hT ht)
        rw [run_query_no _ _ _ _ heS, (hybrid_query e no yes S T heS heT).2.1]
    have hYes : bitsExpectation q W (fun S => bitsExpectation q V
        (fun T => φ ((RevealTree.query e no yes).run (insert e S)) *
          ψ ((RevealTree.query e no yes).hybrid (insert e S) T))) =
        (1-q e) * bitsExpectation q W (fun S => bitsExpectation q W
          (fun T => φ (yes.run S) * ψ (yes.hybrid S T))) +
        q e * bitsExpectation q W (fun S => bitsExpectation q W
          (fun T => φ (yes.run S) * ψ (insert e (yes.hybrid S T)))) := by
      rw [← bitsExpectation_mul_left, ← bitsExpectation_mul_left, ← bitsExpectation_add]
      apply bitsExpectation_congr
      intro S hS
      have heS : e ∉ S := fun hs => heW (hS hs)
      have h := hsplit (insert e S)
      rw [hWV] at h
      rw [h]
      congr 1
      · congr 1
        apply bitsExpectation_congr
        intro T hT
        have heT : e ∉ T := fun ht => heW (hT ht)
        rw [run_query_yes _ _ _ _ heS, (hybrid_query e no yes S T heS heT).2.2.1]
      · congr 1
        apply bitsExpectation_congr
        intro T hT
        have heT : e ∉ T := fun ht => heW (hT ht)
        rw [run_query_yes _ _ _ _ heS, (hybrid_query e no yes S T heS heT).2.2.2]
    have hOuter := bitsExpectation_insert q W e heW
      (fun S => bitsExpectation q V (fun T => φ ((RevealTree.query e no yes).run S) *
        ψ ((RevealTree.query e no yes).hybrid S T)))
    rw [hWV, hNo, hYes] at hOuter
    rw [hOuter, ihn W hn ψ, ihn W hn (fun S => ψ (insert e S)),
      ihy W hy ψ, ihy W hy (fun S => ψ (insert e S)), mean_run_query q V e no yes φ he]
    have hPsi := bitsExpectation_insert q W e heW ψ
    rw [hWV] at hPsi
    rw [hPsi]
    ring

lemma RevealTree.hybrid_eq_resample (tree : RevealTree α β) (V S T : Finset α)
    (fresh : tree.Fresh V) (hS : S ⊆ V) (hT : T ⊆ V) :
    tree.hybrid S T = (S \ tree.queried S) ∪ (T ∩ tree.queried S) := by
  induction tree generalizing V S T with
  | leaf value => simp [hybrid, queried]
  | query e no yes ihn ihy =>
    rcases fresh with ⟨he, hn, hy⟩
    have hSerase : S.erase e ⊆ V.erase e := erase_subset_erase e hS
    have hTerase : T.erase e ⊆ V.erase e := erase_subset_erase e hT
    by_cases heS : e ∈ S
    · have hq := yes.queried_subset (V.erase e) (S.erase e) hy
      have heq : e ∉ yes.queried (S.erase e) := fun h => notMem_erase e V (hq h)
      have hi := ihy (V.erase e) (S.erase e) (T.erase e) hy hSerase hTerase
      simp only [hybrid, queried, ite_eq_left heS, hi]
      by_cases heT : e ∈ T
      · rw [ite_eq_left heT]
        ext x
        by_cases hxe : x = e
        · subst x; simp [heS, heT, heq]
        · simp [hxe]
      · rw [ite_eq_right heT]
        ext x
        by_cases hxe : x = e
        · subst x; simp [heS, heT, heq]
        · simp [hxe]
    · have hq := no.queried_subset (V.erase e) (S.erase e) hn
      have heq : e ∉ no.queried (S.erase e) := fun h => notMem_erase e V (hq h)
      have hi := ihn (V.erase e) (S.erase e) (T.erase e) hn hSerase hTerase
      simp only [hybrid, queried, ite_eq_right heS, hi]
      by_cases heT : e ∈ T
      · rw [ite_eq_left heT]
        ext x
        by_cases hxe : x = e
        · subst x; simp [heS, heT]
        · simp [hxe]
      · rw [ite_eq_right heT]
        ext x
        by_cases hxe : x = e
        · subst x; simp [heS, heT]
        · simp [hxe]

lemma RevealTree.double_event (tree : RevealTree α β) (q : α → ℝ) (V : Finset α)
    (fresh : tree.Fresh V) (event : β → Prop) [DecidablePred event] :
    bitsExpectation q V (fun S => bitsExpectation q V (fun T =>
      (if event (tree.run S) then 1 else 0) *
        (if event (tree.run (tree.hybrid S T)) then 1 else 0))) =
      (bitsExpectation q V (fun S => if event (tree.run S) then 1 else 0)) ^ 2 := by
  rw [tree.hybrid_independent q V fresh (fun b => if event b then 1 else 0)
    (fun S => if event (tree.run S) then 1 else 0)]
  ring

end MatroidProphet

end OAI
