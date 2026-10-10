import OAI.Probability.MatroidProphet.BatchReveal
import OAI.Probability.MatroidProphet.Certificates.Execution

namespace OAI

namespace MatroidProphet
open Finset
variable {α β γ : Type*} [DecidableEq α]

def RevealTree.bind (tree : RevealTree α β) (cont : β → RevealTree α γ) : RevealTree α γ :=
  match tree with
  | .leaf b => cont b
  | .query e no yes => .query e (no.bind cont) (yes.bind cont)

lemma RevealTree.run_bind (tree : RevealTree α β) (cont : β → RevealTree α γ) (S : Finset α) :
    (tree.bind cont).run S = (cont (tree.run S)).run (S \ tree.queried S) := by
  induction tree generalizing S with
  | leaf b => simp [bind, run, queried]
  | query e no yes ihn ihy =>
    by_cases heS : e ∈ S
    · simp only [bind, run, queried, ite_eq_left heS, ihy, erase_sdiff_eq_sdiff_insert]
    · simp only [bind, run, queried, ite_eq_right heS, ihn, erase_sdiff_eq_sdiff_insert]

lemma RevealTree.queried_bind (tree : RevealTree α β) (cont : β → RevealTree α γ) (S : Finset α) :
    (tree.bind cont).queried S =
      tree.queried S ∪ (cont (tree.run S)).queried (S \ tree.queried S) := by
  induction tree generalizing S with
  | leaf b => simp [bind, run, queried]
  | query e no yes ihn ihy =>
    by_cases heS : e ∈ S
    · simp only [bind, run, queried, ite_eq_left heS, ihy, erase_sdiff_eq_sdiff_insert, insert_union]
    · simp only [bind, run, queried, ite_eq_right heS, ihn, erase_sdiff_eq_sdiff_insert, insert_union]

lemma RevealTree.fresh_bind (tree : RevealTree α β) (cont : β → RevealTree α γ)
    (V : Finset α) (fresh : tree.Fresh V)
    (hcont : ∀ S ⊆ V, (cont (tree.run S)).Fresh (V \ tree.queried S)) :
    (tree.bind cont).Fresh V := by
  induction tree generalizing V with
  | leaf b => simpa [bind, run, queried] using hcont ∅ (empty_subset V)
  | query e no yes ihn ihy =>
    rcases fresh with ⟨he, hn, hy⟩
    refine ⟨he, ihn (V.erase e) hn ?_, ihy (V.erase e) hy ?_⟩
    · intro S hS
      have heS : e ∉ S := fun hs => notMem_erase e V (hS hs)
      have hc := hcont S (hS.trans (erase_subset e V))
      simpa only [run, queried, ite_eq_right heS, erase_eq_of_notMem heS,
        erase_sdiff_eq_sdiff_insert] using hc
    · intro S hS
      have heS : e ∉ S := fun hs => notMem_erase e V (hS hs)
      have hc := hcont (insert e S) (insert_subset he (hS.trans (erase_subset e V)))
      simpa only [run, queried, mem_insert_self, ite_true, erase_insert heS,
        erase_eq_of_notMem heS, erase_sdiff_eq_sdiff_insert] using hc

lemma RevealTree.run_congr (tree : RevealTree α β) (V S S' : Finset α)
    (fresh : tree.Fresh V) (agree : ∀ e ∈ V, (e ∈ S ↔ e ∈ S')) :
    tree.run S = tree.run S' := by
  induction tree generalizing V S S' with
  | leaf b => rfl
  | query e no yes ihn ihy =>
    rcases fresh with ⟨he, hn, hy⟩
    have ha := agree e he
    have har : ∀ x ∈ V.erase e, (x ∈ S.erase e ↔ x ∈ S'.erase e) := by
      intro x hx
      simp only [mem_erase, agree x (mem_of_mem_erase hx)]
    by_cases heS : e ∈ S
    · simp only [run, ite_eq_left heS, ite_eq_left (ha.mp heS)]
      exact ihy _ _ _ hy har
    · have heS' : e ∉ S' := fun h => heS (ha.mpr h)
      simp only [run, ite_eq_right heS, ite_eq_right heS']
      exact ihn _ _ _ hn har

lemma RevealTree.queried_congr (tree : RevealTree α β) (V S S' : Finset α)
    (fresh : tree.Fresh V) (agree : ∀ e ∈ V, (e ∈ S ↔ e ∈ S')) :
    tree.queried S = tree.queried S' := by
  induction tree generalizing V S S' with
  | leaf b => rfl
  | query e no yes ihn ihy =>
    rcases fresh with ⟨he, hn, hy⟩
    have ha := agree e he
    have har : ∀ x ∈ V.erase e, (x ∈ S.erase e ↔ x ∈ S'.erase e) := by
      intro x hx
      simp only [mem_erase, agree x (mem_of_mem_erase hx)]
    by_cases heS : e ∈ S
    · simp only [queried, ite_eq_left heS, ite_eq_left (ha.mp heS)]
      rw [ihy _ _ _ hy har]
    · have heS' : e ∉ S' := fun h => heS (ha.mpr h)
      simp only [queried, ite_eq_right heS, ite_eq_right heS']
      rw [ihn _ _ _ hn har]

def RevealTree.transaction (tree : RevealTree α β) (cont : β → QueryProgram α) : QueryProgram α :=
  match tree with
  | .leaf b => .finish (cont b)
  | .query e no yes => .query e (no.transaction cont) (yes.transaction cont)

lemma RevealTree.transaction_fresh (tree : RevealTree α β) (cont : β → QueryProgram α)
    (V : Finset α) (fresh : tree.Fresh V)
    (hcont : ∀ S ⊆ V, (cont (tree.run S)).Fresh (V \ tree.queried S)) :
    (tree.transaction cont).Fresh V := by
  induction tree generalizing V with
  | leaf b => simpa [transaction, QueryProgram.Fresh, run, queried] using hcont ∅ (empty_subset V)
  | query e no yes ihn ihy =>
    rcases fresh with ⟨he, hn, hy⟩
    refine ⟨he, ihn (V.erase e) hn ?_, ihy (V.erase e) hy ?_⟩
    · intro S hS
      have heS : e ∉ S := fun hs => notMem_erase e V (hS hs)
      have hc := hcont S (hS.trans (erase_subset e V))
      simpa only [run, queried, ite_eq_right heS, erase_eq_of_notMem heS,
        erase_sdiff_eq_sdiff_insert] using hc
    · intro S hS
      have heS : e ∉ S := fun hs => notMem_erase e V (hS hs)
      have hc := hcont (insert e S) (insert_subset he (hS.trans (erase_subset e V)))
      simpa only [run, queried, mem_insert_self, ite_true, erase_insert heS,
        erase_eq_of_notMem heS, erase_sdiff_eq_sdiff_insert] using hc

lemma RevealTree.transaction_run (tree : RevealTree α β) (cont : β → QueryProgram α)
    (V : Finset α) (fresh : tree.Fresh V) (cert : Finset α → Prop) [DecidablePred cert]
    (S I : Finset α) :
    (tree.transaction cont).run cert S I =
      (if cert (I ∪ (S ∩ tree.queried S)) then 1 else 0) + (cont (tree.run S)).run cert S ∅ := by
  induction tree generalizing V I with
  | leaf b => simp [transaction, QueryProgram.run, run, queried]
  | query e no yes ihn ihy =>
    rcases fresh with ⟨he, hn, hy⟩
    have ha : ∀ x ∈ V.erase e, (x ∈ S ↔ x ∈ S.erase e) := by
      intro x hx
      simp only [mem_erase]
      exact ⟨fun hs => ⟨(mem_erase.mp hx).1, hs⟩, fun hs => hs.2⟩
    by_cases heS : e ∈ S
    · rw [transaction, QueryProgram.run, ite_eq_left heS, ihy _ hy]
      rw [yes.run_congr _ S (S.erase e) hy ha, yes.queried_congr _ S (S.erase e) hy ha]
      simp only [run, queried, ite_eq_left heS]
      have heq : insert e I ∪ S ∩ yes.queried (S.erase e) =
          I ∪ S ∩ insert e (yes.queried (S.erase e)) := by
        ext x
        by_cases hxe : x = e
        · subst x; simp [heS]
        · simp [hxe]
      rw [heq]
    · rw [transaction, QueryProgram.run, ite_eq_right heS, ihn _ hn]
      rw [no.run_congr _ S (S.erase e) hn ha, no.queried_congr _ S (S.erase e) hn ha]
      simp only [run, queried, ite_eq_right heS]
      have heq : I ∪ S ∩ no.queried (S.erase e) =
          I ∪ S ∩ insert e (no.queried (S.erase e)) := by
        ext x
        by_cases hxe : x = e
        · subst x; simp [heS]
        · simp [hxe]
      rw [heq]

end MatroidProphet

end OAI
