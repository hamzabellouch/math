import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseBernoulliRun

namespace OAI

namespace MetricKMedian.SparseBernoulli
open Finset
variable {n d : ℕ}

def tuple (S : Finset (Fin n)) : Fin d → Fin (n+1) :=
  fun a => if h : a.val<S.card then (S.orderEmbOfFin rfl ⟨a.val,h⟩).castSucc
    else ⟨n,Nat.lt_succ_self n⟩

theorem used_tuple (S : Finset (Fin n)) (hS : S.card ≤ d) : used (tuple (d := d) S)=S := by
  ext x
  simp only [used,mem_filter,mem_univ,true_and]
  constructor
  · rintro ⟨a,ha⟩
    dsimp only [tuple] at ha
    split_ifs at ha with h
    · have he : S.orderEmbOfFin rfl ⟨a.val,h⟩=x := Fin.ext ha
      rw [← he]
      exact orderEmbOfFin_mem _ _ _
    · exact False.elim ((Nat.ne_of_gt x.isLt) ha)
  · intro hx
    let a : Fin S.card := (S.orderIsoOfFin rfl).symm ⟨x,hx⟩
    have ha : a.val < d := lt_of_lt_of_le a.isLt hS
    refine ⟨⟨a.val,ha⟩,?_⟩
    dsimp only [tuple]
    rw [dite_eq_left a.isLt]
    change (S.orderEmbOfFin rfl a).val=x.val
    have he := (S.orderIsoOfFin rfl).apply_symm_apply ⟨x,hx⟩
    exact congrArg (fun z : S => (z.val:Fin n).val) he

theorem subset_moment (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (S : Finset (Fin n)) (hS : S.card ≤ d) :
    (run (d := d) p hp n).moment (fun q => ∏ i ∈ S, flag q i)=∏ i ∈ S, p i := by
  have hh := (run_spec (d := d) p hp).2 (tuple S)
  simpa only [monomial,used_tuple S hS] using hh

end MetricKMedian.SparseBernoulli

end OAI
