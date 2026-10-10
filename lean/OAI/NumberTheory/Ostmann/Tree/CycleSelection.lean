import Mathlib

namespace OAI

namespace Ostmann.Tree

structure BalancedSelection {E V W : Type*} [DecidableEq V] [DecidableEq W]
    (left : E → V) (right : E → W) where
  positive : Finset E
  negative : Finset E
  disjoint : Disjoint positive negative
  nonempty : positive.Nonempty
  left_balance : ∀ v, (positive.filter (fun e => left e=v)).card =
    (negative.filter (fun e => left e=v)).card
  left_bound : ∀ v, (positive.filter (fun e => left e=v)).card ≤ 1
  right_balance : ∀ w, (positive.filter (fun e => right e=w)).card =
    (negative.filter (fun e => right e=w)).card
  right_bound : ∀ w, (positive.filter (fun e => right e=w)).card ≤ 1

namespace BalancedSelection
variable {E V W : Type*} [DecidableEq E] [DecidableEq V] [DecidableEq W]
  {left : E → V} {right : E → W}

noncomputable def of_parallel (e f : E) (hef : e ≠ f)
    (hl : left e=left f) (hr : right e=right f) : BalancedSelection left right where
  positive := {e}
  negative := {f}
  disjoint := by simpa using hef
  nonempty := Finset.singleton_nonempty e
  left_balance := by
    intro v
    change (Finset.filter (fun a => left a=v) {e}).card =
      (Finset.filter (fun a => left a=v) {f}).card
    simp only [Finset.filter_singleton,hl]
    split_ifs <;> simp
  left_bound := by
    intro v
    exact (Finset.card_le_card (Finset.filter_subset _ {e})).trans (by simp)
  right_balance := by
    intro w
    change (Finset.filter (fun a => right a=w) {e}).card =
      (Finset.filter (fun a => right a=w) {f}).card
    simp only [Finset.filter_singleton,hr]
    split_ifs <;> simp
  right_bound := by
    intro w
    exact (Finset.card_le_card (Finset.filter_subset _ {e})).trans (by simp)

variable {U : Type*} [CommGroup U]

noncomputable def twist (c : BalancedSelection left right) (z : U) (e : E) : U :=
  (if e ∈ c.positive then z else 1)*(if e ∈ c.negative then z⁻¹ else 1)
noncomputable def act (c : BalancedSelection left right) (z : U) (M : E → U) : E → U :=
  fun e => c.twist z e*M e

theorem twist_mul (c : BalancedSelection left right) (z w : U) (e : E) :
    c.twist (z*w) e = c.twist z e*c.twist w e := by
  unfold twist
  split_ifs <;> simp [mul_inv_rev, mul_comm, mul_assoc]

@[simp] theorem act_one (c : BalancedSelection left right) (M : E → U) : c.act 1 M=M := by
  funext e
  simp [act,twist]

theorem act_mul (c : BalancedSelection left right) (z w : U) (M : E → U) :
    c.act (z*w) M=c.act z (c.act w M) := by
  funext e
  simp only [act,twist_mul,mul_assoc]

theorem act_positive (c : BalancedSelection left right) (z : U) (M : E → U)
    {e : E} (he : e ∈ c.positive) : c.act z M e=z*M e := by
  have hn : e ∉ c.negative := fun hn => Finset.disjoint_left.mp c.disjoint he hn
  simp [act,twist,he,hn]

theorem act_negative (c : BalancedSelection left right) (z : U) (M : E → U)
    {e : E} (he : e ∈ c.negative) : c.act z M e=z⁻¹*M e := by
  have hp : e ∉ c.positive := fun hp => Finset.disjoint_left.mp c.disjoint hp he
  simp [act,twist,he,hp]

theorem prod_act (c : BalancedSelection left right) (z : U) (M : E → U)
    (s : Finset E) (hbal : (s.filter (fun e => e ∈ c.positive)).card =
      (s.filter (fun e => e ∈ c.negative)).card) :
    ∏ e ∈ s, c.act z M e = ∏ e ∈ s, M e := by
  simp only [act, twist, Finset.prod_mul_distrib]
  rw [Finset.prod_ite, Finset.prod_ite]
  simp only [Finset.prod_const, one_pow, mul_one]
  rw [hbal, inv_pow, mul_inv_cancel, one_mul]

theorem left_product [Fintype E] (c : BalancedSelection left right) (z : U) (M : E → U)
    (v : V) : (∏ e with left e=v, c.act z M e) = ∏ e with left e=v, M e := by
  apply c.prod_act
  have hp : (Finset.univ.filter (fun e => left e=v)).filter (fun e => e∈c.positive) =
      c.positive.filter (fun e => left e=v) := by ext e; simp [and_comm]
  have hn : (Finset.univ.filter (fun e => left e=v)).filter (fun e => e∈c.negative) =
      c.negative.filter (fun e => left e=v) := by ext e; simp [and_comm]
  rw [hp,hn,c.left_balance]

theorem right_product [Fintype E] (c : BalancedSelection left right) (z : U) (M : E → U)
    (v : W) : (∏ e with right e=v, c.act z M e) = ∏ e with right e=v, M e := by
  apply c.prod_act
  have hp : (Finset.univ.filter (fun e => right e=v)).filter (fun e => e∈c.positive) =
      c.positive.filter (fun e => right e=v) := by ext e; simp [and_comm]
  have hn : (Finset.univ.filter (fun e => right e=v)).filter (fun e => e∈c.negative) =
      c.negative.filter (fun e => right e=v) := by ext e; simp [and_comm]
  rw [hp,hn,c.right_balance]

end BalancedSelection
end Ostmann.Tree

end OAI
