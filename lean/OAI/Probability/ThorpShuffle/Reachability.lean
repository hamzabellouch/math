import OAI.Probability.ThorpShuffle.MarginalBounds

namespace OAI

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Reachability
open Conditional

theorem run_append (d s t : ℕ) (a : History d s) (b : History d t) :
    run d (s + t) (Fin.append a b) = run d t b * run d s a := by
  induction t with
  | zero =>
    have hz : Fin.append a b = a := by funext i; exact Fin.append_left a b i
    rw [hz, run_zero, one_mul]
    rfl
  | succ t ih =>
    obtain ⟨⟨c, b⟩, rfl⟩ := (Fin.snocEquiv (fun _ : Fin (t + 1) => Coins d)).surjective b
    erw [Fin.append_snoc, run_snoc, run_snoc, ih, mul_assoc]

def zeroCoins (d : ℕ) : Coins (d + 1) := fun _ => false

theorem step_false (d : ℕ) : step (d + 1) (zeroCoins d) = rotate (d + 1) := by
  ext x i
  simp only [step, Equiv.trans_apply, Fin.consEquiv_symm_apply, pairSwitch, zeroCoins, Bool.xor_false]
  change (rotate (d + 1)) (Fin.cons (x 0) (Fin.tail x)) i = _
  rw [Fin.cons_self_tail]

theorem run_false (d t : ℕ) :
    run (d + 1) t (fun _ => zeroCoins d) = rotate (d + 1) ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [run_succ]
    change step (d + 1) (zeroCoins d) * run (d + 1) t (fun _ => zeroCoins d) = _
    rw [step_false, ih, pow_succ']

def returnMonoid (d : ℕ) : Submonoid (State (d + 1)) where
  carrier := {g | ∃ t, orderOf (rotate (d + 1)) ∣ t ∧ ∃ ω : History (d + 1) t, run (d + 1) t ω = g}
  one_mem' := ⟨0, dvd_zero _, fun i => i.elim0, run_zero _ _⟩
  mul_mem' := by
    rintro g h ⟨s, hs, a, rfl⟩ ⟨t, ht, b, rfl⟩
    exact ⟨t + s, dvd_add ht hs, Fin.append b a, run_append _ _ _ _ _⟩

def returnGroup (d : ℕ) : Subgroup (State (d + 1)) :=
  Subgroup.closure (returnMonoid d : Set (State (d + 1)))

@[simp] theorem mem_returnGroup (d : ℕ) (g : State (d + 1)) :
    g ∈ returnGroup d ↔ g ∈ returnMonoid d := by
  change g ∈ (Subgroup.closure (returnMonoid d : Set (State (d + 1)))).toSubmonoid ↔ _
  rw [Subgroup.closure_toSubmonoid_of_finite, Submonoid.closure_eq]

theorem rotate_inv_pow (d : ℕ) :
    rotate (d + 1) ^ (orderOf (rotate (d + 1)) - 1) = (rotate (d + 1))⁻¹ := by
  apply eq_inv_iff_mul_eq_one.mpr
  rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos _), pow_orderOf_eq_one]

theorem inverse_conj_mem (d : ℕ) {g : State (d + 1)} (hg : g ∈ returnGroup d) :
    (rotate (d + 1))⁻¹ * g * rotate (d + 1) ∈ returnGroup d := by
  rw [mem_returnGroup] at hg ⊢
  rcases hg with ⟨t, ht, ω, rfl⟩
  refine ⟨(1 + t) + (orderOf (rotate (d + 1)) - 1), ?_,
    Fin.append (Fin.append (fun _ => zeroCoins d) ω) (fun _ => zeroCoins d), ?_⟩
  · have hp := orderOf_pos (rotate (d + 1))
    have he : (1 + t) + (orderOf (rotate (d + 1)) - 1) = t + orderOf (rotate (d + 1)) := by omega
    rw [he]; exact dvd_add ht (dvd_refl _)
  · rw [run_append, run_append, run_false, run_false, pow_one, rotate_inv_pow, mul_assoc]

theorem inverse_conj_pow_mem (d t : ℕ) {g : State (d + 1)} (hg : g ∈ returnGroup d) :
    (rotate (d + 1) ^ t)⁻¹ * g * rotate (d + 1) ^ t ∈ returnGroup d := by
  induction t with
  | zero => simpa using hg
  | succ t ih =>
    have h := inverse_conj_mem d ih
    simpa only [pow_succ, mul_inv_rev, mul_assoc] using h

theorem canceled_step_mem (d : ℕ) (c : Coins (d + 1)) :
    (rotate (d + 1))⁻¹ * step (d + 1) c ∈ returnGroup d := by
  rw [mem_returnGroup]
  refine ⟨1 + (orderOf (rotate (d + 1)) - 1), ?_,
    Fin.append (fun _ => c) (fun _ => zeroCoins d), ?_⟩
  · rw [Nat.add_sub_of_le (orderOf_pos _)]
  · rw [run_append, run_false, rotate_inv_pow, run_succ, run_zero, mul_one]

end Reachability

namespace Reachability
open Conditional

theorem first_pair_swap (d : ℕ) (s : Position d) :
    (rotate (d + 1))⁻¹ * step (d + 1) (fun x => decide (x = s)) =
      Equiv.swap (Fin.cons false s) (Fin.cons true s) := by
  classical
  apply Equiv.Perm.ext
  intro x
  obtain ⟨⟨b, t⟩, rfl⟩ := (splitPosition d).symm.surjective x
  have hc : ((rotate (d + 1))⁻¹ * step (d + 1) (fun x => decide (x = s)))
      ((splitPosition d).symm (b, t)) =
      (splitPosition d).symm (b ^^ decide (t = s), t) := by
    simp [step, splitPosition, pairSwitch]
  rw [hc]
  change (Fin.cons (b ^^ decide (t = s)) t : Position (d + 1)) =
    Equiv.swap (Fin.cons false s) (Fin.cons true s) (Fin.cons b t)
  by_cases ht : t = s
  · subst t; cases b <;> simp
  · have hf : (Fin.cons b t : Position (d + 1)) ≠ Fin.cons false s := by
      intro h; apply ht; simpa using congrArg Fin.tail h
    have htr : (Fin.cons b t : Position (d + 1)) ≠ Fin.cons true s := by
      intro h; apply ht; simpa using congrArg Fin.tail h
    simp [ht, Equiv.swap_apply_of_ne_of_ne hf htr]

theorem first_pair_mem (d : ℕ) (s : Position d) :
    Equiv.swap (Fin.cons false s) (Fin.cons true s) ∈ returnGroup d := by
  classical
  rw [← first_pair_swap]
  exact canceled_step_mem d _

theorem first_edge_mem (d : ℕ) (x y : Position (d + 1))
    (h : Fin.tail x = Fin.tail y) : Equiv.swap x y ∈ returnGroup d := by
  classical
  rw [← Fin.cons_self_tail x, ← Fin.cons_self_tail y]
  rw [h]
  cases hx : x 0 <;> cases hy : y 0
  · simpa only [Equiv.swap_self, Equiv.Perm.one_def] using (returnGroup d).one_mem
  · exact first_pair_mem d _
  · rw [Equiv.swap_comm]; exact first_pair_mem d _
  · simpa only [Equiv.swap_self, Equiv.Perm.one_def] using (returnGroup d).one_mem

theorem rotate_pow_apply (d t : ℕ) (x : Position d) (j : Fin d) :
    (rotate d ^ t) x j = x ((finRotate d ^ t) j) := by
  induction t generalizing j with
  | zero => rfl
  | succ t ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    simp only [rotate, Equiv.piCongrLeft_apply, Equiv.symm_symm] at *
    simp only [ih, pow_succ, Equiv.Perm.mul_apply]
    simp

theorem finRotate_pow_zero (d : ℕ) (i : Fin (d + 1)) :
    (finRotate (d + 1) ^ i.val) 0 = i := by
  rw [Equiv.Perm.coe_pow, ← finCycle_eq_finRotate_iterate]
  simp

theorem edge_swap_mem (d : ℕ) (i : Fin (d + 1)) (x y : Position (d + 1))
    (h : ∀ j, j ≠ i → x j = y j) : Equiv.swap x y ∈ returnGroup d := by
  classical
  have ht : Fin.tail ((rotate (d + 1) ^ i.val) x) =
      Fin.tail ((rotate (d + 1) ^ i.val) y) := by
    funext j
    simp only [Fin.tail, rotate_pow_apply]
    apply h
    intro he
    have hz : j.succ = 0 := (finRotate (d + 1) ^ i.val).injective
      (he.trans (finRotate_pow_zero d i).symm)
    exact Fin.succ_ne_zero j hz
  have hm := inverse_conj_pow_mem d i.val (first_edge_mem d _ _ ht)
  rw [Equiv.mul_swap_eq_swap_mul, mul_assoc, inv_mul_cancel, mul_one] at hm
  simpa using hm

theorem cube_connected (d : ℕ) (R : Position d → Position d → Prop)
    (hrefl : ∀ x, R x x) (htrans : ∀ x y z, R x y → R y z → R x z)
    (hedge : ∀ (i : Fin d) x y, (∀ j, j ≠ i → x j = y j) → R x y)
    (x y : Position d) : R x y := by
  induction d with
  | zero => have : x = y := Subsingleton.elim _ _; subst y; exact hrefl x
  | succ d ih =>
    let z : Position (d + 1) := Fin.cons (y 0) (Fin.tail x)
    apply htrans x z y
    · apply hedge 0
      intro j hj
      obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hj
      rfl
    · have hh := ih (fun a b => R (Fin.cons (y 0) a) (Fin.cons (y 0) b))
        (fun a => hrefl _) (fun a b c hab hbc => htrans _ _ _ hab hbc)
        (fun i a b hab => hedge i.succ _ _ (by
          intro j
          refine Fin.cases (fun _ => rfl) (fun j hj => ?_) j
          exact hab j (by intro he; subst j; exact hj rfl)))
        (Fin.tail x) (Fin.tail y)
      simpa only [Fin.cons_self_tail] using hh

theorem all_swap_mem (d : ℕ) (x y : Position (d + 1)) :
    Equiv.swap x y ∈ returnGroup d := by
  classical
  apply cube_connected (d + 1) (fun x y => Equiv.swap x y ∈ returnGroup d)
    (fun x => by simpa only [Equiv.swap_self, Equiv.Perm.one_def] using (returnGroup d).one_mem) ?_ (edge_swap_mem d) x y
  intro a b c hab hbc
  by_cases hac : a = c
  · subst c; simpa only [Equiv.swap_self, Equiv.Perm.one_def] using (returnGroup d).one_mem
  by_cases hab' : a = b
  · subst b; exact hbc
  by_cases hbc' : b = c
  · subst c; exact hab
  have hh := (returnGroup d).mul_mem ((returnGroup d).mul_mem hab hbc) hab
  rw [Equiv.mul_swap_eq_swap_mul (Equiv.swap a b) b c, Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hbc'),
    mul_assoc, Equiv.swap_mul_self, mul_one] at hh
  exact hh

theorem returnGroup_eq_top (d : ℕ) : returnGroup d = ⊤ := by
  apply top_unique
  intro g hg
  clear hg
  induction g using Equiv.Perm.swap_induction_on with
  | one => exact (returnGroup d).one_mem
  | swap_mul g x y _ hg => exact (returnGroup d).mul_mem (all_swap_mem d x y) hg

theorem attainable_return (d : ℕ) (g : State (d + 1)) :
    ∃ t, orderOf (rotate (d + 1)) ∣ t ∧ ∃ ω : History (d + 1) t, run (d + 1) t ω = g := by
  have hg : g ∈ returnGroup d := by rw [returnGroup_eq_top]; trivial
  rwa [mem_returnGroup] at hg

end Reachability

end Thorp

end

end OAI
