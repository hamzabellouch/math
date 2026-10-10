import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Conclusion

def PartitionMatching {α β ι : Type*} (f : α → ι) (g : β → ι) :=
  {e : α ≃ β // ∀ a, g (e a) = f a}

def partitionMatchingEquiv {α β ι : Type*} (f : α → ι) (g : β → ι) :
    PartitionMatching f g ≃ (∀ i, {a // f a = i} ≃ {b // g b = i}) where
  toFun e i :=
    { toFun := fun a => ⟨e.val a.val, (e.property a.val).trans a.property⟩
      invFun := fun b => ⟨e.val.symm b.val, by
        rw [← e.property, e.val.apply_symm_apply]
        exact b.property⟩
      left_inv := fun a => by ext; exact e.val.symm_apply_apply _
      right_inv := fun b => by ext; exact e.val.apply_symm_apply _ }
  invFun e := ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩
  left_inv e := by
    apply Subtype.ext
    apply Equiv.ext
    intro a
    rfl
  right_inv e := by
    funext i
    apply Equiv.ext
    rintro ⟨a, ha⟩
    subst i
    rfl

theorem card_partitionMatching {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (f : α → ι) (g : β → ι)
    (hcard : ∀ i, Fintype.card {a // f a = i} = Fintype.card {b // g b = i}) :
    Nat.card (PartitionMatching f g) = ∏ i, (Fintype.card {a // f a = i}).factorial := by
  classical
  let : Fintype (PartitionMatching f g) :=
    Fintype.ofEquiv (∀ i, {a // f a = i} ≃ {b // g b = i})
      (partitionMatchingEquiv f g).symm
  rw [Nat.card_eq_fintype_card, Fintype.card_congr (partitionMatchingEquiv f g),
    Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro i hi
  exact Fintype.card_equiv (Fintype.equivOfCardEq (hcard i))

def slotFiberEquiv {r m : ℕ} {ι : Type*} (f : Fin r → ι) (i : ι) :
    {x : Fin r × Fin m // f x.1 = i} ≃ {a : Fin r // f a = i} × Fin m where
  toFun x := (⟨x.val.1,x.property⟩,x.val.2)
  invFun x := ⟨(x.1.val,x.2),x.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_slotFiber {r m : ℕ} {ι : Type*} [DecidableEq ι]
    (f : Fin r → ι) (i : ι) :
    Fintype.card {x : Fin r × Fin m // f x.1 = i} =
      Fintype.card {a : Fin r // f a = i} * m := by
  rw [Fintype.card_congr (slotFiberEquiv (m := m) f i)]
  simp

theorem card_slotPartitionMatching {r m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g : Fin r → ι)
    (hcard : ∀ i, Fintype.card {a // f a = i} = Fintype.card {b // g b = i}) :
    Nat.card (PartitionMatching (fun x : Fin r × Fin m => f x.1)
      (fun x : Fin r × Fin m => g x.1)) =
      ∏ i, (Fintype.card {a : Fin r // f a = i} * m).factorial := by
  classical
  rw [card_partitionMatching]
  · simp_rw [card_slotFiber]
  · intro i
    simp_rw [card_slotFiber, hcard i]

theorem factorial_mul_le (a m : ℕ) :
    (a*m).factorial ≤ m.factorial^a * a^(a*m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc
      (a*(m+1)).factorial = (a*m).factorial * (a*m+1).ascFactorial a := by
        rw [Nat.mul_succ, Nat.factorial_mul_ascFactorial]
      _ ≤ (m.factorial^a*a^(a*m))*(a*m+a)^a :=
        Nat.mul_le_mul ih (Nat.ascFactorial_le_pow_add _ _)
      _ = (m+1).factorial^a*a^(a*(m+1)) := by
        rw [Nat.factorial_succ, Nat.mul_succ]
        rw [show a*m+a = a*(m+1) by ring]
        simp only [mul_pow]
        ring

theorem component_log_bound {a r : ℝ} (ha : 1 ≤ a) (har : a ≤ r) :
    a*Real.log a ≤ (a-1)*(Real.log r+1) := by
  have hap : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hlog := Real.log_le_log hap har
  have hsmall := Real.log_le_sub_one_of_pos hap
  have hmul := mul_le_mul_of_nonneg_left hlog (sub_nonneg.mpr ha)
  nlinarith

end Ostmann.Conclusion

end

end OAI
