import Mathlib

namespace OAI

namespace Erdos970

section

namespace ErdosAuxiliaryPolynomial

abbrev MonomialIndex (D : ℕ) := Σ k : Fin (D+1), Fin (k.val+1)

theorem monomialIndex_card (D : ℕ) : Fintype.card (MonomialIndex D) = (D+2).choose 2 := by
  simp only [MonomialIndex,Fintype.card_sigma,Fintype.card_fin]
  change (∑ i : Fin (D+1), (fun n : ℕ => n+1) i.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => n+1) (D+1)]
  simpa only [Nat.choose_one_right,Nat.add_assoc] using Nat.sum_range_add_choose D 1

noncomputable def exponent {D : ℕ} (i : MonomialIndex D) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 i.2.val + Finsupp.single 1 (i.1.val-i.2.val)

theorem exponent_zero {D : ℕ} (i : MonomialIndex D) : exponent i 0 = i.2.val := by simp [exponent]

theorem exponent_one {D : ℕ} (i : MonomialIndex D) : exponent i 1 = i.1.val-i.2.val := by simp [exponent]

theorem exponent_injective (D : ℕ) : Function.Injective (@exponent D) := by
  rintro ⟨k,j⟩ ⟨l,h⟩ he
  have hx := congrArg (fun e : Fin 2 →₀ ℕ => e 0) he
  have hy := congrArg (fun e : Fin 2 →₀ ℕ => e 1) he
  simp only [exponent_zero,exponent_one] at hx hy
  have hj := j.isLt
  have hh := h.isLt
  have hkl : k = l := Fin.ext (by omega)
  subst l
  have hjh : j = h := Fin.ext hx
  subst h
  rfl

end ErdosAuxiliaryPolynomial

end

end Erdos970

end OAI
