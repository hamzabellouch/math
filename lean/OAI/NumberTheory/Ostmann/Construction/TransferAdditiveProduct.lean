import OAI.NumberTheory.Ostmann.Construction.TransferTupleCoordinates

namespace OAI

/-! # The complete additive phase after a transfer, on the actual prime list -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

section
variable {H Y : Type*} [Fintype H] [Fintype Y]
variable (L R : H → ℕ) (U : Y → ℕ)
variable [∀ h, Fact (L h).Prime] [∀ h, Fact (R h).Prime] [∀ y, Fact (U y).Prime]

noncomputable def transferredAdditiveRow (t : ∀ p : ℕ, ZMod p) (s : ℤ) : (Bool × H) ⊕ Y → ℂ
  | .inl (true, h) => ZMod.stdAddChar (t (L h) * ((s : ZMod (L h)) /
      (tupleCofactor (transferredLabels L R U) (.inl (true, h)) : ZMod (L h))))
  | .inl (false, h) => ZMod.stdAddChar (t (R h) * ((s : ZMod (R h)) /
      (tupleCofactor (transferredLabels L R U) (.inl (false, h)) : ZMod (R h))))
  | .inr y => ZMod.stdAddChar (t (U y) * ((s : ZMod (U y)) /
      (tupleCofactor (transferredLabels L R U) (.inr y) : ZMod (U y))))

theorem transfer_additive_product (t : ∀ p : ℕ, ZMod p) (M : ℕ) (v w s : ℤ)
    (hrel : v * (∏ h, R h) - w * (∏ h, L h) = s * M)
    (hLeft : ∀ h, M.Coprime (L h) ∧ (∏ k, R k).Coprime (L h) ∧
      (tupleCofactor L h * ∏ y, U y).Coprime (L h))
    (hRight : ∀ h, M.Coprime (R h) ∧ (∏ k, L k).Coprime (R h) ∧
      (tupleCofactor R h * ∏ y, U y).Coprime (R h))
    (hOutside : ∀ y, M.Coprime (U y) ∧ (∏ h, L h).Coprime (U y) ∧
      (∏ h, R h).Coprime (U y) ∧ (tupleCofactor U y).Coprime (U y)) :
    ((∏ h, ZMod.stdAddChar (t (L h) * ((v : ZMod (L h)) /
          ((M * (tupleCofactor L h * ∏ y, U y) : ℕ) : ZMod (L h))))) *
      ∏ y, ZMod.stdAddChar (t (U y) * ((v : ZMod (U y)) /
          ((M * (∏ h, L h) * tupleCofactor U y : ℕ) : ZMod (U y))))) *
      conj ((∏ h, ZMod.stdAddChar (t (R h) * ((w : ZMod (R h)) /
          ((M * (tupleCofactor R h * ∏ y, U y) : ℕ) : ZMod (R h))))) *
        ∏ y, ZMod.stdAddChar (t (U y) * ((w : ZMod (U y)) /
          ((M * (∏ h, R h) * tupleCofactor U y : ℕ) : ZMod (U y))))) =
    ∏ i, transferredAdditiveRow L R U t s i := by
  have hL (h : H) : ZMod.stdAddChar (t (L h) * ((v : ZMod (L h)) /
        ((M * (tupleCofactor L h * ∏ y, U y) : ℕ) : ZMod (L h)))) =
      transferredAdditiveRow L R U t s (.inl (true, h)) := by
    have he := transfer_left_additive_integer (L := ∏ k, L k) (R := ∏ k, R k)
      (M := M) (D := tupleCofactor L h * ∏ y, U y) v w s (t (L h))
      (Finset.dvd_prod_of_mem L (Finset.mem_univ h))
      (hLeft h).1 (hLeft h).2.1 (hLeft h).2.2 hrel
    simpa only [Nat.cast_mul, transferredAdditiveRow,
      tupleCofactor_transferred_left L R U h (Fact.out : (L h).Prime).ne_zero,
      mul_assoc, mul_left_comm, mul_comm] using he
  have hR (h : H) : conj (ZMod.stdAddChar (t (R h) * ((w : ZMod (R h)) /
        ((M * (tupleCofactor R h * ∏ y, U y) : ℕ) : ZMod (R h))))) =
      transferredAdditiveRow L R U t s (.inl (false, h)) := by
    have he := transfer_right_additive_integer (L := ∏ k, L k) (R := ∏ k, R k)
      (M := M) (D := tupleCofactor R h * ∏ y, U y) v w s (t (R h))
      (Finset.dvd_prod_of_mem R (Finset.mem_univ h))
      (hRight h).1 (hRight h).2.1 (hRight h).2.2 hrel
    simpa only [Nat.cast_mul, transferredAdditiveRow, Complex.star_def,
      tupleCofactor_transferred_right L R U h (Fact.out : (R h).Prime).ne_zero,
      mul_assoc, mul_left_comm, mul_comm] using he
  have hY (y : Y) :
      ZMod.stdAddChar (t (U y) * ((v : ZMod (U y)) /
        ((M * (∏ h, L h) * tupleCofactor U y : ℕ) : ZMod (U y)))) *
      conj (ZMod.stdAddChar (t (U y) * ((w : ZMod (U y)) /
        ((M * (∏ h, R h) * tupleCofactor U y : ℕ) : ZMod (U y))))) =
      transferredAdditiveRow L R U t s (.inr y) := by
    have he := transfer_outside_additive (M : ZMod (U y)) (∏ h, L h : ℕ) (∏ h, R h : ℕ)
      (tupleCofactor U y) v w s (t (U y))
      (zmod_natCast_ne_zero_of_coprime M (hOutside y).1)
      (zmod_natCast_ne_zero_of_coprime _ (hOutside y).2.1)
      (zmod_natCast_ne_zero_of_coprime _ (hOutside y).2.2.1)
      (zmod_natCast_ne_zero_of_coprime _ (hOutside y).2.2.2)
      (transfer_equation_mod_outside (U y) (∏ h, L h) (∏ h, R h) M v w s hrel)
    simpa only [Nat.cast_mul, Int.cast_natCast, transferredAdditiveRow,
      tupleCofactor_transferred_outside L R U y (Fact.out : (U y).Prime).ne_zero] using he
  rw [transfer_phase_product, Fintype.prod_sum_type, Fintype.prod_prod_type, Fintype.prod_bool]
  rw [show (∏ h, ZMod.stdAddChar (t (L h) * ((v : ZMod (L h)) /
        ((M * (tupleCofactor L h * ∏ y, U y) : ℕ) : ZMod (L h))))) =
      ∏ h, transferredAdditiveRow L R U t s (.inl (true, h)) by
        exact Finset.prod_congr rfl (fun h _ => hL h)]
  rw [show (∏ h, conj (ZMod.stdAddChar (t (R h) * ((w : ZMod (R h)) /
        ((M * (tupleCofactor R h * ∏ y, U y) : ℕ) : ZMod (R h)))))) =
      ∏ h, transferredAdditiveRow L R U t s (.inl (false, h)) by
        exact Finset.prod_congr rfl (fun h _ => hR h)]
  congr 1
  exact Finset.prod_congr rfl (fun y _ => hY y)

end
end Ostmann

end OAI
