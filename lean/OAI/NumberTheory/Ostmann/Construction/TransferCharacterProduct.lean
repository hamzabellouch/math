import OAI.NumberTheory.Ostmann.Construction.TransferTupleSupport
import OAI.NumberTheory.Ostmann.Construction.TransferGraphPhase

namespace OAI

/-! # The complete multiplicative phase and unary update on actual prime lists -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

section
variable {H Y : Type*} [Fintype H] [Fintype Y]
variable (L R : H → ℕ) (U : Y → ℕ)
variable [∀ h, Fact (L h).Prime] [∀ h, Fact (R h).Prime] [∀ y, Fact (U y).Prime]

noncomputable def transferredCharacterFactor
    (χH : H → ∀ p : ℕ, DirichletCharacter ℂ p)
    (χY : Y → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (νL νR : H → ℂ) (νYL νYR : Y → ℂ) (v w s : ℤ) : (Bool × H) ⊕ Y → ℂ
  | .inl (true, h) =>
      (νL h * χH h (L h) ((v : ZMod (L h)) / (s : ZMod (L h))) ^ b (some (.inl h)) none) *
        updatedGraphRow (χH h (L h)) b (.inl (true, h))
          (fun k => (L k : ZMod (L h))) (fun k => (R k : ZMod (L h))) (fun y => (U y : ZMod (L h)))
  | .inl (false, h) =>
      (conj (νR h) * χH h (R h) ((-w : ZMod (R h)) / (s : ZMod (R h))) ^ (-b (some (.inl h)) none)) *
        updatedGraphRow (χH h (R h)) b (.inl (false, h))
          (fun k => (L k : ZMod (R h))) (fun k => (R k : ZMod (R h))) (fun y => (U y : ZMod (R h)))
  | .inr y => (νYL y * conj (νYR y)) *
      updatedGraphRow (χY y (U y)) b (.inr y)
        (fun k => (L k : ZMod (U y))) (fun k => (R k : ZMod (U y))) (fun z => (U z : ZMod (U y)))

theorem transfer_character_product
    (χH : H → ∀ p : ℕ, DirichletCharacter ℂ p)
    (χY : Y → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (νL νR : H → ℂ) (νYL νYR : Y → ℂ) (M : ℕ) (v w s : ℤ)
    (hrel : v * (∏ h, R h) - w * (∏ h, L h) = s * M)
    (hc : Pairwise (fun i j => (transferredLabels L R U i).Coprime (transferredLabels L R U j)))
    (hM : ∀ i, M.Coprime (transferredLabels L R U i))
    (hs : ∀ i, IsUnit (s : ZMod (transferredLabels L R U i)))
    (hb : ∀ y, b (some (.inr y)) (some (.inr y)) = 0) :
    ((∏ h, νL h * retainedGraphRow (χH h (L h)) b (.inl h) (M : ZMod (L h))
        (Sum.elim (fun k => (L k : ZMod (L h))) (fun y => (U y : ZMod (L h))))) *
      ∏ y, νYL y * retainedGraphRow (χY y (U y)) b (.inr y) (M : ZMod (U y))
        (Sum.elim (fun k => (L k : ZMod (U y))) (fun z => (U z : ZMod (U y))))) *
      conj ((∏ h, νR h * retainedGraphRow (χH h (R h)) b (.inl h) (M : ZMod (R h))
        (Sum.elim (fun k => (R k : ZMod (R h))) (fun y => (U y : ZMod (R h))))) *
        ∏ y, νYR y * retainedGraphRow (χY y (U y)) b (.inr y) (M : ZMod (U y))
          (Sum.elim (fun k => (R k : ZMod (U y))) (fun z => (U z : ZMod (U y))))) =
    ∏ i, transferredCharacterFactor L R U χH χY b νL νR νYL νYR v w s i := by
  have hL (h : H) : νL h * retainedGraphRow (χH h (L h)) b (.inl h) (M : ZMod (L h))
      (Sum.elim (fun k => (L k : ZMod (L h))) (fun y => (U y : ZMod (L h)))) =
      transferredCharacterFactor L R U χH χY b νL νR νYL νYR v w s (.inl (true, h)) := by
    have he := transfer_left_graph_factor (χH h (L h)) b h (M : ZMod (L h)) 1 v s 0
      (fun k => (L k : ZMod (L h))) (fun k => (R k : ZMod (L h)))
      (fun y => (U y : ZMod (L h))) (νL h)
      (zmod_natCast_ne_zero_of_coprime M (hM (.inl (true, h)))) one_ne_zero
      (by simpa only [← Nat.cast_prod] using (zmod_natCast_ne_zero_of_coprime (p := L h)
        (∏ k, R k) (transferred_left_denominators L R U hc h).1))
      (isUnit_iff_ne_zero.mp (hs (.inl (true, h))))
      (by simpa only [← Nat.cast_prod] using (transfer_equation_mod_left (L h)
        (∏ k, L k) (∏ k, R k) M v w s (Finset.dvd_prod_of_mem L (Finset.mem_univ h)) hrel))
    simpa only [zero_mul, AddChar.map_zero_eq_one, one_mul, transferredCharacterFactor] using he
  have hR (h : H) : conj (νR h * retainedGraphRow (χH h (R h)) b (.inl h) (M : ZMod (R h))
      (Sum.elim (fun k => (R k : ZMod (R h))) (fun y => (U y : ZMod (R h))))) =
      transferredCharacterFactor L R U χH χY b νL νR νYL νYR v w s (.inl (false, h)) := by
    have he := transfer_right_graph_factor (χH h (R h)) b h (M : ZMod (R h)) 1 w s 0
      (fun k => (L k : ZMod (R h))) (fun k => (R k : ZMod (R h)))
      (fun y => (U y : ZMod (R h))) (νR h)
      (zmod_natCast_ne_zero_of_coprime M (hM (.inl (false, h)))) one_ne_zero
      (by simpa only [← Nat.cast_prod] using (zmod_natCast_ne_zero_of_coprime (p := R h)
        (∏ k, L k) (transferred_right_denominators L R U hc h).1))
      (isUnit_iff_ne_zero.mp (hs (.inl (false, h))))
      (by simpa only [← Nat.cast_prod] using (transfer_equation_mod_right (R h)
        (∏ k, L k) (∏ k, R k) M v w s (Finset.dvd_prod_of_mem R (Finset.mem_univ h)) hrel))
    simpa only [zero_mul, AddChar.map_zero_eq_one, one_mul, transferredCharacterFactor] using he
  have hY (y : Y) :
      (νYL y * retainedGraphRow (χY y (U y)) b (.inr y) (M : ZMod (U y))
        (Sum.elim (fun k => (L k : ZMod (U y))) (fun z => (U z : ZMod (U y))))) *
      conj (νYR y * retainedGraphRow (χY y (U y)) b (.inr y) (M : ZMod (U y))
        (Sum.elim (fun k => (R k : ZMod (U y))) (fun z => (U z : ZMod (U y))))) =
      transferredCharacterFactor L R U χH χY b νL νR νYL νYR v w s (.inr y) := by
    have hcommon := transfer_common_row_norm_one (χY y (U y)) b y (M : ZMod (U y))
      (fun z => (U z : ZMod (U y))) ((ZMod.isUnit_iff_coprime M (U y)).mpr (hM (.inr y)))
      (fun z hz => (ZMod.isUnit_iff_coprime (U z) (U y)).mpr
        (@hc (.inr z) (.inr y) (by simpa using hz))) (hb y)
    have he := transfer_outside_graph_factor (χY y (U y)) b y (M : ZMod (U y))
      (∏ h, L h : ℕ) (∏ h, R h : ℕ) 1 v w s 0
      (fun k => (L k : ZMod (U y))) (fun k => (R k : ZMod (U y)))
      (fun z => (U z : ZMod (U y))) (νYL y) (νYR y)
      (zmod_natCast_ne_zero_of_coprime M (hM (.inr y)))
      (zmod_natCast_ne_zero_of_coprime _ (transferred_outside_denominators L R U hc y).1)
      (zmod_natCast_ne_zero_of_coprime _ (transferred_outside_denominators L R U hc y).2.1)
      one_ne_zero hcommon
      (transfer_equation_mod_outside (U y) (∏ h, L h) (∏ h, R h) M v w s hrel)
    simpa only [zero_mul, AddChar.map_zero_eq_one, one_mul, transferredCharacterFactor] using he
  rw [transfer_phase_product, Fintype.prod_sum_type, Fintype.prod_prod_type, Fintype.prod_bool]
  rw [show (∏ h, νL h * retainedGraphRow (χH h (L h)) b (.inl h) (M : ZMod (L h))
      (Sum.elim (fun k => (L k : ZMod (L h))) (fun y => (U y : ZMod (L h))))) =
      ∏ h, transferredCharacterFactor L R U χH χY b νL νR νYL νYR v w s (.inl (true, h))
      by exact Finset.prod_congr rfl (fun h _ => hL h)]
  rw [show (∏ h, conj (νR h * retainedGraphRow (χH h (R h)) b (.inl h) (M : ZMod (R h))
      (Sum.elim (fun k => (R k : ZMod (R h))) (fun y => (U y : ZMod (R h)))))) =
      ∏ h, transferredCharacterFactor L R U χH χY b νL νR νYL νYR v w s (.inl (false, h))
      by exact Finset.prod_congr rfl (fun h _ => hR h)]
  congr 1
  exact Finset.prod_congr rfl (fun y _ => hY y)

end
end Ostmann

end OAI
