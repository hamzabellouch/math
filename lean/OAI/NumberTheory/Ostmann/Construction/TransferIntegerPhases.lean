import OAI.NumberTheory.Ostmann.Construction.TransferLocalPhases

namespace OAI

/-! # Reducing the actual integer transfer equation at each surviving prime -/

namespace Ostmann

/-- A left-slot prime divides the left product, so its local equation loses
that term. No primality is required for this algebraic reduction. -/
theorem transfer_equation_mod_left (p L R M : ℕ) (v w s : ℤ)
    (hpL : p ∣ L) (h : v * R - w * L = s * M) :
    (v : ZMod p) * (R : ZMod p) = (s : ZMod p) * (M : ZMod p) := by
  have hL : (L : ZMod p) = 0 := by
    obtain ⟨k, hk⟩ := hpL
    rw [hk, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  have he := congrArg (fun z : ℤ => (z : ZMod p)) h
  push_cast at he
  simpa only [hL, mul_zero, sub_zero] using he

theorem transfer_equation_mod_right (p L R M : ℕ) (v w s : ℤ)
    (hpR : p ∣ R) (h : v * R - w * L = s * M) :
    -(w : ZMod p) * (L : ZMod p) = (s : ZMod p) * (M : ZMod p) := by
  have hR : (R : ZMod p) = 0 := by
    obtain ⟨k, hk⟩ := hpR
    rw [hk, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  have he := congrArg (fun z : ℤ => (z : ZMod p)) h
  push_cast at he
  simpa only [hR, mul_zero, zero_sub, neg_mul] using he

theorem transfer_equation_mod_outside (p L R M : ℕ) (v w s : ℤ)
    (h : v * R - w * L = s * M) :
    (v : ZMod p) * (R : ZMod p) - (w : ZMod p) * (L : ZMod p) =
      (s : ZMod p) * (M : ZMod p) := by
  have he := congrArg (fun z : ℤ => (z : ZMod p)) h
  push_cast at he
  exact he

/-- Natural coprimality supplies the nonzero denominators in the prime field. -/
theorem zmod_natCast_ne_zero_of_coprime {p : ℕ} [Fact p.Prime] (a : ℕ)
    (h : a.Coprime p) : (a : ZMod p) ≠ 0 :=
  isUnit_iff_ne_zero.mp ((ZMod.isUnit_iff_coprime a p).mpr h)

/-- The actual integer equation supplies the left additive phase identity. -/
theorem transfer_left_additive_integer {p : ℕ} [Fact p.Prime]
    (L R M D : ℕ) (v w s : ℤ) (t : ZMod p)
    (hpL : p ∣ L) (hM : M.Coprime p) (hR : R.Coprime p) (hD : D.Coprime p)
    (hrel : v * R - w * L = s * M) :
    ZMod.stdAddChar (t * ((v : ZMod p) / ((M : ZMod p) * (D : ZMod p)))) =
      ZMod.stdAddChar (t * ((s : ZMod p) / ((R : ZMod p) * (D : ZMod p)))) :=
  transfer_left_additive _ _ _ _ _ _
    (zmod_natCast_ne_zero_of_coprime M hM)
    (zmod_natCast_ne_zero_of_coprime R hR)
    (zmod_natCast_ne_zero_of_coprime D hD)
    (transfer_equation_mod_left p L R M v w s hpL hrel)

/-- The right copy is conjugated before using the integer equation. -/
theorem transfer_right_additive_integer {p : ℕ} [Fact p.Prime]
    (L R M D : ℕ) (v w s : ℤ) (t : ZMod p)
    (hpR : p ∣ R) (hM : M.Coprime p) (hL : L.Coprime p) (hD : D.Coprime p)
    (hrel : v * R - w * L = s * M) :
    star (ZMod.stdAddChar (t * ((w : ZMod p) / ((M : ZMod p) * (D : ZMod p))))) =
      ZMod.stdAddChar (t * ((s : ZMod p) / ((L : ZMod p) * (D : ZMod p)))) :=
  transfer_right_additive _ _ _ _ _ _
    (zmod_natCast_ne_zero_of_coprime M hM)
    (zmod_natCast_ne_zero_of_coprime L hL)
    (zmod_natCast_ne_zero_of_coprime D hD)
    (transfer_equation_mod_right p L R M v w s hpR hrel)

end Ostmann

end OAI
