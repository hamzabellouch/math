import OAI.NumberTheory.Ostmann.Characters.PrimitiveGaussFourier

namespace OAI

/-! # Chinese remainder factorization of the finite Fourier transform -/

namespace Ostmann

open scoped BigOperators

private theorem stdAddChar_mul_factor {m n : ℕ} [NeZero m] [NeZero n]
    (x : ZMod (m * n)) :
    ZMod.stdAddChar ((n : ZMod (m * n)) * x) =
      ZMod.stdAddChar ((ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m)) x) := by
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
  rw [map_intCast]
  have he : (n : ZMod (m * n)) * (a : ZMod (m * n)) = ((n * a : ℤ) : ZMod (m * n)) := by
    push_cast
    rfl
  rw [he, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  field_simp

private theorem crt_fst {m n : ℕ} (h : m.Coprime n) (x : ZMod (m * n)) :
    ((ZMod.chineseRemainder h) x).1 =
      (ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m)) x := by
  simp only [ZMod.chineseRemainder, RingEquiv.coe_mk, Equiv.coe_fn_mk,
    ZMod.castHom_apply, Prod.fst_zmod_cast]

private theorem crt_snd {m n : ℕ} (h : m.Coprime n) (x : ZMod (m * n)) :
    ((ZMod.chineseRemainder h) x).2 =
      (ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n)) x := by
  simp only [ZMod.chineseRemainder, RingEquiv.coe_mk, Equiv.coe_fn_mk,
    ZMod.castHom_apply, Prod.snd_zmod_cast]

theorem crt_stdAddChar {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (x : ZMod (m * n)) :
    ZMod.stdAddChar x =
      ZMod.stdAddChar ((n : ZMod m)⁻¹ * ((ZMod.chineseRemainder h) x).1) *
      ZMod.stdAddChar ((m : ZMod n)⁻¹ * ((ZMod.chineseRemainder h) x).2) := by
  let a : ZMod m := (n : ZMod m)⁻¹ * ((ZMod.chineseRemainder h) x).1
  let b : ZMod n := (m : ZMod n)⁻¹ * ((ZMod.chineseRemainder h) x).2
  have ha : IsUnit (n : ZMod m) := (ZMod.isUnit_iff_coprime n m).mpr h.symm
  have hb : IsUnit (m : ZMod n) := (ZMod.isUnit_iff_coprime m n).mpr h
  have hx : x = (n : ZMod (m * n)) * a.val + (m : ZMod (m * n)) * b.val := by
    apply (ZMod.chineseRemainder h).injective
    apply Prod.ext
    · rw [crt_fst, crt_fst]
      simp only [map_add, map_mul, map_natCast, ZMod.natCast_self, zero_mul, add_zero,
        ZMod.natCast_zmod_val]
      dsimp [a]
      rw [← mul_assoc, ZMod.mul_inv_of_unit _ ha, one_mul, crt_fst]
      rfl
    · rw [crt_snd, crt_snd]
      simp only [map_add, map_mul, map_natCast, ZMod.natCast_self, zero_mul, zero_add,
        ZMod.natCast_zmod_val]
      dsimp [b]
      rw [← mul_assoc, ZMod.mul_inv_of_unit _ hb, one_mul, crt_snd]
      rfl
  have hn : ZMod.stdAddChar ((m : ZMod (m * n)) * (b.val : ZMod (m * n))) =
      ZMod.stdAddChar b := by
    have he : (m : ZMod (m * n)) * (b.val : ZMod (m * n)) =
        ((m * b.val : ℕ) : ZMod (m * n)) := by push_cast; rfl
    calc
      _ = Complex.exp (2 * Real.pi * Complex.I * ((m * b.val : ℕ) : ℂ) / (m * n)) := by
        rw [he, ← Int.cast_natCast, ZMod.stdAddChar_coe]
        push_cast
        rfl
      _ = Complex.exp (2 * Real.pi * Complex.I * (b.val : ℂ) / n) := by
        congr 1
        push_cast
        have hm : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
        field_simp
      _ = ZMod.stdAddChar b := by
        simpa only [ZMod.stdAddChar_apply] using (ZMod.toCircle_apply b).symm
  change ZMod.stdAddChar x = ZMod.stdAddChar a * ZMod.stdAddChar b
  calc
    _ = ZMod.stdAddChar ((n : ZMod (m * n)) * (a.val : ZMod (m * n)) + (m : ZMod (m * n)) * (b.val : ZMod (m * n))) := by rw [hx]
    _ = _ := by
      rw [AddChar.map_add_eq_mul, stdAddChar_mul_factor, hn]
      simp only [map_natCast, ZMod.natCast_zmod_val]

/-- Probability normalization makes the coprime Fourier transform a product. -/
theorem additiveFourier_crt {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (f : ZMod m → ℂ) (g : ZMod n → ℂ) (u : ZMod (m * n)) :
    additiveFourier (fun x => f ((ZMod.chineseRemainder h) x).1 *
      g ((ZMod.chineseRemainder h) x).2) u =
      additiveFourier f ((n : ZMod m)⁻¹ * ((ZMod.chineseRemainder h) u).1) *
      additiveFourier g ((m : ZMod n)⁻¹ * ((ZMod.chineseRemainder h) u).2) := by
  let e := ZMod.chineseRemainder h
  have he (x : ZMod (m * n)) : ZMod.stdAddChar (-(x * u)) =
      ZMod.stdAddChar (-( (e x).1 * ((n : ZMod m)⁻¹ * (e u).1))) *
      ZMod.stdAddChar (-( (e x).2 * ((m : ZMod n)⁻¹ * (e u).2))) := by
    rw [crt_stdAddChar h]
    simp only [map_neg, map_mul]
    change ZMod.stdAddChar ((n : ZMod m)⁻¹ * -((e x).1 * (e u).1)) *
      ZMod.stdAddChar ((m : ZMod n)⁻¹ * -((e x).2 * (e u).2)) = _
    congr 2 <;> ring
  have hs : (∑ x : ZMod (m * n), f (e x).1 * g (e x).2 * ZMod.stdAddChar (-(x * u))) =
      (∑ a : ZMod m, f a * ZMod.stdAddChar (-(a * ((n : ZMod m)⁻¹ * (e u).1)))) *
      (∑ b : ZMod n, g b * ZMod.stdAddChar (-(b * ((m : ZMod n)⁻¹ * (e u).2)))) := by
    simp_rw [he]
    rw [← e.symm.bijective.sum_comp (fun x =>
      f (e x).1 * g (e x).2 *
      (ZMod.stdAddChar (-((e x).1 * ((n : ZMod m)⁻¹ * (e u).1))) *
       ZMod.stdAddChar (-((e x).2 * ((m : ZMod n)⁻¹ * (e u).2)))))]
    simp only [e.apply_symm_apply]
    rw [Fintype.sum_prod_type, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    ring
  rw [additiveFourier_apply, hs, additiveFourier_apply, additiveFourier_apply,
    Nat.cast_mul, mul_inv]
  ring

/-- Translation contributes its additive character with the negative Fourier sign. -/
theorem additiveFourier_translate {N : ℕ} [NeZero N]
    (f : ZMod N → ℂ) (t u : ZMod N) :
    additiveFourier (fun x => f (x - t)) u =
      ZMod.stdAddChar (-(t * u)) * additiveFourier f u := by
  rw [additiveFourier_apply, additiveFourier_apply]
  have hs := (Equiv.addRight t).bijective.sum_comp
    (fun x : ZMod N => f (x - t) * ZMod.stdAddChar (-(x * u)))
  rw [← hs]
  change (N : ℂ)⁻¹ * (∑ x : ZMod N, f ((x + t) - t) *
    ZMod.stdAddChar (-((x + t) * u))) = _
  simp only [add_sub_cancel_right]
  have he (x : ZMod N) : -((x + t) * u) = -(x * u) + -(t * u) := by ring
  simp_rw [he, AddChar.map_add_eq_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

end Ostmann

end OAI
