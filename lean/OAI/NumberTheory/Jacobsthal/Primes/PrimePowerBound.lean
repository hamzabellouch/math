import OAI.NumberTheory.Jacobsthal.Harmonic.CommonFrequencyLift
import OAI.NumberTheory.Jacobsthal.Sieve.KloostermanPrimeExponent

namespace OAI

namespace Erdos970

section

namespace ErdosKloosterman.PrimePower

noncomputable def envelope (p a : ℕ) (h k : ℤ) : ℝ :=
  ((a+1 : ℕ) : ℝ)^2 * ((p^a : ℕ) : ℝ)^((3 : ℝ)/4) *
    ((Nat.gcd (p^a) (Int.gcd h k) : ℕ) : ℝ)^((1 : ℝ)/4)

theorem envelope_ge_primitive (p a : ℕ) [Fact p.Prime] (ha : 0 < a) (h k : ℤ) :
    4 * ((p^a : ℕ) : ℝ)^((3 : ℝ)/4) ≤ envelope p a h k := by
  have hg : 0 < Nat.gcd (p^a) (Int.gcd h k) :=
    Nat.gcd_pos_of_pos_left _ (pow_pos (Fact.out : p.Prime).pos a)
  have hg1 : (1 : ℝ) ≤ ((Nat.gcd (p^a) (Int.gcd h k) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hg)
  have hgp := Real.one_le_rpow hg1 (by norm_num : (0 : ℝ) ≤ 1/4)
  have ha2 : (2 : ℝ) ≤ ((a+1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ a+1)
  have hc : (4 : ℝ) ≤ ((a+1 : ℕ) : ℝ)^2 := by nlinarith
  unfold envelope
  calc
    _ ≤ ((a+1 : ℕ) : ℝ)^2 * ((p^a : ℕ) : ℝ)^((3 : ℝ)/4) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ ≤ _ := le_mul_of_one_le_right (by positivity) hgp

theorem quarter_scale (p Q g : ℝ) (hp : 0 < p) (hQ : 0 ≤ Q) (hg : 0 ≤ g) :
    p * (Q^((3 : ℝ)/4) * g^((1 : ℝ)/4)) =
      (p*Q)^((3 : ℝ)/4) * (p*g)^((1 : ℝ)/4) := by
  rw [Real.mul_rpow hp.le hQ, Real.mul_rpow hp.le hg]
  have he : p^((3 : ℝ)/4) * p^((1 : ℝ)/4) = p := by
    rw [← Real.rpow_add hp]
    norm_num
  calc
    _ = (p^((3 : ℝ)/4) * p^((1 : ℝ)/4)) *
        (Q^((3 : ℝ)/4) * g^((1 : ℝ)/4)) := by rw [he]
    _ = _ := by ring

theorem envelope_scale (p a : ℕ) [Fact p.Prime] (h k : ℤ) :
    (p : ℝ) * envelope p a h k ≤ envelope p (a+1) ((p : ℤ)*h) ((p : ℤ)*k) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hc : ((a+1 : ℕ) : ℝ)^2 ≤ ((a+1+1 : ℕ) : ℝ)^2 := by
    push_cast
    nlinarith [show (0 : ℝ) ≤ a from Nat.cast_nonneg a]
  unfold envelope
  rw [common_frequency_gcd, pow_succ' p a, Nat.cast_mul, Nat.cast_mul]
  calc
    _ = ((a+1 : ℕ) : ℝ)^2 * ((p : ℝ) *
        (((p^a : ℕ) : ℝ)^((3 : ℝ)/4) *
          ((Nat.gcd (p^a) (Int.gcd h k) : ℕ) : ℝ)^((1 : ℝ)/4))) := by ring
    _ = _ := by rw [quarter_scale _ _ _ hp (by positivity) (by positivity)]
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

end ErdosKloosterman.PrimePower

end

section

namespace ErdosKloosterman.PrimePower

private theorem prime_zero_envelope (p : ℕ) [Fact p.Prime] (h k : ℤ)
    (hh : (h : ZMod p) = 0) (hk : (k : ZMod p) = 0) :
    envelope p 1 h k = 4 * (p : ℝ) := by
  have hd : p ∣ Int.gcd h k := Int.dvd_gcd
    ((ZMod.intCast_zmod_eq_zero_iff_dvd h p).mp hh)
    ((ZMod.intCast_zmod_eq_zero_iff_dvd k p).mp hk)
  have hg := Nat.gcd_eq_left_iff_dvd.mpr hd
  unfold envelope
  rw [pow_one, hg]
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  calc
    _ = 4 * ((p : ℝ)^((3 : ℝ)/4) * (p : ℝ)^((1 : ℝ)/4)) := by norm_num; ring
    _ = _ := by rw [← Real.rpow_add hp]; norm_num

theorem prime_envelope_bound (p : ℕ) [Fact p.Prime] (h k : ℤ) :
    ‖standardSum p h k‖ ≤ envelope p 1 h k := by
  have primitive (hab : (h : ZMod p) ≠ 0 ∨ (k : ZMod p) ≠ 0) :
      ‖standardSum p h k‖ ≤ envelope p 1 h k := by
    calc
      _ ≤ 2 * (p : ℝ)^((3 : ℝ)/4) := standardSum_prime_bound p h k hab
      _ ≤ 4 * (p : ℝ)^((3 : ℝ)/4) := by
        nlinarith [Real.rpow_nonneg (Nat.cast_nonneg p) ((3 : ℝ)/4)]
      _ ≤ _ := by simpa only [pow_one] using envelope_ge_primitive p 1 (by decide) h k
  by_cases hh : (h : ZMod p) = 0
  · by_cases hk : (k : ZMod p) = 0
    · have he : standardSum p h k = (Fintype.card (ZMod p)ˣ : ℂ) := by
        simp only [standardSum, hh, hk, sum_zero_zero, ← Nat.card_eq_fintype_card]
      have hc : (Fintype.card (ZMod p)ˣ : ℝ) ≤ p := by
        have hc := Fintype.card_le_of_injective (fun u : (ZMod p)ˣ => (u : ZMod p))
          Units.val_injective
        simpa only [ZMod.card] using (show (Fintype.card (ZMod p)ˣ : ℝ) ≤
          Fintype.card (ZMod p) by exact_mod_cast hc)
      rw [he]
      calc
        _ = (Fintype.card (ZMod p)ˣ : ℝ) := by simp
        _ ≤ p := hc
        _ ≤ envelope p 1 h k := by
          rw [prime_zero_envelope p h k hh hk]
          nlinarith [show (0 : ℝ) ≤ p from Nat.cast_nonneg p]
    · exact primitive (Or.inr hk)
  · exact primitive (Or.inl hh)

theorem prime_power_envelope_bound (p : ℕ) [Fact p.Prime] :
    ∀ a : ℕ, 0 < a → ∀ h k : ℤ, ‖standardSum (p^a) h k‖ ≤ envelope p a h k := by
  intro a
  induction a with
  | zero => intro ha; omega
  | succ a ih =>
    intro ha h k
    by_cases haz : a = 0
    · subst a
      simpa only [Nat.zero_add, pow_one] using prime_envelope_bound p h k
    have ha0 : 0 < a := by omega
    by_cases hprimitive : (h : ZMod p) ≠ 0 ∨ (k : ZMod p) ≠ 0
    · exact (primitive_three_quarter_bound p (a+1) (by omega) h k hprimitive).trans
        (envelope_ge_primitive p (a+1) (by omega) h k)
    push Not at hprimitive
    obtain ⟨hh, hk⟩ := hprimitive
    obtain ⟨h', rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd h p).mp hh
    obtain ⟨k', rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd k p).mp hk
    rw [common_frequency_lift p a ha0, norm_mul]
    have hn : ‖(p : ℂ)‖ = (p : ℝ) := by simp
    rw [hn]
    exact (mul_le_mul_of_nonneg_left (ih ha0 h' k') (Nat.cast_nonneg p)).trans
      (envelope_scale p a h' k')

theorem standardSum_prime_power_bound (p a : ℕ) [Fact p.Prime] (ha : 1 ≤ a) (h k : ℤ) :
    ‖standardSum (p^a) h k‖ ≤ ((a+1 : ℕ) : ℝ)^2 * ((p^a : ℕ) : ℝ)^((3 : ℝ)/4) *
      ((Nat.gcd (p^a) (Int.gcd h k) : ℕ) : ℝ)^((1 : ℝ)/4) :=
  prime_power_envelope_bound p a ha h k

end ErdosKloosterman.PrimePower

end

end Erdos970

end OAI
