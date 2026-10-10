import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLiouvilleTheorem

namespace OAI

/-! On the actual Liouville prime tail, every prime is larger than the
allowed character modulus. Passing to the primitive character therefore
leaves the prime sum exactly unchanged. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma mrt_primitive_character_twist {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hq : 0<q) {p : ℕ} (hp : p.Prime) (hqp : q<p) (t : ℝ) :
    characterTwist χ.primitiveCharacter t p=characterTwist χ t p := by
  have hcop : p.Coprime q := hp.coprime_iff_not_dvd.mpr (by
    intro hd
    exact (not_le_of_gt hqp) (Nat.le_of_dvd hq hd))
  have he := χ.primitiveCharacter_apply_of_isCoprime hcop.isCoprime
  have he' : χ.primitiveCharacter (p:ZMod χ.conductor)=χ (p:ZMod q) := by
    simpa only [Int.cast_natCast] using he
  simp only [characterTwist,he']

lemma mrt_liouville_tail_above_modulus {X q : ℕ}
    (hX : 1≤Real.log (X:ℝ))
    (hq : (q:ℝ)≤(Real.log (X:ℝ))^(1/125:ℝ))
    {p : ℕ} (hp : p∈mrtLiouvillePrimeTail X) : q<p := by
  have hlower := (mrtPrimeBand_bounds (Real.exp_pos _).le (Nat.cast_nonneg X) hp).1
  have hpow : (Real.log (X:ℝ))^(1/125:ℝ)≤(Real.log (X:ℝ))^(3/4:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
  have hexp : (Real.log (X:ℝ))^(3/4:ℝ)<
      Real.exp ((Real.log (X:ℝ))^(3/4:ℝ)) := by
    linarith [Real.add_one_le_exp ((Real.log (X:ℝ))^(3/4:ℝ))]
  have hh : (q:ℝ)<p := lt_of_le_of_lt (hq.trans hpow) (hexp.trans hlower)
  exact_mod_cast hh

theorem mrt_liouville_tail_primitive {X q : ℕ} (χ : DirichletCharacter ℂ q)
    (hq : 0<q) (hX : 1≤Real.log (X:ℝ))
    (hqX : (q:ℝ)≤(Real.log (X:ℝ))^(1/125:ℝ)) (t : ℝ) :
    (∑p∈mrtLiouvillePrimeTail X,characterTwist χ.primitiveCharacter t p/(p:ℂ))=
      ∑p∈mrtLiouvillePrimeTail X,characterTwist χ t p/(p:ℂ) := by
  apply sum_congr rfl
  intro p hp
  rw [mrt_primitive_character_twist χ hq (mrtPrimeBand_prime hp)
    (mrt_liouville_tail_above_modulus hX hqX hp) t]

theorem mrt_liouville_short_of_primitive_prime_tail
    (hMRT : MRTShortExponentialInput) (K : ℝ)
    (hprime : ∀ᶠ X : ℕ in atTop, ∀ q : ℕ, 0<q →
      (q:ℝ)≤(Real.log (X:ℝ))^(1/125:ℝ) →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
      ∀ t : ℝ, |t|≤X → -K≤
        (∑p∈mrtLiouvillePrimeTail X,characterTwist χ t p/(p:ℂ)).re) :
    MRTLiouvilleShortInput := by
  apply mrt_liouville_short_of_distance hMRT
  apply mrt_liouville_distance_from_prime_tail K
  have hlog : Tendsto (fun X:ℕ => Real.log (X:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hprime,hlog.eventually (eventually_ge_atTop (1:ℝ))] with X hpr hX
  intro q hq hqX χ t ht
  let : NeZero q := ⟨Nat.ne_of_gt hq⟩
  have hc : 0<χ.conductor := Nat.pos_of_ne_zero χ.conductor_ne_zero
  have hcq : χ.conductor≤q := Nat.le_of_dvd hq χ.conductor_dvd_level
  have hcqr : (χ.conductor:ℝ)≤q := by exact_mod_cast hcq
  have hcX : (χ.conductor:ℝ)≤(Real.log (X:ℝ))^(1/125:ℝ) := hcqr.trans hqX
  have hh := hpr χ.conductor hc hcX χ.primitiveCharacter χ.primitiveCharacter_isPrimitive t ht
  rw [mrt_liouville_tail_primitive χ hq hX hqX t] at hh
  exact hh

end TwoPointCorrelations

end OAI
