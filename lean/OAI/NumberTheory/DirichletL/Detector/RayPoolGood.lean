import OAI.NumberTheory.DirichletL.Detector.RaySlots

namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.ProbeRaySlots
open HeckeFamily ProbePhysical CanonicalQuadraticSieve PrincipalSignalComparison
local notation "Id" => Ideal HeckeFamily.O

theorem prime_coprime_of_norm_gt (η : Character) (P : PrimeIdeal)
    (hN : (η.modulus.absNorm:ℝ)<(P.val.absNorm:ℝ)) : IsCoprime P.val η.modulus := by
  apply Ideal.coprime_of_no_prime_ge
  intro J hPJ hηJ hJ
  have hmax := (Ideal.isPrime_of_prime P.property).isMaximal P.property.ne_zero
  have heq := hmax.eq_of_le hJ.ne_top hPJ
  rw [←heq] at hηJ
  have hd : P.val∣η.modulus := Ideal.dvd_iff_le.mpr hηJ
  have hn := Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot))
    (map_dvd Ideal.absNorm hd)
  exact (not_le_of_gt hN) (by exact_mod_cast hn)

theorem pool_eventually_target_coprime (C : Set Id) (S : Finset Id) (η : Character)
    (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ∀ᶠx : ℝ in atTop,∀P∈pool C S a b x,IsCoprime P.val η.modulus := by
  filter_upwards [eventually_gt_atTop ((η.modulus.absNorm:ℝ)/a),eventually_gt_atTop (0:ℝ)] with x hx hx0
  intro P hP
  apply prime_coprime_of_norm_gt η P
  exact ((div_lt_iff₀ ha).mp hx).trans (pool_norm_bounds C S ha.le hab hx0 P hP).1

theorem pool_eventually_target_unit_value (C : Set Id) (S : Finset Id) (η : Character)
    (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ∀ᶠx : ℝ in atTop,∀P∈pool C S a b x,‖idealCoeff η P.val‖=1 := by
  filter_upwards [pool_eventually_target_coprime C S η a b ha hab] with x hx
  intro P hP
  exact idealCoeff_norm_one_of_coprime η P.val P.property.ne_zero (hx P hP)

theorem pool_supported (C : Set Id) (S : Finset Id) (hS : SourceExclusions S)
    (a b x : ℝ) (P : PrimeIdeal) (hP : P∈pool C S a b x) : Supported P.val :=
  outside_prime_supported S hS.bad P ((mem_pool C S a b x P).mp hP).2.2.2

theorem pool_target_coprime_at_power (C : Set Id) (S : Finset Id) (η : Character)
    (a b ell : ℝ) (ha : 0<a) (hab : a≤b) (hell : 0<ell) :
    ∀ᶠZ : ℝ in atTop,∀P∈pool C S a b (Z^ell),IsCoprime P.val η.modulus :=
  (tendsto_rpow_atTop hell).eventually (pool_eventually_target_coprime C S η a b ha hab)

end SevenEighths.ProbeRaySlots
end

end OAI
