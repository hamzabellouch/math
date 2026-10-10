import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.LaurentPlane

namespace OAI


                                           
section

namespace MaximalSeshadri.LaurentPlane
noncomputable section
variable {K A R : Type*} [CommRing K] [CommRing A] [CommRing R]

lemma map_unit_zpow (f : A →+* R) (a : Aˣ) (n : ℤ) :
    f (a ^ n : Aˣ) = ((Units.map f a) ^ n : Rˣ) := by
  change (((Units.map f.toMonoidHom) (a ^ n) : Rˣ) : R) = _
  exact congrArg Units.val (map_zpow (Units.map f.toMonoidHom) a n)

lemma lift_cone_left (k : K →+* R) (u v : Rˣ) (f : A →+* R)
    (x : Aˣ) (y : A) (hx : Units.map f x = u) (hy : f y = v)
    (z : ℤ × ℤ) (hz : 0 ≤ z.2) :
    f (↑(x ^ z.1) * y ^ z.2.toNat) = eval k u v (T z) := by
  rw [map_mul, map_pow, map_unit_zpow, hx, hy, eval_T, Units.val_mul]
  have he : z.2 = (z.2.toNat : ℤ) := (Int.toNat_of_nonneg hz).symm
  rw [he, zpow_natCast, Units.val_pow_eq_pow_val]
  simp [max_eq_left hz]

lemma lift_cone_right (k : K →+* R) (u v : Rˣ) (f : A →+* R)
    (x : A) (y : Aˣ) (hx : f x = u) (hy : Units.map f y = v)
    (z : ℤ × ℤ) (hz : 0 ≤ z.1) :
    f (x ^ z.1.toNat * ↑(y ^ z.2)) = eval k u v (T z) := by
  rw [map_mul, map_pow, map_unit_zpow, hx, hy, eval_T, Units.val_mul]
  have he : z.1 = (z.1.toNat : ℤ) := (Int.toNat_of_nonneg hz).symm
  rw [he, zpow_natCast, Units.val_pow_eq_pow_val]
  simp [max_eq_left hz]

lemma lift_cone_top (k : K →+* R) (u v : Rˣ) (f : A →+* R)
    (x : Aˣ) (y : A) (hx : Units.map f x = u * v⁻¹) (hy : f y = ↑(v⁻¹))
    (z : ℤ × ℤ) (hz : z.1 + z.2 ≤ 0) :
    f (↑(x ^ z.1) * y ^ (-(z.1 + z.2)).toNat) = eval k u v (T z) := by
  rw [map_mul, map_pow, map_unit_zpow, hx, hy, eval_T]
  have hn : ((-(z.1 + z.2)).toNat : ℤ) = -(z.1 + z.2) :=
    Int.toNat_of_nonneg (by omega)
  rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, hn, ← Units.val_mul]
  congr 1
  rw [mul_zpow, mul_assoc, ← zpow_add]
  have he : z.1 + -(z.1 + z.2) = -z.2 := by omega
  rw [he]
  simp

theorem finite_laurent_of_chart {P N M : Type*} [CommRing P]
    [AddCommGroup N] [AddCommGroup M] [Module P N] [Module R M]
    [Module.Finite P N] (k : K →+* R) (u v : Rˣ)
    (e : P →+* Ring K) (F : N →+ M)
    (hF : ∀ p n, F (p • n) = eval k u v (e p) • F n)
    (hclear : ∀ m : M, ∃ d : ℕ, ∃ n : N, (↑u * ↑v : R)^d • m = F n) :
    letI := Module.compHom M (eval k u v)
    Module.Finite (Ring K) M := by
  let := Module.compHom M (eval k u v)
  apply finite_of_clearing e F hF
  intro m
  obtain ⟨d,n,hn⟩ := hclear m
  refine ⟨T (-(d : ℤ),-(d : ℤ)),n,?_⟩
  change m = eval k u v (T (-(d : ℤ),-(d : ℤ))) • F n
  rw [eval_T, ← hn, ← mul_smul]
  have he : ↑(u ^ (-(d : ℤ)) * v ^ (-(d : ℤ))) * (↑u * ↑v : R)^d = 1 := by
    rw [← Units.val_mul, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
    suffices u ^ (-(d : ℤ)) * v ^ (-(d : ℤ)) * (u * v)^d = 1 by
      exact congrArg Units.val this
    rw [← mul_zpow, zpow_neg, zpow_natCast]
    exact inv_mul_cancel _
  rw [he, one_smul]

end
end MaximalSeshadri.LaurentPlane

end


end OAI
