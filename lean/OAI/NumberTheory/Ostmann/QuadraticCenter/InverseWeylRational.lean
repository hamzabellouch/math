import OAI.NumberTheory.Ostmann.QuadraticCenter.InverseWeylPhase

namespace OAI

namespace Ostmann.QuadraticCenter

theorem rational_multiples_spacing (b : ℤ) (r : ℕ) (hr : 0 < r)
    (hcop : Int.gcd (r:ℤ) b = 1) (a d m : ℤ) (had : a ≠ d)
    (hshort : |a-d| < (r:ℤ)) :
    1/(r:ℝ) ≤ |((a:ℝ)-(d:ℝ))*(b:ℝ)/r-m| := by
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  let z : ℤ := (a-d)*b-m*r
  have hz : z ≠ 0 := by
    intro hz0
    have he : (a-d)*b = m*r := sub_eq_zero.mp hz0
    have hdiv : (r:ℤ) ∣ (a-d)*b := ⟨m, by simpa [mul_comm] using he⟩
    have hdiv' := Int.dvd_of_dvd_mul_left_of_gcd_one hdiv hcop
    have hle := Int.natAbs_le_of_dvd_ne_zero hdiv' (sub_ne_zero.mpr had)
    have hle' : (r:ℤ) ≤ |a-d| := by
      simpa only [Int.natCast_natAbs] using
        (show (r:ℤ) ≤ ((a-d).natAbs:ℤ) by exact_mod_cast hle)
    omega
  have hzR : (z:ℝ) = (((a:ℝ)-(d:ℝ))*(b:ℝ)/r-m)*(r:ℝ) := by
    dsimp [z]
    push_cast
    field_simp
  have hl : (1:ℝ) ≤ |(z:ℝ)| := by exact_mod_cast Int.one_le_abs hz
  apply (div_le_iff₀ hrR).mpr
  simpa only [hzR, abs_mul, abs_of_pos hrR] using hl

theorem approximated_multiples_spacing (theta : ℝ) (b : ℤ) (r : ℕ) (hr : 0 < r)
    (hcop : Int.gcd (r:ℤ) b = 1)
    (happrox : |theta-(b:ℝ)/r| ≤ 1/(r:ℝ)^2)
    (a d m : ℤ) (had : a ≠ d) (hshort : 2*|a-d| ≤ (r:ℤ)) :
    1/(2*(r:ℝ)) ≤ |theta*a-theta*d-m| := by
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hshort' : |a-d| < (r:ℤ) := by
    have hp : (0:ℤ) < |a-d| := abs_pos.mpr (sub_ne_zero.mpr had)
    omega
  have hshortR : 2*|(a:ℝ)-(d:ℝ)| ≤ (r:ℝ) := by exact_mod_cast hshort
  have hrat := rational_multiples_spacing b r hr hcop a d m had hshort'
  have heps : |((a:ℝ)-(d:ℝ))*(theta-(b:ℝ)/r)| ≤ 1/(2*(r:ℝ)) := by
    rw [abs_mul]
    calc
      _ ≤ |(a:ℝ)-(d:ℝ)| * (1/(r:ℝ)^2) :=
        mul_le_mul_of_nonneg_left happrox (abs_nonneg _)
      _ ≤ ((r:ℝ)/2)*(1/(r:ℝ)^2) := by gcongr; linarith
      _ = _ := by field_simp
  have hid : ((a:ℝ)-(d:ℝ))*(b:ℝ)/r-m =
      (theta*a-theta*d-m)-((a:ℝ)-(d:ℝ))*(theta-(b:ℝ)/r) := by ring
  rw [hid] at hrat
  have htri := abs_sub (theta*a-theta*d-m) (((a:ℝ)-(d:ℝ))*(theta-(b:ℝ)/r))
  have he : 1/(r:ℝ) = 2*(1/(2*(r:ℝ))) := by ring
  rw [he] at hrat
  linarith

end Ostmann.QuadraticCenter

end OAI
