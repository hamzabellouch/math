import Mathlib.Data.Int.ModEq
import OAI.NumberTheory.Ostmann.QuadraticCenter.DistinctQuadraticMoment

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter

theorem jacobi_affine_common_center {p m : ℕ} {h t : ℤ}
    (hcenter : (p:ℤ)∣h-(m:ℤ)*t) (x : ℤ) :
    jacobiSym ((m:ℤ)*x-h) p = jacobiSym (m:ℤ) p*jacobiSym (x-t) p := by
  rw [← jacobiSym.mul_left]
  apply jacobiSym.mod_left'
  apply Int.modEq_iff_dvd.mpr
  convert hcenter using 1
  ring

theorem commonCenter_multiplier_coprime {p m : ℕ} (hp : p.Prime)
    (hm : 0 < m) (hmp : m < p) : Nat.Coprime m p := by
  apply (hp.coprime_iff_not_dvd.mpr ?_).symm
  exact Nat.not_dvd_of_pos_of_lt hm hmp

def commonCenterOrientation (ε : ℕ → ℤ) (m p : ℕ) : ℤ :=
  ε p*jacobiSym (m:ℤ) p

theorem commonCenterOrientation_sign {ε : ℕ → ℤ} {m p : ℕ}
    (hε : ε p=1 ∨ ε p=-1) (hmp : Nat.Coprime m p) :
    commonCenterOrientation ε m p=1 ∨ commonCenterOrientation ε m p=-1 := by
  have hgcd : (m:ℤ).gcd p=1 := by simpa using hmp.gcd_eq_one
  have hJ := jacobiSym.eq_one_or_neg_one hgcd
  rcases hε with hε | hε <;> rcases hJ with hJ | hJ <;>
    simp [commonCenterOrientation,hε,hJ]

theorem commonCenter_oriented_jacobi {p m : ℕ} {ε : ℕ → ℤ} {h t : ℤ}
    (hmp : Nat.Coprime m p) (hcenter : (p:ℤ)∣h-(m:ℤ)*t) (x : ℤ) :
    commonCenterOrientation ε m p*jacobiSym ((m:ℤ)*x-h) p = ε p*jacobiSym (x-t) p := by
  have hgcd : (m:ℤ).gcd p=1 := by simpa using hmp.gcd_eq_one
  have hsq := jacobiSym.sq_one hgcd
  rw [commonCenterOrientation,jacobi_affine_common_center hcenter]
  calc
    _ = ε p*(jacobiSym (m:ℤ) p)^2*jacobiSym (x-t) p := by ring
    _ = _ := by rw [hsq]; ring

theorem commonCenter_oriented_jacobi_of_dvd {p m : ℕ} (hp : p.Prime)
    (hpm : p∣m) (ε : ℕ → ℤ) (h x : ℤ) :
    commonCenterOrientation ε m p*jacobiSym ((m:ℤ)*x-h) p = 0 := by
  have hnc : ¬Nat.Coprime m p := by
    intro hc
    exact (hp.coprime_iff_not_dvd.mp hc.symm) hpm
  have hJ : jacobiSym (m:ℤ) p=0 := jacobiSym.eq_zero_iff.mpr ⟨hp.ne_zero,by
    simpa only [Int.gcd_natCast_natCast] using hnc⟩
  simp [commonCenterOrientation,hJ]

end Ostmann.QuadraticCenter

end

end OAI
