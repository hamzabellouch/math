import OAI.NumberTheory.Ostmann.Quadratic.QuadraticKernelSeparation
import OAI.NumberTheory.Ostmann.Arithmetic.UnitSquareRoots

namespace OAI

/-! # Unit residue constraints imposed by a reduced common center -/

namespace Ostmann

open scoped Classical

theorem kernel_root_coprime (m t : ℕ) (h x u : ℤ)
    (hred : h.natAbs.Coprime m) (heq : u * (t : ℤ) ^ 2 = (m : ℤ) * x - h) :
    t.Coprime m := by
  apply Nat.coprime_of_dvd
  intro p hp hpt hpm
  have hpt' : (p : ℤ) ∣ (t : ℤ) := Int.natCast_dvd_natCast.mpr hpt
  have hpm' : (p : ℤ) ∣ (m : ℤ) := Int.natCast_dvd_natCast.mpr hpm
  have hpterm : (p : ℤ) ∣ u * (t : ℤ) ^ 2 :=
    dvd_mul_of_dvd_right (dvd_pow hpt' (by omega)) u
  have hph : (p : ℤ) ∣ h := by
    have hd := dvd_sub (dvd_mul_of_dvd_left hpm' x) hpterm
    convert hd using 1
    linear_combination heq
  have hph' : p ∣ h.natAbs := Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hph)
  exact hp.not_dvd_one (hred ▸ Nat.dvd_gcd hph' hpm)

theorem kernel_coefficient_coprime (m : ℕ) (h x u t : ℤ)
    (hred : h.natAbs.Coprime m) (heq : u * t ^ 2 = (m : ℤ) * x - h) :
    u.natAbs.Coprime m := by
  apply Nat.coprime_of_dvd
  intro p hp hpu hpm
  exact kernel_prime_not_dvd_denominator m h x u t hred heq hp hpu hpm

theorem intCast_isUnit_of_natAbs_coprime (m : ℕ) (u : ℤ)
    (hc : u.natAbs.Coprime m) : IsUnit (u : ZMod m) := by
  have ha : IsUnit (u.natAbs : ZMod m) := (ZMod.unitOfCoprime u.natAbs hc).isUnit
  have habs : ((u.natAbs : ℤ) : ZMod m) = (u.natAbs : ZMod m) := by simp
  rcases le_total 0 u with hu | hu
  · have heq : (u.natAbs : ℤ) = u := by rw [Int.natCast_natAbs, abs_of_nonneg hu]
    rw [← heq, habs]
    exact ha
  · have heq : (u.natAbs : ℤ) = -u := by rw [Int.natCast_natAbs, abs_of_nonpos hu]
    have heq' : (u.natAbs : ZMod m) = -(u : ZMod m) := by
      rw [← habs, heq, Int.cast_neg]
    rw [heq'] at ha
    simpa using ha.neg

theorem kernel_square_residues (S : Finset ℤ) (root : ℤ → ℕ)
    (m : ℕ) (h u : ℤ) (hred : h.natAbs.Coprime m) (hS : S.Nonempty)
    (hroot : ∀ x ∈ S, u * (root x : ℤ) ^ 2 = (m : ℤ) * x - h) :
    ∃ a : (ZMod m)ˣ, ∀ x ∈ S,
      (root x).Coprime m ∧ (root x : ZMod m) ^ 2 = (a : ZMod m) := by
  obtain ⟨x0, hx0⟩ := hS
  have ht0 := kernel_root_coprime m (root x0) h x0 u hred (hroot x0 hx0)
  let a := (ZMod.unitOfCoprime (root x0) ht0) ^ 2
  refine ⟨a, fun x hx => ⟨kernel_root_coprime m (root x) h x u hred (hroot x hx), ?_⟩⟩
  have hu := intCast_isUnit_of_natAbs_coprime m u
    (kernel_coefficient_coprime m h x0 u (root x0) hred (hroot x0 hx0))
  have h1 := congrArg (fun z : ℤ => (z : ZMod m)) (hroot x hx)
  have h0 := congrArg (fun z : ℤ => (z : ZMod m)) (hroot x0 hx0)
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_sub,
    ZMod.natCast_self, zero_mul, zero_sub] at h1 h0
  have heq : (root x : ZMod m) ^ 2 = (root x0 : ZMod m) ^ 2 :=
    hu.mul_left_cancel (h1.trans h0.symm)
  simpa [a] using heq

end Ostmann

end OAI
