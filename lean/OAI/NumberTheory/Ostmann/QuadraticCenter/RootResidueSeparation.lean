import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Image
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticKernelSeparation

namespace OAI

/-! # Scaled root populations have disjoint residues at split primes -/

namespace Ostmann

theorem kernel_roots_separated_mod_prime {p : ℕ} [Fact p.Prime]
    (m : ℕ) (h x y u v s t : ℤ) (c : ZMod p)
    (hpm : ¬p ∣ m)
    (hx : u * s ^ 2 = (m : ℤ) * x - h)
    (hy : v * t ^ 2 = (m : ℤ) * y - h)
    (hc : (u : ZMod p) * c ^ 2 = (v : ZMod p))
    (hprime : (x - y).natAbs.Prime) (hsmall : p < (x - y).natAbs) :
    (s : ZMod p) ≠ c * (t : ZMod p) := by
  intro hs
  have hm0 : (m : ZMod p) ≠ 0 := by
    intro hm
    exact hpm ((ZMod.natCast_eq_zero_iff m p).mp hm)
  have hx' : (u : ZMod p) * (s : ZMod p) ^ 2 =
      (m : ZMod p) * (x : ZMod p) - (h : ZMod p) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ZMod p)) hx
  have hy' : (v : ZMod p) * (t : ZMod p) ^ 2 =
      (m : ZMod p) * (y : ZMod p) - (h : ZMod p) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ZMod p)) hy
  have heq : (u : ZMod p) * (s : ZMod p) ^ 2 =
      (v : ZMod p) * (t : ZMod p) ^ 2 := by
    rw [hs, mul_pow, ← mul_assoc, hc]
  have hxy : (m : ZMod p) * ((x : ZMod p) - (y : ZMod p)) = 0 := by
    linear_combination -hx' + hy' + heq
  have hd0 : ((x - y : ℤ) : ZMod p) = 0 := by
    simpa only [Int.cast_sub] using (mul_eq_zero.mp hxy).resolve_left hm0
  have hd : (p : ℤ) ∣ x - y := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hd0
  have hdn : p ∣ (x - y).natAbs :=
    Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hd)
  have heq' : p = (x - y).natAbs :=
    (hprime.eq_one_or_self_of_dvd p hdn).resolve_left (Fact.out : p.Prime).ne_one
  omega

theorem kernel_root_images_disjoint {p : ℕ} [Fact p.Prime]
    (S T : Finset ℤ) (rootS rootT : ℤ → ℤ) (m : ℕ) (h u v : ℤ) (c : ZMod p)
    (hpm : ¬p ∣ m)
    (hS : ∀ x ∈ S, u * rootS x ^ 2 = (m : ℤ) * x - h)
    (hT : ∀ y ∈ T, v * rootT y ^ 2 = (m : ℤ) * y - h)
    (hc : (u : ZMod p) * c ^ 2 = (v : ZMod p))
    (hprime : ∀ x ∈ S, ∀ y ∈ T, (x - y).natAbs.Prime)
    (hsmall : ∀ x ∈ S, ∀ y ∈ T, p < (x - y).natAbs) :
    Disjoint (S.image (fun x => (rootS x : ZMod p)))
      (T.image (fun y => c * (rootT y : ZMod p))) := by
  classical
  apply Finset.disjoint_left.mpr
  intro z hzS hzT
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hzS
  obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hzT
  exact kernel_roots_separated_mod_prime m h x y u v (rootS x) (rootT y) c hpm
    (hS x hx) (hT y hy) hc (hprime x hx y hy) (hsmall x hx y hy) hxy.symm

end Ostmann

end OAI
