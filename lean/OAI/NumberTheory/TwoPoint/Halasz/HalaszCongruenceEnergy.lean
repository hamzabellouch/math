import OAI.NumberTheory.TwoPoint.Halasz.HalaszFiberEnergy
import OAI.NumberTheory.TwoPoint.Halasz.HalaszCongruenceExponent

namespace OAI

/-! The mixed congruence count inserted into the finite energy inequality.
The trace `f` may contain further variables, provided those variables
vanish modulo the indicated prime powers. -/
namespace TwoPointCorrelations

open Finset Polynomial
open scoped Classical

theorem halasz_mixed_congruence_energy {ι : Type*} {p r k : ℕ} [Fact p.Prime]
    (hkp : k<p) (P : Fin k → (ZMod (p^(r+1)))[X])
    (hdeg : ∀ j, (P j).natDegree≤j.val+1)
    (hunit : ∀ j, IsUnit ((P j).coeff (j.val+1)))
    (F : Finset ι) (z : ι → Fin k → ZMod (p^(r+1)))
    (f : ι → Fin k → ℕ)
    (hnonsing : ∀ x∈F, Function.Injective
      (fun j => halaszPrimePowerReduction p r (z x j)))
    (hmod : ∀ x∈F, ∀ j,
      (∑ i, (P j).eval (z x i)).val % p^(min (j.val+1) (r+1)) =
        f x j % p^(min (j.val+1) (r+1))) :
    halaszFiberEnergy F f ≤
      (k^k * ∏ j : Fin k, p^(r+1-min (j.val+1) (r+1))) *
        halaszFiberEnergy F (fun x => (f x,z x)) := by
  apply halasz_fiber_energy_refine
  intro t _
  convert halasz_mixed_congruence_count hkp P hdeg hunit
    ((F.filter (fun x => f x=t)).image z)
    (fun j => t j % p^(min (j.val+1) (r+1))) ?_ ?_ using 1
  · congr 1
    ext y
    simp
  · intro y hy
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
    exact hnonsing x (mem_filter.mp hx).1
  · intro y hy j
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
    rw [hmod x (mem_filter.mp hx).1 j,(mem_filter.mp hx).2]

theorem halasz_mixed_congruence_energy_triangular {ι : Type*} {p r k : ℕ}
    [Fact p.Prime] (hkp : k<p) (hrk : r+1≤k)
    (P : Fin k → (ZMod (p^(r+1)))[X])
    (hdeg : ∀ j, (P j).natDegree≤j.val+1)
    (hunit : ∀ j, IsUnit ((P j).coeff (j.val+1)))
    (F : Finset ι) (z : ι → Fin k → ZMod (p^(r+1)))
    (f : ι → Fin k → ℕ)
    (hnonsing : ∀ x∈F, Function.Injective
      (fun j => halaszPrimePowerReduction p r (z x j)))
    (hmod : ∀ x∈F, ∀ j,
      (∑ i, (P j).eval (z x i)).val % p^(min (j.val+1) (r+1)) =
        f x j % p^(min (j.val+1) (r+1))) :
    halaszFiberEnergy F f ≤
      (k^k * p^((r+1)*r/2)) * halaszFiberEnergy F (fun x => (f x,z x)) := by
  have h := halasz_mixed_congruence_energy hkp P hdeg hunit F z f hnonsing hmod
  rw [halasz_congruence_digit_product hrk] at h
  simpa only [Nat.add_sub_cancel] using h

end TwoPointCorrelations

end OAI
