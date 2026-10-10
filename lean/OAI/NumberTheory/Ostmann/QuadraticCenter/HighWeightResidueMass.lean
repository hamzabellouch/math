import OAI.NumberTheory.Ostmann.QuadraticCenter.HalfKernelRankin
import OAI.NumberTheory.Ostmann.Preliminaries.DivisibleResidueCount

namespace OAI

/-! # Residue-uniform high-weight mass via the small half kernels -/

namespace Ostmann

open scoped BigOperators

/-- The half-kernel construction converts the mass in one residue class into
a reciprocal squarefree sum. Its fibers are controlled uniformly in the residue. -/
theorem half_kernel_residue_mass (S : Finset ℕ) (N L a : ℕ)
    (hL : 0 < L) (hsize : 2 * L ^ 2 ≤ N)
    (hS : ∀ s ∈ S, Squarefree s)
    (hrange : ∀ s ∈ S, s ∈ Finset.Ioc N (2 * N))
    (hres : ∀ s ∈ S, Nat.ModEq L s a)
    (hcop : ∀ s ∈ S, L.Coprime s) (u : ℝ) (hu : 1 ≤ u) :
    (∑ s ∈ S, u ^ s.primeFactors.card) ≤
      (2 * u * N / L) * ∑ r ∈ S.image smallHalfKernel, (u ^ 2) ^ r.primeFactors.card / (r : ℝ) := by
  classical
  have hmaps (s : ℕ) (hs : s ∈ S) : smallHalfKernel s ∈ S.image smallHalfKernel :=
    Finset.mem_image_of_mem smallHalfKernel hs
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  obtain ⟨s₀, hs₀, heq₀⟩ := Finset.mem_image.mp hr
  have hspec₀ := smallHalfKernel_spec s₀ (hS s₀ hs₀)
  rw [heq₀] at hspec₀
  have hr0 : 0 < r := Nat.pos_of_ne_zero hspec₀.1.ne_zero
  have hcopr : L.Coprime r := (hcop s₀ hs₀).of_dvd_right hspec₀.2.1
  have hrN : r ^ 2 ≤ 2 * N := hspec₀.2.2.1.trans (Finset.mem_Ioc.mp (hrange s₀ hs₀)).2
  have hLr := half_kernel_modulus_le L N r hsize hrN
  let T := S.filter (fun s => smallHalfKernel s = r)
  have hsub : T ⊆ (Finset.Ioc N (2 * N)).filter (fun s => Nat.ModEq L s a ∧ r ∣ s) := by
    intro s hs
    obtain ⟨hs, heq⟩ := Finset.mem_filter.mp hs
    have hsp := smallHalfKernel_spec s (hS s hs)
    rw [heq] at hsp
    exact Finset.mem_filter.mpr ⟨hrange s hs, hres s hs, hsp.2.1⟩
  have hcard : (T.card : ℝ) ≤ 2 * (N : ℝ) / (L * r) :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (dyadic_divisible_residue_class_count N L r a hL hr0 hcopr hLr)
  have hweight (s : ℕ) (hs : s ∈ T) :
      u ^ s.primeFactors.card ≤ u * (u ^ 2) ^ r.primeFactors.card := by
    obtain ⟨hs, heq⟩ := Finset.mem_filter.mp hs
    have hsp := smallHalfKernel_spec s (hS s hs)
    rw [heq] at hsp
    exact half_kernel_weight s r hsp.2.2.2 u hu
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr0
  change (∑ s ∈ T, u ^ s.primeFactors.card) ≤ _
  calc
    _ ≤ ∑ _s ∈ T, u * (u ^ 2) ^ r.primeFactors.card := Finset.sum_le_sum hweight
    _ = (T.card : ℝ) * (u * (u ^ 2) ^ r.primeFactors.card) := by simp
    _ ≤ (2 * (N : ℝ) / (L * r)) * (u * (u ^ 2) ^ r.primeFactors.card) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by field_simp

/-- Rankin's parameter bounds the residue mass with its half-kernel,
congruence and multiplicity conditions. -/
theorem high_weight_residue_mass (S P : Finset ℕ) (N L a b : ℕ)
    (hL : 0 < L) (hsize : 2 * L ^ 2 ≤ N)
    (hS : ∀ s ∈ S, Squarefree s)
    (hrange : ∀ s ∈ S, s ∈ Finset.Ioc N (2 * N))
    (hres : ∀ s ∈ S, Nat.ModEq L s a) (hcop : ∀ s ∈ S, L.Coprime s)
    (hP : ∀ s ∈ S, (smallHalfKernel s).primeFactors ⊆ P)
    (hb : ∀ s ∈ S, b ≤ (smallHalfKernel s).primeFactors.card)
    (u t : ℝ) (hu : 1 ≤ u) (ht : 1 ≤ t) :
    (∑ s ∈ S, u ^ s.primeFactors.card) ≤
      (2 * u * N / L) * (t ^ b)⁻¹ *
        Real.exp (u ^ 2 * t * ∑ p ∈ P, (p : ℝ)⁻¹) := by
  have hu0 : 0 ≤ u := zero_le_one.trans hu
  apply (half_kernel_residue_mass S N L a hL hsize hS hrange hres hcop u hu).trans
  have hrank := high_weight_squarefree_reciprocal (S.image smallHalfKernel) P
    (by intro r hr; obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hr; exact (smallHalfKernel_spec s (hS s hs)).1)
    (by intro r hr; obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hr; exact hP s hs)
    (u ^ 2) t (sq_nonneg _) ht b
    (by intro r hr; obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hr; exact hb s hs)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hrank (by positivity : 0 ≤ 2 * u * N / L)

end Ostmann

end OAI
