import OAI.NumberTheory.TwoPoint.Fourier.MinorArcEnergyKernel
import OAI.NumberTheory.TwoPoint.Fourier.MinorArcSignedKernel

namespace OAI

/-! The four-prime kernel in MRT (3.3), including arbitrary window lengths. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem minor_arc_prime_difference_kernel (P : Finset ℕ) (N : ℕ)
    (hP : ∀ p ∈ P, p ≤ N) (α V : ℝ) (hV : 0 ≤ V) :
    (∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P,
      minorArcGeometricBound V (α * ((p₁ : ℝ) + p₂ - p₃ - p₄))) ≤
      (Finset.addEnergy P P : ℝ) *
        ∑ n ∈ Icc (-(2 * (N : ℤ))) (2 * (N : ℤ)),
          minorArcGeometricBound V (α * (n : ℝ)) := by
  let S := (P ×ˢ P) ×ˢ (P ×ˢ P)
  let f : (ℕ × ℕ) × (ℕ × ℕ) → ℤ := fun v =>
    ((v.1.1 : ℤ) + v.1.2) - ((v.2.1 : ℤ) + v.2.2)
  have hmap : ∀ v ∈ S, f v ∈ Icc (-(2 * (N : ℤ))) (2 * (N : ℤ)) := by
    rintro ⟨⟨p, q⟩, ⟨r, s⟩⟩ hv
    obtain ⟨hpq, hrs⟩ := mem_product.mp hv
    obtain ⟨hp, hq⟩ := mem_product.mp hpq
    obtain ⟨hr, hs⟩ := mem_product.mp hrs
    have := hP p hp
    have := hP q hq
    have := hP r hr
    have := hP s hs
    apply mem_Icc.mpr
    dsimp [f]
    omega
  have he := minor_arc_fiber_sum S (Icc (-(2 * (N : ℤ))) (2 * (N : ℤ))) f
    (fun n => minorArcGeometricBound V (α * (n : ℝ)))
    (Finset.addEnergy P P : ℝ) hmap
    (fun n _ => minor_arc_geometric_nonneg hV _)
    (fun n _ => by
      have hh := (Nat.cast_le (α := ℝ)).mpr (minor_arc_prime_shifted_fiber P n)
      simpa only [S, f] using hh)
  convert he using 1
  dsimp [S, f]
  simp only [sum_product]
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro q hq
  apply sum_congr rfl
  intro r hr
  apply sum_congr rfl
  intro s hs
  congr 1
  push_cast
  ring

theorem minor_arc_prime_kernel_rational (P : Finset ℕ) (N : ℕ)
    (hP : ∀ p ∈ P, p ≤ N) (α V : ℝ) (hV : 0 ≤ V)
    (a : ℤ) (q : ℕ) (hq : 2 ≤ q) (hcop : IsCoprime (q : ℤ) a)
    (happrox : |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2) :
    (∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P,
      minorArcGeometricBound V (α * ((p₁ : ℝ) + p₂ - p₃ - p₄))) ≤
      (Finset.addEnergy P P : ℝ) *
        (2 * (3 * (2 * (N : ℝ) + 1) / q + 1) *
          (2 * V + 4 * (q : ℝ) * (1 + Real.log (q : ℝ)))) := by
  have he := minor_arc_prime_difference_kernel P N hP α V hV
  have hk := minor_arc_signed_kernel (2 * N) q α V a hq hV hcop happrox
  have hs : (∑ n ∈ Icc (-(2 * (N : ℤ))) (2 * (N : ℤ)),
      minorArcGeometricBound V (α * (n : ℝ))) =
      ∑ n ∈ Icc (-((2 * N : ℕ) : ℤ)) ((2 * N : ℕ) : ℤ),
        minorArcGeometricBound V ((n : ℝ) * α) := by
    simp only [Nat.cast_mul, Nat.cast_ofNat, mul_comm α]
  rw [hs] at he
  apply he.trans
  have hm := mul_le_mul_of_nonneg_left hk
    (Nat.cast_nonneg (Finset.addEnergy P P) : (0 : ℝ) ≤ _)
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hm

end TwoPointCorrelations

end OAI
