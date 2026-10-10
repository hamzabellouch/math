import OAI.NumberTheory.Ostmann.Characters.AffineKernelCount
import OAI.NumberTheory.Ostmann.QuadraticCenter.FewKernelContradiction

namespace OAI

/-! # The large-sieve count and the kernel-population contradiction meet

No squarefree-kernel assignment or kernel-count bound is assumed here: both
are constructed from the actual biased affine values.
-/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem biased_affine_populations_impossible (P₀ : PublishedProgressionInput)
    (H : PublishedRealZeroInput P₀) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve)
    (Cpop : ℝ) (hCpop : 500 ≤ Cpop) (C : ℝ) (hM : MertensLowerBound C)
    (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    ∃ η L₀ : ℝ, 0 < η ∧ η ≤ 1 / 1000 ∧ 0 < L₀ ∧
      ∀ᶠ T : ℝ in atTop, ∀ (L J : ℝ) (P : Finset ℕ) (k Z M m : ℕ)
        (h : ℤ) (eS eT : ℕ → ℂ) (S U : Finset ℤ),
        T ^ (3 / 2 : ℝ) ≤ L → L₀ ≤ L → 2 ≤ k → (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
        0 < J → Real.exp T ≤ Cpop * T * J →
        J * Real.exp (-T / (k - 1 : ℕ)) ≤ P.card →
        Real.exp (3 * T / 5) ≤ P.card → (Z : ℝ) ≤ Real.exp (T + 1) →
        1 ≤ Z → 1 ≤ M → M ≤ Z ^ k → ((Z : ℝ) ^ k) ≤ Real.exp (2 * L) →
        (∀ p ∈ P, p.Prime) → (∀ p ∈ P, Odd p) → (∀ p ∈ P, p ≤ Z) →
        (∀ p ∈ P, ‖eS p‖ ≤ 1) → (∀ p ∈ P, ‖eT p‖ ≤ 1) →
        (∀ p ∈ P, T ≤ Real.log (p : ℝ)) → 4 * L ≤ (c / 2) * P.card * T →
        0 < m → (m : ℝ) ≤ Real.exp (η * L) → h.natAbs.Coprime m →
        (∀ x ∈ S, |(m : ℤ) * x - h| ≤ M) →
        (∀ x ∈ U, |(m : ℤ) * x - h| ≤ M) →
        (∀ x ∈ S, c ≤ ‖quadraticPrimeMean P eS ((m : ℤ) * x - h)‖) →
        (∀ x ∈ U, c ≤ ‖quadraticPrimeMean P eT ((m : ℤ) * x - h)‖) →
        (∀ x ∈ S, ∀ y ∈ S, |((x - y : ℤ) : ℝ)| ≤ Real.exp L) →
        (∀ x ∈ U, ∀ y ∈ U, |((x - y : ℤ) : ℝ)| ≤ Real.exp L) →
        (∀ x ∈ S, ∀ y ∈ U, (x - y).natAbs.Prime ∧
          kernelSplitCutoff η L < (x - y).natAbs) →
        a * Real.exp (L / 2) / L ^ 6 ≤ S.card →
        a * Real.exp (L / 2) / L ^ 6 ≤ U.card → False := by
  obtain ⟨η, L₀, hη, hηU, hL₀, hno⟩ := few_kernel_populations_impossible P₀ H hSiegel C hM a ha
  refine ⟨η, L₀, hη, hηU, hL₀, ?_⟩
  filter_upwards [eventual_affine_kernel_count sieve Cpop hCpop (η / 100) c (by positivity) hc] with T hcount
  intro L J P k Z M m h eS eT S U hTL hL hk hkU hJ hpop hcenter hsize hZU hZ hM1 hMZ hZL
    hP hodd hPZ heS heT hlogp hdiv hm hmU hred hboundS hboundU hbiasS hbiasU
    hspanS hspanU hcross hsizeS hsizeU
  obtain ⟨f, r, hfcard, hf⟩ := hcount L J P k Z M m h eS S hTL hk hkU hJ hpop hcenter
    hsize hZU hZ hM1 hMZ hZL hP hodd hPZ heS hlogp hdiv hboundS hbiasS
  obtain ⟨g, s, hgcard, hg⟩ := hcount L J P k Z M m h eT U hTL hk hkU hJ hpop hcenter
    hsize hZU hZ hM1 hMZ hZL hP hodd hPZ heT hlogp hdiv hboundU hbiasU
  exact hno L hL S U f g r s m h hm hmU hred hfcard hgcard
    (fun x hx => ⟨(hf x hx).1, (hf x hx).2.2.1, (hf x hx).2.2.2.1⟩)
    (fun x hx => ⟨(hg x hx).1, (hg x hx).2.2.1, (hg x hx).2.2.2.1⟩)
    hspanS hspanU hcross hsizeS hsizeU

end Ostmann

end OAI
