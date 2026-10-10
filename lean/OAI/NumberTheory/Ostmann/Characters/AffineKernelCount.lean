import OAI.NumberTheory.Ostmann.Characters.AffineKernelBias
import OAI.NumberTheory.Ostmann.Quadratic.KernelCountFromCenter

namespace OAI

/-! # The actual affine values have few distinct biased squarefree kernels -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem eventual_affine_kernel_count (sieve : PublishedQuadraticLargeSieve)
    (Cpop : ℝ) (hCpop : 500 ≤ Cpop)
    (ε c : ℝ) (hε : 0 < ε) (hc : 0 < c) :
    ∀ᶠ T : ℝ in atTop, ∀ (L J : ℝ) (P : Finset ℕ) (r Z M m : ℕ)
      (h : ℤ) (e : ℕ → ℂ) (S : Finset ℤ),
      T ^ (3 / 2 : ℝ) ≤ L → 2 ≤ r → (r : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      0 < J → Real.exp T ≤ Cpop * T * J →
      J * Real.exp (-T / (r - 1 : ℕ)) ≤ P.card →
      Real.exp (3 * T / 5) ≤ P.card → (Z : ℝ) ≤ Real.exp (T + 1) →
      1 ≤ Z → 1 ≤ M → M ≤ Z ^ r → ((Z : ℝ) ^ r) ≤ Real.exp (2 * L) →
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, Odd p) → (∀ p ∈ P, p ≤ Z) →
      (∀ p ∈ P, ‖e p‖ ≤ 1) → (∀ p ∈ P, T ≤ Real.log (p : ℝ)) →
      4 * L ≤ (c / 2) * P.card * T →
      (∀ x ∈ S, |(m : ℤ) * x - h| ≤ M) →
      (∀ x ∈ S, c ≤ ‖quadraticPrimeMean P e ((m : ℤ) * x - h)‖) →
      ∃ (kernel : ℤ → ℤ) (root : ℤ → ℕ),
        ((S.image kernel).card : ℝ) ≤ Real.exp (3 * ε * L) ∧
        ∀ x ∈ S, kernel x ≠ 0 ∧ 0 < root x ∧ Squarefree (kernel x).natAbs ∧
          kernel x * (root x : ℤ) ^ 2 = (m : ℤ) * x - h ∧
          c / 2 ≤ ‖quadraticPrimeMean P e (kernel x)‖ := by
  filter_upwards [eventual_kernel_count_from_commonCenter sieve Cpop hCpop ε (c / 2) hε (by positivity),
    eventually_ge_atTop (1 : ℝ)] with T hcount hT
  intro L J P r Z M m h e S hL hr hrU hJ hpop hcenter hsize hZU hZ hM hMS hS
    hP hodd hPZ he hlogp hdiscard hbound hbias
  have hcard : 0 < P.card := by
    have hh := (Real.exp_pos (3 * T / 5)).trans_le hsize
    exact_mod_cast hh
  have hMexp : (M : ℝ) ≤ Real.exp (2 * L) := (by exact_mod_cast hMS : (M : ℝ) ≤ (Z : ℝ) ^ r).trans hS
  have hb (x : ℤ) (hx : x ∈ S) : |(((m : ℤ) * x - h : ℤ) : ℝ)| ≤ Real.exp (2 * L) := by
    have hh : |(((m : ℤ) * x - h : ℤ) : ℝ)| ≤ M := by exact_mod_cast hbound x hx
    exact hh.trans hMexp
  obtain ⟨kernel, root, hkr⟩ := exists_biased_affine_kernels P hP S m h e c T (2 * L)
    hc (by linarith) hcard he hlogp (by linarith) hb hbias
  refine ⟨kernel, root, ?_, hkr⟩
  apply hcount L J P r Z M e (S.image kernel) hL hr hrU hJ hpop hcenter hsize hZU
    hZ hM hMS hS hP hodd hPZ he
  · intro u hu
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hu, ht, hsf, heq, _⟩ := hkr x hx
    exact signed_kernel_mem_range hu ht hsf heq (hbound x hx)
  · intro u hu
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    exact (hkr x hx).2.2.2.2

end Ostmann

end OAI
