import OAI.NumberTheory.Ostmann.Construction.OriginalKernelDecomposition
import OAI.NumberTheory.Ostmann.QuadraticCenter.SmallKernelFamily
import OAI.NumberTheory.Ostmann.QuadraticCenter.LargeKernelFamily

namespace OAI

/-! # Principal Fourier terms in finite frequency families -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem smallKernelParameters_principal (T : ℝ) (L : ℕ) :
    smallKernelParameters T L ⊆ principalQuadraticParameters T L := by
  intro i hi
  obtain ⟨hi, hp, _⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨hi, hp⟩

theorem squarefreeKernelSupport_card_le (L N : ℕ) :
    (squarefreeKernelSupport L N).card ≤ N := by
  apply (Finset.card_le_card (Finset.filter_subset _ _)).trans
  simp only [Nat.card_Icc]
  omega

theorem smallSquarefreeKernels_spec (L N s : ℕ) (hs : s ∈ smallSquarefreeKernels L N) :
    1 ≤ s ∧ s ≤ N ∧ Squarefree s ∧ s.Coprime L ∧ s ≤ L ^ 4 := by
  obtain ⟨hs, hsmall⟩ := Finset.mem_filter.mp hs
  exact ⟨(mem_squarefreeKernelSupport L N s).mp hs |>.1,
    (mem_squarefreeKernelSupport L N s).mp hs |>.2.1,
    (mem_squarefreeKernelSupport L N s).mp hs |>.2.2.1,
    (mem_squarefreeKernelSupport L N s).mp hs |>.2.2.2, hsmall⟩

theorem largeSquarefreeKernels_spec (L N s : ℕ) (hL : 2 ≤ L)
    (hs : s ∈ largeSquarefreeKernels L N) :
    1 ≤ s ∧ s ≤ N ∧ Squarefree s ∧ s.Coprime L ∧ 4 * L ^ 2 ≤ s := by
  obtain ⟨hs, hlarge⟩ := Finset.mem_filter.mp hs
  obtain ⟨hs1, hsN, hsf, hcp⟩ := (mem_squarefreeKernelSupport L N s).mp hs
  refine ⟨hs1, hsN, hsf, hcp, ?_⟩
  have hpow : 4 ≤ L ^ 2 := by nlinarith
  have hh : 4 * L ^ 2 ≤ L ^ 4 := by nlinarith [Nat.zero_le ((L ^ 2 - 4) * L ^ 2)]
  exact hh.trans (Nat.le_of_lt hlarge)

theorem filteredKernel_card_le (L N : ℕ) (pred : ℕ → Prop) [DecidablePred pred] :
    ((squarefreeKernelSupport L N).filter pred).card ≤ N :=
  (Finset.card_le_card (Finset.filter_subset _ _)).trans (squarefreeKernelSupport_card_le L N)

/-- One common index approximates both principal pieces. Its outer parameter
is one, and its scale remains in the small-kernel range. -/
theorem eventual_principalFourier_grid (H : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hH : 0 ≤ H) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (M N h₀ : ℕ) (θ R : ℝ),
      (Q.card : ℝ) ≤ T → (∀ p ∈ Q, 1000000 ≤ p) →
      (Q.toList.prod : ℝ) ≤ Real.exp T → Odd M → h₀ < Q.toList.prod →
      0 ≤ θ → θ ≤ 1 → 1 ≤ R → R ≤ Real.exp (14 * T) →
      (Q.toList.prod : ℝ) ^ 6 + Real.exp (-200 * T) ≤ R →
      (N : ℝ) ≤ Real.exp (14 * T) →
      ∃ i ∈ smallKernelParameters T Q.toList.prod,
        ‖principalSmallFourier Q hQ D M N h₀ θ R Φ -
          quadraticArrayStatistic (smallSquarefreeKernels Q.toList.prod N) M
            (fixedQuadraticCoefficient T Q hQ D Φ i)‖ ≤ Real.exp (-113 * T) ∧
        ‖principalLargeFourier Q hQ D M N h₀ θ R Φ -
          quadraticArrayStatistic (largeSquarefreeKernels Q.toList.prod N) M
            (fixedQuadraticCoefficient T Q hQ D Φ i)‖ ≤ Real.exp (-113 * T) := by
  filter_upwards [eventual_small_kernel_family_covers H Φ hH hΦ] with T hc
  intro Q hQ D M N h₀ θ R hcard hlarge hL hM hh₀ hθ0 hθ1 hR hRU hmargin hN
  obtain ⟨i, hi, he⟩ := hc Q hQ D M h₀ θ R hcard hlarge hL hM hh₀ hθ0 hθ1 hR hRU hmargin
  have happ (pred : ℕ → Prop) [DecidablePred pred] :
      ‖quadraticArrayStatistic ((squarefreeKernelSupport Q.toList.prod N).filter pred) M
          (arithmeticQuadraticCoefficient Q hQ D Φ R 1 M h₀ θ) -
        quadraticArrayStatistic ((squarefreeKernelSupport Q.toList.prod N).filter pred) M
          (fixedQuadraticCoefficient T Q hQ D Φ i)‖ ≤ Real.exp (-113 * T) := by
    apply quadraticArrayStatistic_grid_error
    · intro s hs
      exact (mem_squarefreeKernelSupport _ _ _ |>.mp (Finset.mem_filter.mp hs).1).1
    · exact (Nat.cast_le.mpr (filteredKernel_card_le _ _ pred)).trans hN
    · intro s hs
      obtain ⟨hs1, hsN, _⟩ := (mem_squarefreeKernelSupport _ _ _).mp (Finset.mem_filter.mp hs).1
      exact he s hs1 ((Nat.cast_le.mpr hsN).trans hN)
  exact ⟨i, hi, happ _, happ _⟩

end Ostmann

end OAI
