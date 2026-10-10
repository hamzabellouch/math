import OAI.MeasureTheory.Falconer.Angular.InheritedCircleRegularity
import OAI.MeasureTheory.Falconer.Fourier.InheritedSymbolMeasurability
import OAI.MeasureTheory.Falconer.Fourier.InheritedSymbolSupport

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff Topology

 theorem uniform_actual_symbol_derivatives {sig : ℝ} (hsig : 0 < sig) (K j : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {ι : Type} [DecidableEq ι],
    ∀ (S : Finset ι) (b : ι → PolicyDescriptor) (k : ι → ℕ),
    S.card ≤ (N+1)^3+1 → (∑ a ∈ S, k a) ≤ K →
    ∀ L : ℕ, (∀ a ∈ S, descriptorLength (b a) ≤ L) →
    ∀ Q : DyadicSquare, 0 < Q.side → ∀ (ρ : Measure Plane) (m : ℝ → ℝ)
    (lam : ℝ) (J i : ℕ) (h : Plane → ℂ) (x : Plane), ‖h x‖ ≤ 1 → ∀ θ : ℝ,
    ‖iteratedDeriv j (fun φ => inheritedCircleSymbol S b k Q ρ m N lam sig J i h x
      (sourceUnitDirection φ)) θ‖ ≤
      symbolDerivativeConstant (K+j)^(K+j) * sourceSymbolScale N sig L^j := by
  obtain ⟨N₀,h₀⟩ := uniform_inheritedMaskProduct_bound hsig K j
  refine ⟨N₀,?_⟩
  intro N hN ι inst S b k hcard hK L hL Q hQ ρ m lam J i h x hx θ
  rw [inheritedCircleSymbol_derivative_norm S b k Q hQ]
  apply (mul_le_mul_of_nonneg_right hx (norm_nonneg _)).trans
  rw [one_mul]
  exact h₀ N hN S b k hcard hK L hL Q hQ ρ m lam J i (fun _ => x) θ

 theorem actual_symbol_derivative_support {ι : Type*} (S : Finset ι)
    (b : ι → PolicyDescriptor) (k : ι → ℕ) (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ)
    (h : Plane → ℂ) (x : Plane) (j : ℕ) :
    tsupport (iteratedDeriv j (fun φ => inheritedCircleSymbol S b k Q ρ m N lam sig J i h x
      (sourceUnitDirection φ))) ⊆
    tsupport (iteratedDeriv j (inheritedMaskProduct S b k Q ρ m N lam sig J i (fun _ => x))) := by
  apply closure_mono
  intro θ hθ
  contrapose! hθ
  simp only [Function.mem_support,not_not] at hθ ⊢
  apply norm_eq_zero.mp
  rw [inheritedCircleSymbol_derivative_norm S b k Q hQ]
  change iteratedDeriv j (inheritedMaskProduct S b k Q ρ m N lam sig J i (fun _ => x)) θ = 0 at hθ
  rw [hθ,norm_zero,mul_zero]

 theorem uniform_actual_symbol_support {sig : ℝ} (hsig : 0 < sig) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {ι : Type} [DecidableEq ι],
    ∀ (S : Finset ι) (b : ι → PolicyDescriptor) (k : ι → ℕ),
    ∀ Q : DyadicSquare, Q.side = 1 → ∀ (ρ : Measure Plane) (m : ℝ → ℝ)
    (lam : ℝ) (i : ℕ) (h : Plane → ℂ) (x : Plane) (j : ℕ),
    ∀ a ∈ S, ValidDescriptor N (b a) → ∀ P ∈ occupiedAnchorPaths Q ρ (descriptorAnchor (b a)),
    x ∈ (Q.descendant P).carrier →
    tsupport (iteratedDeriv j (fun φ => inheritedCircleSymbol S b k Q ρ m N lam sig J i h x
      (sourceUnitDirection φ))) ⊆
      sourceUnitDirection ⁻¹' descriptorGoodSet Q ρ m N lam sig J (i+1) P (b a) := by
  obtain ⟨N₀,h₀⟩ := uniform_inheritedMaskProduct_support hsig hJ
  refine ⟨N₀,?_⟩
  intro N hN ι inst S b k Q hQ ρ m lam i h x j a ha hb P hP hx
  exact (actual_symbol_derivative_support S b k Q (by rw [hQ]; norm_num) ρ m N lam sig J i h x j).trans
    (h₀ N hN S b k Q hQ ρ m lam i (fun _ => x) j a ha hb P hP hx)

end PlanarFalconer

end OAI
