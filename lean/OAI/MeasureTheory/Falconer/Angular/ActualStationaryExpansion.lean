import OAI.MeasureTheory.Falconer.Angular.ActualStationaryAmplitude
import OAI.MeasureTheory.Falconer.Angular.StationaryRemainderScale

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

 theorem uniform_actual_symbol_derivatives_upto {sig : ℝ} (hsig : 0 < sig) (K n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {ι : Type} [DecidableEq ι],
    ∀ (S : Finset ι) (b : ι → PolicyDescriptor) (k : ι → ℕ),
    S.card ≤ (N+1)^3+1 → (∑ a ∈ S, k a) ≤ K →
    ∀ L : ℕ, (∀ a ∈ S, descriptorLength (b a) ≤ L) →
    ∀ Q : DyadicSquare, 0 < Q.side → ∀ (ρ : Measure Plane) (m : ℝ → ℝ)
    (lam : ℝ) (J i : ℕ) (h : Plane → ℂ) (x : Plane), ‖h x‖ ≤ 1 →
    ∀ j ≤ n, ∀ θ : ℝ,
    ‖iteratedDeriv j (fun φ => inheritedCircleSymbol S b k Q ρ m N lam sig J i h x
      (sourceUnitDirection φ)) θ‖ ≤ C * sourceSymbolScale N sig L^j := by
  choose N₀ h₀ using fun j => uniform_actual_symbol_derivatives hsig K j
  let C : ℝ := ∑ j ∈ Finset.range (n+1), symbolDerivativeConstant (K+j)^(K+j)
  have hCj (j : ℕ) : 0 ≤ symbolDerivativeConstant (K+j)^(K+j) :=
    pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le _)) _
  refine ⟨C,Finset.sum_nonneg (fun j _ => hCj j),(Finset.range (n+1)).sup N₀,?_⟩
  intro N hN ι inst S b k hcard hK L hL Q hQ ρ m lam J i h x hx j hj θ
  have hjmem : j ∈ Finset.range (n+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  have hNj : N₀ j ≤ N := (Finset.le_sup hjmem).trans hN
  apply (h₀ j N hNj S b k hcard hK L hL Q hQ ρ m lam J i h x hx θ).trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (sourceSymbolScale_pos _ _ _).le _)
  exact Finset.single_le_sum (fun l _ => hCj l) hjmem

 theorem uniform_actual_localized_stationary_expansion {sig : ℝ} (hsig : 0 < sig) (K n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {ι : Type} [DecidableEq ι],
    ∀ (S : Finset ι) (b : ι → PolicyDescriptor) (k : ι → ℕ),
    S.card ≤ (N+1)^3+1 → (∑ a ∈ S, k a) ≤ K →
    ∀ L : ℕ, (∀ a ∈ S, descriptorLength (b a) ≤ L) →
    ∀ Q : DyadicSquare, 0 < Q.side → ∀ (ρ : Measure Plane) (m : ℝ → ℝ)
    (lam : ℝ) (J i : ℕ) (h : Plane → ℂ) (x : Plane), ‖h x‖ ≤ 1 →
    ∀ Λ : ℝ, 0 < Λ →
    let f := fun φ => inheritedCircleSymbol S b k Q ρ m N lam sig J i h x (sourceUnitDirection φ)
    ‖localizedCircleIntegral Λ f - Complex.exp (Complex.I*(Λ:ℂ)) *
      (fresnelCoefficient (Λ/2) * stationaryDerivativeExpansion f n Λ)‖ ≤
    (Real.pi/(Λ/2))^(1/2:ℝ) *
      (A*sourceSymbolScale N sig L^2*(sourceSymbolScale N sig L^2/Λ)^(n+1)) := by
  obtain ⟨C,hC,N₀,h₀⟩ := uniform_actual_symbol_derivatives_upto hsig K (2*(n+1)+2)
  obtain ⟨A,hA,hbound⟩ := localized_stationary_ratio_remainder n
  refine ⟨A*C,mul_nonneg hA hC,N₀,?_⟩
  intro N hN ι inst S b k hcard hK L hL Q hQ ρ m lam J i h x hx Λ hΛ
  exact hbound (inheritedCircleSymbol_contDiff S b k Q hQ ρ m N lam sig J i h x)
    hΛ hC (sourceSymbolScale_one_le N hsig.le L)
    (h₀ N hN S b k hcard hK L hL Q hQ ρ m lam J i h x hx)

end PlanarFalconer

end OAI
