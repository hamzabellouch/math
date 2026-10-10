import OAI.MeasureTheory.Falconer.Estimates.ActualFarEquation24
import OAI.MeasureTheory.Falconer.Estimates.ActualFarBuffer

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal ContDiff
attribute [local instance] Classical.propDecidable

theorem uniform_actual_far_equation24_source_buffer {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hsΨ : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ t, Ψ t ≤ W)
    {sig T lam : ℝ} (hsig : 0 < sig) (K : ℕ) {J : ℕ} (hJ : 0 < J) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (Q : Fin 2 → DyadicSquare), (∀ l, (Q l).side = 1) →
    ∀ (ρ : Fin 2 → Measure Plane) [∀ l, IsFiniteMeasure (ρ l)],
    (∀ l, ρ l (Q l).carrierᶜ = 0) →
    ∀ (m : ℝ → ℝ) (q a₀ t₀ a v : ℕ),
    0 < q → a₀ ≤ a → v ≤ t₀ → v ≤ N →
    ∀ (S : Fin 2 → Finset PolicyDescriptor) (k : Fin 2 → PolicyDescriptor → ℕ),
    (∀ l, remainingPolicyDescriptors (fun t => m t-(t:ℝ)/(N:ℝ)) N q a₀ t₀ a ⊆ S l) →
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, ∑ t ∈ S l, k l t ≤ K) →
    ∀ L ≤ N, (∀ l t, t ∈ S l → descriptorLength t ≤ L) →
    a < v-2*sourceFarBuffer N L sig →
    ∀ (B₀ : ℕ) (δ : ℝ),
    (∀ l, RegularizedProfileData (Q l) (ρ l) N B₀ δ lam m) →
    ∀ (i : Fin 2 → ℕ) (hsp : Fin 2 → Plane → ℂ),
    (∀ l, Measurable (hsp l)) → (∀ l x, ‖hsp l x‖ ≤ 1) →
    ∀ A B : CellPath, A.length = a → B.length = a →
    let d := v-2*sourceFarBuffer N L sig-a
    let β := fun l => inheritedCircleSymbol (S l) id (k l) (Q l) (ρ l) m N lam sig J (i l) (hsp l)
    let M := fun p : ℝ => ((2:ℝ)^N)^(-m p)
    let D : ℕ → Fin 2 → PositiveDistanceData := fun b l =>
      ⟨Q l,ρ l,m,N,q,b,v,lam,sig,J,i l+1,[],[]⟩
    ‖angularCellContribution (Q 0) (Q 1) (ρ 0) (ρ 1) A B d a v Ψ
      (M a) (M a) (M (a+d)) (M (a+d)) (β 0) (β 1)
      (fun row col => ¬ angularNear (Q 0) (Q 1) (a+d) row col)‖ ≤
    C * ∑ b ∈ Finset.Icc (a+9) (a+d+5),
      ((2:ℝ)^N)^(-2*(m b-(b:ℝ)/N-(m a-(a:ℝ)/N))+12*lam) *
        ((D b 0).separatedMaximum (D b 1)
          (sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B (b-a)) b).toReal +
      ((2:ℝ)^N)^(-T) := by
  obtain ⟨C,hC,N₁,h₁⟩ := uniform_actual_far_equation24 (T := T) (lam := lam)
    hΨ hpos hsΨ hW hΨW hsig K hJ
  obtain ⟨N₂,h₂⟩ := uniform_source_far_buffer hsig
  refine ⟨C,hC,max N₁ N₂,?_⟩
  intro N hN Q hQ ρ inst hcarry m q a₀ t₀ a v hq ha₀ ht hv S k hS hcard hK L hLN hL
    hbranch B₀ δ hd i hsp hm hb A B hA hB
  have hbuf := h₂ N ((le_max_right _ _).trans hN) L v a hbranch
  exact h₁ N ((le_max_left _ _).trans hN) Q hQ ρ hcarry m q a₀ t₀ a
    (v-2*sourceFarBuffer N L sig-a) v hq ha₀ ht hv hbuf.2.1 S k hS hcard hK L hLN hL
    (sourceFarBuffer N L sig) hbuf.2.2.1 hbuf.2.2.2.1 hbuf.2.2.2.2 B₀ δ hd i hsp hm hb A B hA hB

end PlanarFalconer

end OAI
