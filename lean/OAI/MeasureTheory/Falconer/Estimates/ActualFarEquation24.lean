import OAI.MeasureTheory.Falconer.Estimates.ActualComparableDepthSum
import OAI.MeasureTheory.Falconer.Angular.ActualFarStationaryReduction

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal ContDiff
attribute [local instance] Classical.propDecidable

theorem uniform_actual_far_equation24 {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hsΨ : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ t, Ψ t ≤ W)
    {sig T lam : ℝ} (hsig : 0 < sig) (K : ℕ) {J : ℕ} (hJ : 0 < J) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (Q : Fin 2 → DyadicSquare), (∀ l, (Q l).side = 1) →
    ∀ (ρ : Fin 2 → Measure Plane) [∀ l, IsFiniteMeasure (ρ l)],
    (∀ l, ρ l (Q l).carrierᶜ = 0) →
    ∀ (m : ℝ → ℝ) (q a₀ t₀ a d v : ℕ),
    0 < q → a₀ ≤ a → v ≤ t₀ → v ≤ N → a+d+5 < v →
    ∀ (S : Fin 2 → Finset PolicyDescriptor) (k : Fin 2 → PolicyDescriptor → ℕ),
    (∀ l, remainingPolicyDescriptors (fun t => m t-(t:ℝ)/(N:ℝ)) N q a₀ t₀ a ⊆ S l) →
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, ∑ t ∈ S l, k l t ≤ K) →
    ∀ L ≤ N, (∀ l t, t ∈ S l → descriptorLength t ≤ L) →
    ∀ L₀ : ℝ, (v:ℝ)-(a+d:ℕ) = 2*L₀ → (L:ℝ) ≤ L₀ → 10*sig*(N:ℝ) ≤ L₀ →
    ∀ (B₀ : ℕ) (δ : ℝ),
    (∀ l, RegularizedProfileData (Q l) (ρ l) N B₀ δ lam m) →
    ∀ (i : Fin 2 → ℕ) (hsp : Fin 2 → Plane → ℂ),
    (∀ l, Measurable (hsp l)) → (∀ l x, ‖hsp l x‖ ≤ 1) →
    ∀ A B : CellPath, A.length = a → B.length = a →
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
  obtain ⟨o,N₁,h₁⟩ := uniform_actual_far_stationary_reduction (T := T) (lam := lam)
    hsig K hΨ hpos hsΨ hW hΨW
  obtain ⟨C,hC,N₂,h₂⟩ := uniform_actual_comparable_depth_sum hΨ hsΨ hsig K o hJ
  refine ⟨C,hC,max N₁ N₂,?_⟩
  intro N hN Q hQ ρ inst hcarry m q a₀ t₀ a d v hq ha₀ ht hv hdepth S k hS hcard hK L hLN hL
    L₀ hvh hLL hL₀ B₀ δ hd i hsp hm hb A B hA hB
  let β := fun l => inheritedCircleSymbol (S l) id (k l) (Q l) (ρ l) m N lam sig J (i l) (hsp l)
  let M := fun p : ℝ => ((2:ℝ)^N)^(-m p)
  let original := angularCellContribution (Q 0) (Q 1) (ρ 0) (ρ 1) A B d a v Ψ
    (M a) (M a) (M (a+d)) (M (a+d)) (β 0) (β 1)
    (fun row col => ¬ angularNear (Q 0) (Q 1) (a+d) row col)
  let comparable := angularComparableFarContribution (Q 0) (Q 1) (ρ 0) (ρ 1) A B a d v (M a) (M a)
    (angularStationarySpatialKernel (β 0) (β 1) o v Ψ)
  have he := h₁ N ((le_max_left _ _).trans hN) S (fun _ => id) k hcard hK L hLN hL
    Q hQ ρ (fun _ => m) B₀ δ hd (fun _ => J) i hsp hm hb a (by omega)
    ![A,B] (by intro l; fin_cases l <;> assumption) d v L₀ (by exact_mod_cast hv) hvh hLL hL₀
  have he' : ‖original-comparable‖ ≤ ((2:ℝ)^N)^(-T) := by
    simpa only [original,comparable,β,M,Matrix.cons_val_zero,Matrix.cons_val_one,Nat.cast_add] using he
  have hc := h₂ N ((le_max_right _ _).trans hN) Q hQ ρ hcarry m q a₀ t₀ a d v hq ha₀ ht hv
    S k hS hcard hK L hL L₀ hvh hLL hL₀ B₀ δ lam hd (by omega) i hsp hm hb A B hA hB
  have hh := (norm_add_le (original-comparable) comparable).trans (add_le_add he' hc)
  rw [sub_add_cancel] at hh
  simpa only [original,β,M,add_comm] using hh

end PlanarFalconer

end OAI
