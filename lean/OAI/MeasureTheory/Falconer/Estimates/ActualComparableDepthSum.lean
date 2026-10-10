import OAI.MeasureTheory.Falconer.Shells.ActualComparableShellNormalized
import OAI.MeasureTheory.Falconer.Angular.ActualStationarySpatialIntegrability
import OAI.MeasureTheory.Falconer.Estimates.ComparableContributionPartition

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal ContDiff
attribute [local instance] Classical.propDecidable

theorem uniform_actual_comparable_depth_sum {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hsΨ : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {sig : ℝ} (hsig : 0 < sig) (K o : ℕ) {J : ℕ} (hJ : 0 < J) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (Q : Fin 2 → DyadicSquare), (∀ l, (Q l).side = 1) →
    ∀ (ρ : Fin 2 → Measure Plane) [∀ l, IsFiniteMeasure (ρ l)],
    (∀ l, ρ l (Q l).carrierᶜ = 0) →
    ∀ (m : ℝ → ℝ) (q a₀ t₀ a d v : ℕ),
    0 < q → a₀ ≤ a → v ≤ t₀ → v ≤ N →
    ∀ (S : Fin 2 → Finset PolicyDescriptor) (k : Fin 2 → PolicyDescriptor → ℕ),
    (∀ l, remainingPolicyDescriptors (fun t => m t-(t:ℝ)/(N:ℝ)) N q a₀ t₀ a ⊆ S l) →
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, ∑ t ∈ S l, k l t ≤ K) →
    ∀ L : ℕ, (∀ l t, t ∈ S l → descriptorLength t ≤ L) →
    ∀ L₀ : ℝ, (v:ℝ)-(a+d:ℕ) = 2*L₀ → (L:ℝ) ≤ L₀ → 10*sig*(N:ℝ) ≤ L₀ →
    ∀ (B₀ : ℕ) (δ lam : ℝ),
    (∀ l, RegularizedProfileData (Q l) (ρ l) N B₀ δ lam m) → a+d+5 ≤ N →
    ∀ (i : Fin 2 → ℕ) (hsp : Fin 2 → Plane → ℂ),
    (∀ l, Measurable (hsp l)) → (∀ l x, ‖hsp l x‖ ≤ 1) →
    ∀ A B : CellPath, A.length = a → B.length = a →
    let β := fun l => inheritedCircleSymbol (S l) id (k l) (Q l) (ρ l) m N lam sig J (i l) (hsp l)
    let M := ((2:ℝ)^N)^(-m a)
    let D : ℕ → Fin 2 → PositiveDistanceData := fun b l =>
      ⟨Q l,ρ l,m,N,q,b,v,lam,sig,J,i l+1,[],[]⟩
    ‖angularComparableFarContribution (Q 0) (Q 1) (ρ 0) (ρ 1) A B a d v M M
      (angularStationarySpatialKernel (β 0) (β 1) o v Ψ)‖ ≤
    C * ∑ b ∈ Finset.Icc (a+9) (a+d+5),
      ((2:ℝ)^N)^(-2*(m b-(b:ℝ)/N-(m a-(a:ℝ)/N))+12*lam) *
        ((D b 0).separatedMaximum (D b 1)
          (sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B (b-a)) b).toReal := by
  obtain ⟨C,hC,N₁,h₁⟩ := uniform_actual_comparable_shell_normalized hΨ hsΨ hsig K o hJ
  obtain ⟨N₂,h₂⟩ := uniform_actual_far_stationary_integrable hΨ hsΨ hsig K o
  refine ⟨C,hC,max N₁ N₂,?_⟩
  intro N hN Q hQ ρ inst hcarry m q a₀ t₀ a d v hq ha₀ ht hv S k hS hcard hK L hL
    L₀ hvh hLL hL₀ B₀ δ lam hd hp i hsp hm hb A B hA hB
  let β := fun l => inheritedCircleSymbol (S l) id (k l) (Q l) (ρ l) m N lam sig J (i l) (hsp l)
  let M := ((2:ℝ)^N)^(-m a)
  have hQp (l : Fin 2) : 0 < (Q l).side := by rw [hQ l]; exact zero_lt_one
  have hint (row : CellPath × CellPath) (hr : row ∈ sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B d)
      (col : CellPath × CellPath) (hc : col ∈ sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B d)
      (hf : ¬ angularNear (Q 0) (Q 1) (a+d) row col) :
      IntegrableOn (angularStationarySpatialKernel (β 0) (β 1) o v Ψ) angularLengthComparable
        (angularFourCellMeasure (Q 0) (Q 1) (ρ 0) (ρ 1) row col) := by
    exact h₂ N ((le_max_right _ _).trans hN) S (fun _ => id) k hcard hK L hL Q hQp ρ
      (fun _ => m) (fun _ => lam) (fun _ => J) i hsp hm hb v (a+d:ℕ) L₀ hvh hLL hL₀
      (angularFourCellMeasure (Q 0) (Q 1) (ρ 0) (ρ 1) row col) angularLengthComparable
      (angular_comparable_far_ae (Q 0) (Q 1) (hQ 0) (hQ 1) (ρ 0) (ρ 1) (a+d) row col
        (sourceProductVertices_subset _ _ _ _ _ _ a d hA hB hr)
        (sourceProductVertices_subset _ _ _ _ _ _ a d hA hB hc) hf)
  dsimp only
  rw [angular_comparable_contribution_partition (Q 0) (Q 1) (hQ 0) (hQ 1) (ρ 0) (ρ 1)
    A B a d hA hB v M M _ hint,Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro b hbdepth
  have hba : a ≤ b := by have := (Finset.mem_Icc.mp hbdepth).1; omega
  have heq : a+(b-a) = b := Nat.add_sub_of_le hba
  have hbN : b ≤ N := (Finset.mem_Icc.mp hbdepth).2.trans hp
  have hs := h₁ N ((le_max_left _ _).trans hN) Q hQ ρ hcarry m q a₀ t₀ a d (b-a) v
    hq (by omega) ht hv S k hS hcard hK L hL L₀ hvh hLL hL₀ B₀ δ lam hd
    (by omega) i hsp hb A B hA hB
  have hpow : M^2*M^2 = M^4 := by rw [← pow_add]
  simpa only [← Nat.cast_add,heq,hpow,M,β,mul_assoc] using hs

end PlanarFalconer

end OAI
