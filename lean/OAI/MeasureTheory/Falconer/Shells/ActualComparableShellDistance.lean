import OAI.MeasureTheory.Falconer.Shells.ActualComparableShellRebin
import OAI.MeasureTheory.Falconer.Geometry.SeparatedDistanceMaximum

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal ContDiff
attribute [local instance] Classical.propDecidable

theorem uniform_actual_comparable_shell_distance {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hsΨ : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {sig : ℝ} (hsig : 0 < sig) (K o : ℕ) {J : ℕ} (hJ : 0 < J) :
    ∃ H : ℝ, 0 ≤ H ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (Q : Fin 2 → DyadicSquare), (∀ l, (Q l).side = 1) →
    ∀ (ρ : Fin 2 → Measure Plane) [∀ l, IsFiniteMeasure (ρ l)],
    (∀ l, ρ l (Q l).carrierᶜ = 0) →
    ∀ (m : ℝ → ℝ) (q a₀ t₀ a d n v : ℕ),
    0 < q → a₀ ≤ a+n → v ≤ t₀ → v ≤ N →
    ∀ (S : Fin 2 → Finset PolicyDescriptor) (k : Fin 2 → PolicyDescriptor → ℕ),
    (∀ l, remainingPolicyDescriptors (fun t => m t-(t:ℝ)/(N:ℝ)) N q a₀ t₀ a ⊆ S l) →
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, ∑ t ∈ S l, k l t ≤ K) →
    ∀ L : ℕ, (∀ l t, t ∈ S l → descriptorLength t ≤ L) →
    ∀ L₀ : ℝ, (v:ℝ)-(a+d:ℕ) = 2*L₀ → (L:ℝ) ≤ L₀ → 10*sig*(N:ℝ) ≤ L₀ →
    ∀ (lam : ℝ) (i : Fin 2 → ℕ) (hsp : Fin 2 → Plane → ℂ),
    (∀ l x, ‖hsp l x‖ ≤ 1) →
    ∀ A B : CellPath, A.length = a → B.length = a →
    let β := fun l => inheritedCircleSymbol (S l) id (k l) (Q l) (ρ l) (m)
      N (lam) sig J (i l) (hsp l)
    let D : Fin 2 → PositiveDistanceData := fun l =>
      ⟨Q l,ρ l,m,N,q,a+n,v,lam,sig,J,i l+1,[],[]⟩
    ‖∑ row ∈ sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B d,
      ∑ col ∈ sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B d,
        if ¬ angularNear (Q 0) (Q 1) (a+d) row col then
          ∫ x in angularLengthShell (a+n), angularStationarySpatialKernel (β 0) (β 1) o v Ψ x
            ∂angularFourCellMeasure (Q 0) (Q 1) (ρ 0) (ρ 1) row col
        else 0‖ₑ ≤
    ENNReal.ofReal H * binKernelConstant *
      ENNReal.ofReal ((((2:ℝ)^N)^(-m (a+n)))^4*(2:ℝ)^(-2*((v:ℝ)-(a+n:ℕ)))) *
      ((sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B n).card:ℝ≥0∞) *
      257025537024256 *
      (D 0).separatedMaximum (D 1) (sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B n) (a+n) := by
  obtain ⟨H,hH,N₀,h₀⟩ := uniform_actual_comparable_shell_rebin hΨ hsΨ hsig K o hJ
  refine ⟨H,hH,N₀,?_⟩
  intro N hN Q hQ ρ inst hcarry m q a₀ t₀ a d n v hq ha₀ ht hv S k hS hcard hK L hL
    L₀ hvh hLL hL₀ lam i hsp hspb A B hA hB
  let D : Fin 2 → PositiveDistanceData := fun l =>
    ⟨Q l,ρ l,m,N,q,a+n,v,lam,sig,J,i l+1,[],[]⟩
  have he := h₀ N hN Q hQ ρ hcarry (fun _ => m) q a₀ t₀ a d n v hq ha₀ ht hv
    S k hS hcard hK L hL L₀ hvh hLL hL₀ (fun _ => lam) i hsp hspb A B hA hB
  have hn : (D 0).normalization = (D 1).normalization := rfl
  have hk := PositiveDistanceData.rebinned_positive_kernel_max (D 0) (D 1) rfl hn A B n (a+n)
  have hc := PositiveDistanceData.separated_sum_le_maximum (D 0) (D 1) (hQ 0) (hQ 1) (a+n)
    (sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B n)
    (sourceProductVertices_subset _ _ _ _ _ _ a n hA hB)
  dsimp only at he ⊢
  rw [mul_assoc] at he
  have hh := he.trans (mul_le_mul_right hk (ENNReal.ofReal H))
  have hh' := hh.trans (mul_le_mul_right
    (mul_le_mul_right hc (binKernelConstant * ENNReal.ofReal
      ((D 0).levelMass^4*(2:ℝ)^(-2*((v:ℝ)-(a+n:ℕ)))))) (ENNReal.ofReal H))
  simpa only [D,PositiveDistanceData.levelMass,mul_assoc,Nat.cast_add] using hh'

end PlanarFalconer

end OAI
