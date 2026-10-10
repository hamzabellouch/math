import OAI.Probability.DilutedSpin.JointGridSelection
import OAI.Probability.DilutedSpin.SpinRootData

namespace OAI

section
section
namespace DilutedSpinGlass.DepthAverage
open Filter
open scoped Topology BigOperators
variable {α : Type} [Fintype α] [DecidableEq α] {L : ℕ} [NeZero L]

/-- At each fixed grid, there are only finitely many depth assignments. Thus
the signed physical identity error can be averaged BEFORE the size limit. -/
theorem tendsto_average_zero (D : (α → Fin L) → Prop)
    (F : ℕ → (α → Fin L) → ℝ)
    (hF : ∀ q, Tendsto (fun n => F n q) atTop (𝓝 0)) :
    Tendsto (fun n => average D (F n)) atTop (𝓝 0) := by
  classical
  simp only [average_eq]
  have hs := tendsto_finsetSum (Finset.univ.filter D) (fun q _ => hF q)
  have hh := hs.div_const ((L:ℝ)^Fintype.card α)
  simpa only [Finset.sum_const_zero,zero_div] using hh

end DilutedSpinGlass.DepthAverage
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir Filter Set
open scoped NNReal BigOperators Topology
variable {α : Type} [Fintype α] [DecidableEq α] {L p : ℕ}

/-- The low-increment grid sequence simultaneously has its regular singleton
base case and a vanishing normalized regular-cube matrix error. The old tree,
target shape, labeling and charging denominator may all vary with the complete
depth assignment. This is the actual shared-root signed covariance, not an
absolute coefficient majorant or a diagonal restriction of two averages. -/
theorem joint_grid_averaged_selection (M : Model p) {C H : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hθ : ∀ᵐ z ∂M.disorder.toMeasure, ∀ σ, |z.1 σ| ≤ C)
    (hh : ∀ᵐ h ∂M.field.toMeasure, |h| ≤ H)
    (hθi : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hhi : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (Ns : ℕ → ℕ) (us : ℕ → Spec L×ℕ → ℝ), StrictMono Ns ∧
      (∀ n i, us n i ∈ Icc (probeLow i.2) (probeHigh i.2)) ∧
      (∀ n, ConcreteReservoir.increment (weights L) prior (gridExponents L) direction anchor M (Ns n) (us n) ≤
        liminf (pressure M) atTop+ε) ∧
      (∀ η : ℝ, 0 < η → ∀ t : ℝ, 0 < t → ∀ᶠ n in atTop,
        ∀ d ∈ regularSingletonDepths L η,
          physicalSingletonEnergy (gridExponents L) M C H (Ns n+1) (us n) d ≤
            ((L+1:ℕ):ℝ)⁻¹/η+t) ∧
      (∀ (D : (α → Fin (L+1)) → Prop)
          (S T : (α → Fin (L+1)) → PrescribedTree (L+1))
          (a : (Q : α → Fin (L+1)) → (S Q).Leaf)
          (k : (α → Fin (L+1)) → ℕ), (∀ Q, 0<k Q) →
          ∀ (q : (Q : α → Fin (L+1)) → Option (Fin (k Q)) → (T Q).Leaf)
            (denom : (α → Fin (L+1)) → ℝ),
          Tendsto (fun n => DepthAverage.average D (fun Q =>
            |physicalTreeMatrixCovariance (gridExponents L) (S Q) (a Q) M C H
              (Ns n+1) (us n) (T Q) (q Q)|/|denom Q|)) atTop (𝓝 0)) := by
  obtain ⟨Ns,us,hNs,hus,hinc,henergy,hmatrix⟩ := joint_grid_selection M hC hH hθ hh hθi hhi hε
  refine ⟨Ns,us,hNs,hus,hinc,henergy,?_⟩
  intro D S T a k hk q denom
  apply DepthAverage.tendsto_average_zero
  intro Q
  have hh := (hmatrix (S Q) (a Q) (k Q) (hk Q) (T Q) (q Q)).abs.div_const |denom Q|
  simpa only [abs_zero,zero_div] using hh

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
