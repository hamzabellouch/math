import OAI.Probability.DilutedSpin.AveragedMatrixSelection
import OAI.Probability.DilutedSpin.ScheduledEnergyBound

namespace OAI

section
section
namespace DilutedSpinGlass.DepthAverage
open scoped BigOperators
variable {α : Type} [Fintype α] [DecidableEq α] {L : ℕ} [NeZero L]

lemma average_le_const (D : (α → Fin L) → Prop) (F : (α → Fin L) → ℝ)
    {B : ℝ} (hB : 0≤B) (hF : ∀ q, D q → F q≤B) : average D F≤B := by
  calc
    _ ≤ (depthLaw α L).expect (fun _ => B) := by
      apply FiniteLaw.expect_mono
      intro q
      split_ifs with hd
      · exact hF q hd
      · exact hB
    _ = _ := FiniteLaw.expect_const _ _

end DilutedSpinGlass.DepthAverage
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir Filter Set
open ReducedTopology
open scoped NNReal BigOperators Topology
noncomputable local instance scheduledSelectionDecidableEq (type : Type) :
    DecidableEq type := Classical.decEq type
variable {L p : ℕ}

/-- One chosen physical sequence works for EVERY finite depth-coordinate
alphabet and every assignment-dependent signed matrix experiment. In
particular passing to a proper child's topology does not reselect the
reservoir or its perturbation. The base case is the same scheduled family
as the multileaf step and regular child fiber estimates. -/
theorem scheduled_joint_selection (M : Model p) {C H : ℝ} (hC : 0≤C) (hH : 0≤H)
    (hθ : ∀ᵐ z ∂M.disorder.toMeasure, ∀ σ, |z.1 σ|≤C)
    (hh : ∀ᵐ h ∂M.field.toMeasure, |h|≤H)
    (hθi : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hhi : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    {ε : ℝ} (hε : 0<ε) :
    ∃ (Ns : ℕ → ℕ) (us : ℕ → Spec L×ℕ → ℝ), StrictMono Ns ∧
      (∀ n i, us n i ∈ Icc (probeLow i.2) (probeHigh i.2)) ∧
      (∀ n, ConcreteReservoir.increment (weights L) prior (gridExponents L) direction anchor M (Ns n) (us n)≤
        liminf (pressure M) atTop+ε) ∧
      (∀ η : ℝ, 0<η → ∀ t : ℝ, 0<t → ∀ᶠ n in atTop,
        DepthAverage.average (regularShapeDomain .leaf (L+1) η)
          (physicalScheduledEnergy M C H (Ns n+1) L (us n) .leaf)≤((L+1:ℕ):ℝ)⁻¹/η+t) ∧
      (∀ (α : Type) [Fintype α] [DecidableEq α]
          (D : (α → Fin (L+1)) → Prop)
          (S T : (α → Fin (L+1)) → PrescribedTree (L+1))
          (a : (Q : α → Fin (L+1)) → (S Q).Leaf)
          (k : (α → Fin (L+1)) → ℕ), (∀ Q, 0<k Q) →
          ∀ (q : (Q : α → Fin (L+1)) → Option (Fin (k Q)) → (T Q).Leaf)
            (denom : (α → Fin (L+1)) → ℝ),
          Tendsto (fun n => DepthAverage.average D (fun Q =>
            |physicalTreeMatrixCovariance (gridExponents L) (S Q) (a Q) M C H
              (Ns n+1) (us n) (T Q) (q Q)|/|denom Q|)) atTop (𝓝 0)) := by
  obtain ⟨Ns,us,hNs,hus,hinc,henergy,hmatrix⟩ := joint_grid_selection M hC hH hθ hh hθi hhi hε
  refine ⟨Ns,us,hNs,hus,hinc,?_,?_⟩
  · intro η hη t ht
    filter_upwards [henergy η hη t ht] with n hn
    apply DepthAverage.average_le_const _ _ (by positivity)
    intro Q hQ
    rw [physicalScheduledEnergy_leaf]
    exact hn (Q none) (by
      simp only [regularSingletonDepths,Finset.mem_filter,Finset.mem_univ,true_and]
      exact hQ.1.1 none)
  · intro α _ _ D S T a k hk q denom
    apply DepthAverage.tendsto_average_zero
    intro Q
    have hh := (hmatrix (S Q) (a Q) (k Q) (hk Q) (T Q) (q Q)).abs.div_const |denom Q|
    simpa only [abs_zero,zero_div] using hh

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
