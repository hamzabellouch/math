import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.BarrierTransferPoissonBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

theorem barrier_transfer_ball {a ρ p q : TFSpace → ℝ} {Z k r S lam M P Q c : ℝ}
    (hr : 0 < r) (hS : 0 < S) (hlam : 0 ≤ lam) (hk : 0 ≤ k) (hc : 0 ≤ c)
    (ha : Continuous a)
    (hρm : Measurable ρ) (hρi : Integrable ρ) (hM : 0 ≤ M)
    (hρn : ∀ x, 0 ≤ ρ x) (hρb : ∀ x, ρ x ≤ M)
    (hpm : Measurable p) (hpi : Integrable p) (hP : 0 ≤ P)
    (hpn : ∀ x, 0 ≤ p x) (hpb : ∀ x, p x ≤ P)
    (hqm : Measurable q) (hqi : Integrable q) (hQ : 0 ≤ Q)
    (hqn : ∀ x, 0 ≤ q x) (hqb : ∀ x, q x ≤ Q)
    (hw : WeakNuclearLowerOn univ Z (fun x => nuclearField Z x+a x)
      (fun x => innerSource r ρ p x+outerCoefficient r x*reaction k (nuclearField Z x+a x)))
    (hd : ∀ x ∈ ball (0 : TFSpace) S, r ≤ ‖x‖ →
      4*Real.pi*ρ x ≤ reaction k (nuclearField Z x-tfPotential ρ x-lam)+4*Real.pi*q x)
    (hb : ∀ x : TFSpace, ‖x‖ = S → a x+tfPotential ρ x ≤ c) :
    ∀ x ∈ closedBall (0 : TFSpace) S,
      nuclearField Z x+a x ≤ nuclearField Z x-tfPotential ρ x+
        tfPotential (fun y => p y+q y) x+c := by
  let e : TFSpace → ℝ := fun x => p x+q x
  have hm : Measurable e := hpm.add hqm
  have hi : Integrable e := hpi.add hqi
  have hn : ∀ x, 0 ≤ e x := fun x => add_nonneg (hpn x) (hqn x)
  have hB : ∀ x, e x ≤ P+Q := fun x => add_le_add (hpb x) (hqb x)
  have heN (x : TFSpace) : 0 ≤ tfPotential e x := tfPotential_nonneg (ae_of_all _ hn) x
  have hp := (bounded_L1_potential_lipschitz hρm hρi hM hρn hρb).continuous
  have he := (bounded_L1_potential_lipschitz hm hi (add_nonneg hP hQ) hn hB).continuous
  have hcont : ContinuousOn (fun x => (nuclearField Z x+a x)-
      (nuclearField Z x-tfPotential ρ x)-tfPotential e x) (closedBall 0 S) := by
    convert ((ha.add hp).sub he).continuousOn using 1
    funext x
    simp only [Pi.sub_apply,Pi.add_apply]
    ring
  have hw' : WeakLaplacianLowerOn (ball 0 S)
      (fun x => (nuclearField Z x+a x)-(nuclearField Z x-tfPotential ρ x)-tfPotential e x)
      (fun x => outerCoefficient r x*(reaction k (nuclearField Z x+a x)-
        reaction k (nuclearField Z x-tfPotential ρ x-lam))) := by
    apply (barrier_transfer_weak hr ha hρm hρi hM hρn hρb
      hpm hpi hP hpn hpb hqm hqi hQ hqn hqb hw hd).congr_field
    intro x _
    ring
  have hcmp := monotone_reaction_comparison_ball hS hc hlam heN
    (outerCoefficient_nonneg r) (reaction_monotone hk) hcont (fun x hx => ?_) hw'
  · intro x hx
    have hh := hcmp x hx
    dsimp only [e] at hh
    linarith
  · linarith [hb x hx,heN x]

end CoulombBarrier

end

end OAI
