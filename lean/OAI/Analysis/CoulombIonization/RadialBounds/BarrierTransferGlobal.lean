import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierTransferBarrier
import OAI.Analysis.CoulombIonization.Variational.FinitePotentialDecay

namespace OAI

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology
noncomputable section
namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

theorem barrier_transfer_global {a ρ p q : TFSpace → ℝ} {Z k r lam M P Q C : ℝ}
    (hr : 0 < r) (hlam : 0 ≤ lam) (hk : 0 ≤ k)
    (ha : Continuous a)
    (hρm : Measurable ρ) (hρi : Integrable ρ) (hM : 0 ≤ M)
    (hρn : ∀ x, 0 ≤ ρ x) (hρb : ∀ x, ρ x ≤ M)
    (hpm : Measurable p) (hpi : Integrable p) (hP : 0 ≤ P)
    (hpn : ∀ x, 0 ≤ p x) (hpb : ∀ x, p x ≤ P)
    (hqm : Measurable q) (hqi : Integrable q) (hQ : 0 ≤ Q)
    (hqn : ∀ x, 0 ≤ q x) (hqb : ∀ x, q x ≤ Q)
    (hw : WeakNuclearLowerOn univ Z (fun x => nuclearField Z x+a x)
      (fun x => innerSource r ρ p x+outerCoefficient r x*reaction k (nuclearField Z x+a x)))
    (hd : ∀ x, r ≤ ‖x‖ →
      4*Real.pi*ρ x ≤ reaction k (nuclearField Z x-tfPotential ρ x-lam)+4*Real.pi*q x)
    (hu : ∀ x, r ≤ ‖x‖ → nuclearField Z x+a x ≤ C/‖x‖^4) :
    ∀ x, nuclearField Z x+a x ≤ nuclearField Z x-tfPotential ρ x+
        tfPotential (fun y => p y+q y) x := by
  have hn : Tendsto (norm : TFSpace → ℝ) (comap norm (atTop : Filter ℝ)) atTop := tendsto_comap
  have hpdec := bounded_L1_potential_decay hn hρm hρi hρn hM hρb
  have hd0 : Tendsto (fun x : TFSpace => C/‖x‖^4-Z/‖x‖+tfPotential ρ x)
      (comap norm (atTop : Filter ℝ)) (𝓝 0) := by
    simpa only [sub_zero,zero_add, Function.comp_apply] using
      (((tendsto_pow_atTop (by norm_num : (4:ℕ) ≠ 0)).comp hn).const_div_atTop C).sub
        (hn.const_div_atTop Z) |>.add hpdec
  intro x
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨S,hS⟩ := eventually_atTop.mp (eventually_comap.mp (hd0.eventually (gt_mem_nhds hε)))
  let T := max (max S ‖x‖) (r+1)
  have hST : S ≤ T := (le_max_left S ‖x‖).trans (le_max_left _ _)
  have hxT : ‖x‖ ≤ T := (le_max_right S ‖x‖).trans (le_max_left _ _)
  have hrT : r < T := (lt_add_one r).trans_le (le_max_right _ _)
  have hT : 0 < T := hr.trans hrT
  apply barrier_transfer_ball hr hT hlam hk hε.le ha hρm hρi hM hρn hρb
    hpm hpi hP hpn hpb hqm hqi hQ hqn hqb hw (fun y _ hy => hd y hy) _ x
    (mem_closedBall_zero_iff.mpr hxT)
  intro y hy
  have hbd := hu y (hrT.le.trans_eq hy.symm)
  have hsmall := hS T hST y hy
  unfold nuclearField at hbd
  linarith
end CoulombBarrier

end

end OAI
