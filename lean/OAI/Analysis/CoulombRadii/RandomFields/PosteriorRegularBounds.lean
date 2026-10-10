import Mathlib
import OAI.Analysis.CoulombRadii.Variational.CorrectionDensity
import OAI.Analysis.CoulombRadii.RandomFields.ConditionalDensity

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom
section Fields
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A] {n : ℕ}
variable (P : Measure Ω) [IsFiniteMeasure P] (raw : Ω → Configuration n) (obs : Ω → A)
variable {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g)
variable (hm : (∫ z,g z^2)=1) {c r s : ℝ} (hc : 0<c) (hr : 0<r) (hs : 0<s)

include hg hgs hc hr hs
lemma conditionalPacketDensity_uniform_bounds :
    ∀ D : ℝ,∃ C : ℝ,∀ a x,x∈Metric.closedBall 0 D →
      |conditionalPacketDensity P raw obs g c r s a x|≤C := by
  obtain ⟨C,hC,hCb⟩ := conditionalPacketDensity_bounded P raw obs hg hgs hc hr hs
  exact fun D => ⟨C,fun a x _ => by
    rw [abs_of_nonneg (conditionalPacketDensity_nonneg P raw obs g hc hr hs a x)]
    exact hCb a x⟩

include hm
lemma conditionalPacketPotential_bounded : ∃ C : ℝ,0≤C ∧ ∀ a x,
    |potentialOf (conditionalPacketDensity P raw obs g c r s a) x|≤C := by
  obtain ⟨A,hA,hAb⟩ := conditionalPacketDensity_bounded P raw obs hg hgs hc hr hs
  refine ⟨A*kernelBallMass 1+n,add_nonneg (mul_nonneg hA (kernelBallMass_nonneg 1)) (Nat.cast_nonneg n),fun a x => ?_⟩
  rw [abs_of_nonneg (potentialOf_nonneg (conditionalPacketDensity_nonneg P raw obs g hc hr hs a) x)]
  have H := (potential_integrable_and_bound (x:=x) (mixturePacketDensity_integrable hg hm hc hr hs _)
    (conditionalPacketDensity_nonneg P raw obs g hc hr hs a) (by norm_num : (0:ℝ)<1)
    (fun y _ => hAb a y)).2
  change potentialOf (conditionalPacketDensity P raw obs g c r s a) x ≤
    A*kernelBallMass 1+1⁻¹*(∫ y,conditionalPacketDensity P raw obs g c r s a y) at H
  simpa only [inv_one,one_mul,conditionalPacketDensity_mass P raw obs hg hm hc hr hs] using H

lemma conditionalPacketOffset_uniform_bounds :
    ∀ D : ℝ,∃ C : ℝ,∀ a x,x∈Metric.closedBall 0 D →
      |-potentialOf (conditionalPacketDensity P raw obs g c r s a) x|≤C := by
  obtain ⟨C,hC,hCb⟩ := conditionalPacketPotential_bounded P raw obs hg hgs hm hc hr hs
  exact fun D => ⟨C,fun a x _ => by simpa only [abs_neg] using hCb a x⟩
end Fields
end NeutralAtom
end

end

end OAI
