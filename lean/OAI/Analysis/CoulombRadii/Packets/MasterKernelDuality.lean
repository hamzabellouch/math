import Mathlib
import OAI.Analysis.CoulombRadii.Packets.MasterKernel
import OAI.Analysis.CoulombRadii.FieldAnalysis.LipschitzTestEnergy

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology SchwartzMap
noncomputable section
namespace NeutralAtom

theorem master_kernel_coulomb_duality (g : 𝓢(Position,ℝ))
    (hg : ∀ x, 1<‖x‖ → g x=0) (hm : (∫ x, g x^2)=1) :
    ∃ C : ℝ, 0<C ∧ ∀ {c r₀ s : ℝ}, 0<c → 0<r₀ → 0<s →
    c*(1+packetExponent)*s^packetExponent≤1/4 →
    ∀ (y : Position) {Ω : Set Coulomb.Space} (_ : MeasurableSet Ω)
      [IsFiniteMeasure (volume.restrict Ω)] (σ : Coulomb.Space → ℝ),
    MemLp σ Coulomb.TFExponent (volume.restrict Ω) →
    (∀ z∉Ω, σ z=0) → Metric.closedBall y (4*packetWidth c r₀ s y)⊆Ω →
    (∫ z, σ z*packetKernel g c r₀ s z y)^2≤
      (C/(packetWidth c r₀ s y)^5)*Coulomb.coulombBilinear σ σ := by
  obtain ⟨B,hB,H⟩ := master_kernel_estimates g hg hm
  refine ⟨64*B^2,by positivity,?_⟩
  intro c r₀ s hc hr hs hq y Ω hΩ _ σ hσ hσs hball
  obtain ⟨hsp,hamp,hL,_,_⟩ := H hc hr hs hq y
  let t := packetWidth c r₀ s y
  have ht : 0<t := packetWidth_pos hc hr hs y
  have hK : ∀ z, 2*t<‖z-y‖ → packetKernel g c r₀ s z y=0 := by
    intro z hz
    by_contra hn
    have hh := hsp z hn
    rw [norm_sub_rev] at hh
    linarith
  have HH := Coulomb.raw_coulomb_lipschitz_test hΩ hσ hσs
    (show 0≤B/t^4 by positivity) (show 0<2*t by positivity) y hamp hK hL
    (by simpa only [t,show (2:ℝ)*(2*t)=4*t by ring] using hball)
  have he : (4*Real.pi)⁻¹*(3*(volume (Metric.closedBall y (2*(2*t)))).toReal*(B/t^4)^2)=
      (64*B^2)/t^5 := by
    rw [←Measure.real,Coulomb.volume_closedBall_three y (by positivity)]
    field_simp [ht.ne',Real.pi_ne_zero]
    ring
  rw [he,mul_comm] at HH
  exact HH

end NeutralAtom
end

end
end

end OAI
