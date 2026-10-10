import Mathlib
import OAI.Analysis.CoulombRadii.Packets.BandOscillation
import OAI.Analysis.CoulombRadii.RandomFields.PosteriorSpatialCap

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical SchwartzMap
noncomputable section
namespace NeutralAtom

theorem posterior_count_cap_oscillation {B K : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K) :
    ∃ C : ℝ,0 < C ∧ ∀ {Ω Data : Type*} [MeasurableSpace Ω] [MeasurableSpace Data] {n : ℕ}
      (P : Measure Ω) [IsFiniteMeasure P] (raw : Ω → Configuration n) (obs : Ω → Data)
      (g : Position → ℝ),Continuous g → HasCompactSupport g → (∫ z,g z^2)=1 →
      ∀ {c r₀ s : ℝ},0 < c → 0 < r₀ → 0 < s → ∀ (datum : Data) (Z r L τ : ℝ),
      0 < r → 1 ≤ L → 0 < τ → τ ≤ r →
      (∀ y,r/2 ≤ ‖y‖ → ‖y‖ ≤ 8*L*r →
        conditionalPacketDensity P raw obs g c r₀ s datum y ≤ (B/τ^3)*(K/r^3)) →
      (∀ y,3*r/4 ≤ ‖y‖ → ‖y‖ ≤ 6*L*r →
        ‖y‖^4*(Z*coulombKernel y-potentialOf
          (conditionalPacketDensity P raw obs g c r₀ s datum) y) ≤ physicalSpatialCap) →
      ∀ y z : Position,r ≤ ‖y‖ → ‖y‖ ≤ 4*L*r → ‖z-y‖ ≤ r/16 →
        let F := fun x => Z*coulombKernel x-potentialOf (conditionalPacketDensity P raw obs g c r₀ s datum) x
        ‖F z-F y‖ ≤ C*(‖z-y‖/r)*((r/τ)^3/r^4+max (-F y) 0) := by
  obtain ⟨C,hC,H⟩ := atomic_band_negative_oscillation (mul_nonneg hB hK)
    (by have := physicalSpatialCap_pos; positivity : 0 ≤ 16*physicalSpatialCap)
  refine ⟨C,hC,?_⟩
  intro Ω Data mΩ mData n P hP raw obs g hg hgs hm c r₀ s hc hr₀ hs datum Z r L τ hr hL hτ hτr hden hcap y z hy0 hy1 hz
  let ρ := conditionalPacketDensity P raw obs g c r₀ s datum
  have hi : Integrable ρ := mixturePacketDensity_integrable hg hm hc hr₀ hs _
  have hmeas : Measurable ρ := mixturePacketDensity_measurable _ hg hc hr₀ hs
  have hp : ∀ x,0 ≤ ρ x := conditionalPacketDensity_nonneg P raw obs g hc hr₀ hs datum
  obtain ⟨A,hA,HA⟩ := conditionalPacketDensity_bounded P raw obs hg hgs hc hr₀ hs
  have hlam : 1 ≤ (r/τ)^3 := one_le_pow₀ ((le_div_iff₀ hτ).mpr (by simpa using hτr))
  have hρ (x) (hx0 : 3*r/4 ≤ ‖x‖) (hx1 : ‖x‖ ≤ 6*L*r) : ρ x ≤ (r/τ)^3*((B*K)/r^6) := by
    have hh := hden x (by linarith) (by nlinarith [mul_nonneg (by linarith : 0 ≤ L) hr.le])
    apply hh.trans_eq
    field_simp
  have hcapPos := physicalSpatialCap_pos
  have hF (x) (hx0 : 3*r/4 ≤ ‖x‖) (hx1 : ‖x‖ ≤ 6*L*r) :
      Z*coulombKernel x-potentialOf ρ x ≤ (r/τ)^3*((16*physicalSpatialCap)/r^4) := by
    have hxn : 0 < ‖x‖ := by linarith
    have hpow : (r/2)^4 ≤ ‖x‖^4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
    have hhalf : physicalSpatialCap/‖x‖^4 ≤ physicalSpatialCap/(r/2)^4 :=
      div_le_div_of_nonneg_left physicalSpatialCap_pos.le (by positivity) hpow
    calc
      _ ≤ physicalSpatialCap/‖x‖^4 := (le_div_iff₀ (pow_pos hxn 4)).mpr (by simpa only [mul_comm] using hcap x hx0 hx1)
      _ ≤ physicalSpatialCap/(r/2)^4 := hhalf
      _ = (16*physicalSpatialCap)/r^4 := by ring
      _ ≤ (r/τ)^3*((16*physicalSpatialCap)/r^4) := le_mul_of_one_le_left (by positivity) hlam
  exact H ρ Z r L ((r/τ)^3) hi hmeas hp ⟨A,HA datum⟩
    (conditionalPacketPotential_continuous P raw obs hg hgs hm hc hr₀ hs datum)
    hr hL hlam hρ hF y z hy0 hy1 hz
end NeutralAtom
end

end

end OAI
