import OAI.MathematicalPhysics.Boltzmann.Branching.BoundedGeometricBlock
import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalizedDampedBalance
import OAI.MathematicalPhysics.Boltzmann.Branching.LargeOutput

namespace OAI

/-! # A finite-speed history stays in the physical cutoff core -/

noncomputable section

open Set
open BoltzmannNonuniqueness.EuclideanFlight
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem boundedFlightCone_characteristic {t₀ Δ : ℝ} {x v : V} {q : PhysicalFlightState}
    (hq : boundedFlightCone (Δ,(x,v)) q) :
    let z := flightCharacteristicEquiv (t₀+Δ) q
    z.1 ∈ Icc t₀ (t₀+Δ) ∧ ‖z.2.2‖ ≤ 6 ∧
      ‖z.2.1+t₀ • z.2.2-x‖ ≤ 12*Δ ∧ ‖q.2.1-x‖ ≤ 6*Δ := by
  have hd : 0 ≤ Δ-q.1 := sub_nonneg.mpr hq.2.1
  have hd' : Δ-q.1 ≤ Δ := sub_le_self _ hq.1
  have hpos : 0 ≤ Δ := hq.1.trans hq.2.1
  refine ⟨⟨?_,?_⟩,hq.2.2.1,?_,?_⟩
  · change t₀ ≤ t₀+Δ-q.1
    linarith
  · change t₀+Δ-q.1 ≤ t₀+Δ
    linarith [hq.1]
  · change ‖(q.2.1-(t₀+Δ-q.1) • q.2.2)+t₀ • q.2.2-x‖ ≤ 12*Δ
    have he : (q.2.1-(t₀+Δ-q.1) • q.2.2)+t₀ • q.2.2-x =
        (q.2.1-x)-(Δ-q.1) • q.2.2 := by module
    rw [he]
    calc
      _ ≤ ‖q.2.1-x‖+‖(Δ-q.1) • q.2.2‖ := norm_sub_le _ _
      _ ≤ 6*(Δ-q.1)+(Δ-q.1)*6 := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hd]
        exact add_le_add hq.2.2.2 (mul_le_mul_of_nonneg_left hq.2.2.1 hd)
      _ ≤ 12*Δ := by linarith
  · exact hq.2.2.2.trans (mul_le_mul_of_nonneg_left hd' (by norm_num))

theorem boundedFlightCone_cold_domain {a t₀ Δ η l : ℝ} {x v : V} {q : PhysicalFlightState}
    (ha : a ≤ t₀) (hl : 0 ≤ l)
    (hcut : Real.exp η*l+6*Δ < ‖transverse x‖)
    (hq : boundedFlightCone (Δ,(x,v)) q) :
    flightCharacteristicEquiv (t₀+Δ) q ∈ coldCharacteristicDomain a η l := by
  obtain ⟨ht,_,_,hpos⟩ := boundedFlightCone_characteristic hq
  have htrans : ‖transverse x‖-‖transverse q.2.1‖ ≤ 6*Δ := by
    calc
      _ ≤ ‖transverse x-transverse q.2.1‖ := norm_sub_norm_le _ _
      _ = ‖transverse (x-q.2.1)‖ := by rw [PlaneChart.transverse_sub]
      _ ≤ ‖x-q.2.1‖ := LargeOutput.transverse_norm_le _
      _ = ‖q.2.1-x‖ := norm_sub_rev _ _
      _ ≤ _ := hpos
  have hrad : Real.exp η*l < ‖transverse q.2.1‖ := by linarith
  have hn : 0 < ‖transverse q.2.1‖ := (mul_nonneg (Real.exp_pos η).le hl).trans_lt hrad
  change a ≤ t₀+Δ-q.1 ∧
    0 < ‖transverse ((q.2.1-(t₀+Δ-q.1) • q.2.2)+(t₀+Δ-q.1) • q.2.2)‖ ∧
    Real.exp η*l < ‖transverse ((q.2.1-(t₀+Δ-q.1) • q.2.2)+(t₀+Δ-q.1) • q.2.2)‖
  rw [sub_add_cancel]
  exact ⟨ha.trans ht.1,hn,hrad⟩

end BoltzmannNonuniqueness.ReferenceGeometry

end

end OAI
