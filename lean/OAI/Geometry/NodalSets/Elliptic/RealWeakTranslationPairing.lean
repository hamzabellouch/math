import OAI.Geometry.NodalSets.Elliptic.RealL2PairingRepresentatives
import OAI.Geometry.NodalSets.Elliptic.RealSmoothDifferenceLimit

namespace OAI

namespace Yau
open MeasureTheory Set Filter
open scoped ContDiff Topology
noncomputable section

theorem real_smooth_difference_pairing_limit {n : ℕ} (u psi : Coord n → ℝ)
    (hu : Integrable u) (hp : ContDiff ℝ ∞ psi) (hc : HasCompactSupport psi) (i : Fin n) :
    Tendsto (fun h : ℝ ↦ ∫ x, u x*realDifferenceQuotient i h psi x) (𝓝[≠] (0:ℝ))
      (𝓝 (∫ x, u x*coordPartial psi x i)) := by
  obtain ⟨B,hB,hb⟩ := real_smooth_difference_uniform_bound psi hp hc
  apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ |u x| *B)
  · exact Filter.Eventually.of_forall (fun h ↦ hu.aestronglyMeasurable.mul
      (realDifferenceQuotient_smooth i h psi hp).continuous.aestronglyMeasurable)
  · apply Filter.Eventually.of_forall
    intro h
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul_of_nonneg_left (hb i h x) (abs_nonneg _)
  · exact hu.norm.mul_const B
  · exact Filter.Eventually.of_forall (fun x ↦ tendsto_const_nhds.mul
      (real_smooth_difference_tendsto psi hp i x))

theorem real_translate_pairing_hasDerivAt {n : ℕ} (u psi : Coord n → ℝ)
    (hu : Integrable u) (hum : MemLp u 2 volume)
    (hp : ContDiff ℝ ∞ psi) (hc : HasCompactSupport psi) (i : Fin n) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ ∫ x, u x*psi (x+Pi.single i s))
      (∫ x, u x*coordPartial (fun y ↦ psi (y+Pi.single i t)) x i) t := by
  let phi : Coord n → ℝ := fun x ↦ psi (x+Pi.single i t)
  have hphi : ContDiff ℝ ∞ phi := hp.comp (contDiff_id.add contDiff_const)
  have hphic : HasCompactSupport phi := hc.comp_homeomorph (Homeomorph.addRight (Pi.single i t))
  have ht := real_smooth_difference_pairing_limit u phi hu hphi hphic i
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  have he (h : ℝ) : h⁻¹ • ((∫ x, u x*psi (x+Pi.single i (t+h)))-
      (∫ x, u x*psi (x+Pi.single i t))) = ∫ x, u x*realDifferenceQuotient i h phi x := by
    have hint (s : ℝ) : Integrable (fun x ↦ u x*psi (x+Pi.single i s)) :=
      hum.integrable_mul ((real_compact_continuous_memLp psi hp.continuous hc).comp_measurePreserving
        (f := fun x : Coord n ↦ x+(Pi.single i s : Coord n))
        (measurePreserving_add_right (G := Coord n) volume (Pi.single i s : Coord n)))
    rw [smul_eq_mul,← integral_sub (hint (t+h)) (hint t),← integral_const_mul]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    simp only [realDifferenceQuotient,phi,Pi.single_add]
    rw [show x+Pi.single i h+Pi.single i t=x+(Pi.single i t+Pi.single i h) by abel]
    ring
  simpa only [he] using ht

end
end Yau

end OAI
