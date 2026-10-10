import OAI.Geometry.NodalSets.Charts.SphereReferenceMeasurePositive
import OAI.Geometry.NodalSets.Elliptic.CompactParameterEllipticityLemmas

namespace OAI

namespace Yau.Target
open Yau.Geometry Set Metric MeasureTheory
noncomputable section
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

theorem sphere_chart_l2_comparison (rho : T → Base → ℝ)
    (hr : Continuous (fun z : T × Base ↦ rho z.1 z.2)) (hp : ∀ t p, 0 < rho t p)
    (p : Base) (Q : Set Yau.Jets.Coord) (hQ : IsCompact Q) :
    ∃ K > 0, ∀ t (v : Base → ℝ), Continuous v →
      IntegrableOn (fun x ↦ v (sphereChartCoordMap p x)^2) Q ∧
      (∫ x in Q, v (sphereChartCoordMap p x)^2) ≤ K*sphereWeightedPairing (rho t) v v := by
  let d (t : T) (x : Yau.Jets.Coord) := roundCoordDensity x*rho t (sphereChartCoordMap p x)
  have hdpos (t : T) (x : Yau.Jets.Coord) : 0 < d t x :=
    mul_pos (roundCoordDensity_pos x) (hp t _)
  have hdc : Continuous (fun z : T × Q ↦ d z.1 z.2) :=
    (roundCoordDensity_smooth.continuous.comp (continuous_subtype_val.comp continuous_snd)).mul
      (hr.comp (continuous_fst.prodMk ((sphereChartCoordMap_smooth p).continuous.comp
        (continuous_subtype_val.comp continuous_snd))))
  obtain ⟨K,hK,hbound⟩ := compact_parameter_scalar_bound (fun t x ↦ (d t x)⁻¹) hQ
    (hdc.inv₀ (fun z ↦ (hdpos z.1 z.2).ne'))
  have hlow (t : T) (x : Yau.Jets.Coord) (hx : x ∈ Q) : 1 ≤ K*d t x := by
    have hh := (le_abs_self (d t x)⁻¹).trans (hbound t x hx)
    simpa only [inv_mul_cancel₀ (hdpos t x).ne'] using
      mul_le_mul_of_nonneg_right hh (hdpos t x).le
  refine ⟨K,hK,?_⟩
  intro t v hv
  have hrt : Continuous (rho t) := hr.comp (continuous_const.prodMk continuous_id)
  let J (x : Yau.Jets.Coord) := roundCoordDensity x*(rho t (sphereChartCoordMap p x)*
    v (sphereChartCoordMap p x)*v (sphereChartCoordMap p x))
  have hJ : Integrable J := by
    have hi := (sphereReferenceMeasure_integrable_chart p _).mp
      (sphereWeightedPairing_integrable (rho t) v v hrt hv hv)
    simpa only [roundChartDensity_coord_eq] using hi
  have hJn (x : Yau.Jets.Coord) : 0 ≤ J x := by
    dsimp [J]
    nlinarith [roundCoordDensity_pos x,hp t (sphereChartCoordMap p x),sq_nonneg (v (sphereChartCoordMap p x)),
      mul_nonneg (mul_pos (roundCoordDensity_pos x) (hp t (sphereChartCoordMap p x))).le
        (sq_nonneg (v (sphereChartCoordMap p x)))]
  have hi : IntegrableOn (fun x ↦ v (sphereChartCoordMap p x)^2) Q :=
    ((hv.comp (sphereChartCoordMap_smooth p).continuous).pow 2).continuousOn.integrableOn_compact hQ
  refine ⟨hi,?_⟩
  have hmon := setIntegral_mono_on hi (hJ.integrableOn.const_mul K) hQ.isClosed.measurableSet
    (fun x hx ↦ show v (sphereChartCoordMap p x)^2 ≤ K*J x from by
      have hh := mul_le_mul_of_nonneg_right (hlow t x hx) (sq_nonneg (v (sphereChartCoordMap p x)))
      dsimp [d,J] at hh ⊢
      nlinarith [hh])
  rw [integral_const_mul] at hmon
  have heq : (∫ x, J x) = sphereWeightedPairing (rho t) v v := by
    rw [sphereWeightedPairing,sphereReferenceMeasure_integral_chart p]
    simp only [roundChartDensity_coord_eq]
    rfl
  exact hmon.trans ((mul_le_mul_of_nonneg_left
    (setIntegral_le_integral hJ (Filter.Eventually.of_forall hJn)) hK.le).trans_eq (by rw [heq]))

theorem sphere_normalized_chart_l2_bound (rho : T → Base → ℝ)
    (hr : Continuous (fun z : T × Base ↦ rho z.1 z.2)) (hp : ∀ t p, 0 < rho t p)
    (p : Base) (Q : Set Yau.Jets.Coord) (hQ : IsCompact Q) :
    ∃ K > 0, ∀ t (v : Base → ℝ), Continuous v → sphereWeightedPairing (rho t) v v=1 →
      (∫ x in Q, v (sphereChartCoordMap p x)^2) ≤ K := by
  obtain ⟨K,hK,hest⟩ := sphere_chart_l2_comparison rho hr hp p Q hQ
  refine ⟨K,hK,?_⟩
  intro t v hv hn
  simpa only [hn,mul_one] using (hest t v hv).2

end
end Yau.Target

end OAI
