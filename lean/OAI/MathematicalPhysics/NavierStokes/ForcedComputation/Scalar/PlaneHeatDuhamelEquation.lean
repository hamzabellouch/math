import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneHeatSourceEquation

namespace OAI

/-! The inhomogeneous heat equation for the initial-value plus source formula. -/

noncomputable section
namespace ForcedComputation.PlaneHeat
open ShearFlows Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators

theorem norm_fderiv_jet_le (k : ℕ) (J : BoundedSpatialJets.Space Plane ℝ (k+1)) (x : Plane) :
    ‖fderiv ℝ (BoundedSpatialJets.function Plane ℝ (k+1) J) x‖ ≤ ‖J‖ := by
  rw [← BoundedSpatialJets.function_derivative Plane ℝ k J x]
  exact (BoundedSpatialJets.norm_function_le Plane (Plane →L[ℝ] ℝ) k _ x).trans
    (BoundedSpatialJets.norm_derivative_le Plane ℝ k J)

theorem hasDerivAt_initial_evolution {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (f : Plane → ℝ) (hf : ContDiff ℝ ∞ f) (J : BoundedSpatialJets.Space Plane ℝ 3)
    (hJ : (BoundedSpatialJets.function Plane ℝ 3 J : Plane → ℝ) = f) (x : Plane) :
    HasDerivAt (fun s => evolution ℝ f (ν*s) x)
      (ν * ∑ j : Fin 2, spatialPartial ℝ j (spatialPartial ℝ j (evolution ℝ f (ν*t))) x) t := by
  have hC (y : Plane) : ‖f y‖ ≤ ‖J‖ := by
    rw [← hJ]
    exact BoundedSpatialJets.norm_function_le Plane ℝ 3 J y
  have hD (y : Plane) : ‖fderiv ℝ f y‖ ≤ ‖J‖ := by
    rw [← hJ]
    exact norm_fderiv_jet_le 2 J y
  have hE (j : Fin 2) (y : Plane) : ‖fderiv ℝ (spatialPartial ℝ j f) y‖ ≤ ‖J‖ := by
    let P := BoundedSpatialJets.directionalDerivativeCLM Plane ℝ 2 (Pi.single j 1)
    have he : (BoundedSpatialJets.function Plane ℝ 2 (P J) : Plane → ℝ) = spatialPartial ℝ j f := by
      funext z
      rw [BoundedSpatialJets.function_directionalDerivativeCLM, hJ]
      rfl
    rw [← he]
    apply (norm_fderiv_jet_le 1 (P J) y).trans
    apply (P.le_opNorm J).trans
    have hp : ‖P‖ ≤ 1 := by
      simpa only [P, Pi.norm_single, norm_one] using
        BoundedSpatialJets.norm_directionalDerivativeCLM_le Plane ℝ 2 (Pi.single j 1)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (norm_nonneg J)
  have hd := (hasDerivAt_heatConvolution_equation ℝ (mul_pos hν ht) hf
    ‖J‖ ‖J‖ ‖J‖ hC hD hE x).comp t ((hasDerivAt_id t).const_mul ν)
  have he : evolution ℝ f (ν*t) = heatConvolution ℝ (ν*t) f := by
    funext y
    exact ite_eq_right (not_le.mpr (mul_pos hν ht))
  rw [he]
  convert hd.congr_of_eventuallyEq (f₁ := fun s => evolution ℝ f (ν*s) x) ?_ using 1
  · simp only [mul_one, mul_comm]
  · filter_upwards [Ioi_mem_nhds ht] with s hs
    exact ite_eq_right (not_le.mpr (mul_pos hν hs))

theorem spatialPartial_add {f g : Plane → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (j : Fin 2) :
    spatialPartial ℝ j (fun x => f x+g x) = fun x => spatialPartial ℝ j f x+spatialPartial ℝ j g x := by
  funext x
  rw [spatialPartial, fderiv_fun_add (hf x) (hg x)]
  rfl

theorem spatialPartial_twice_add {f g : Plane → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (j : Fin 2) :
    spatialPartial ℝ j (spatialPartial ℝ j (fun x => f x+g x)) =
      fun x => spatialPartial ℝ j (spatialPartial ℝ j f) x+
        spatialPartial ℝ j (spatialPartial ℝ j g) x := by
  rw [spatialPartial_add (hf.differentiable (by norm_num)) (hg.differentiable (by norm_num))]
  apply spatialPartial_add
  · exact ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable (by norm_num)
  · exact ((hg.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable (by norm_num)

theorem hasDerivAt_duhamel {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (f : Plane → ℝ) (hf : ContDiff ℝ ∞ f) (J : BoundedSpatialJets.Space Plane ℝ 3)
    (hJ : (BoundedSpatialJets.function Plane ℝ 3 J : Plane → ℝ) = f)
    (q : WeaklySingular.Path (PlaneScalarMild.Jet 3) T)
    (hq : ∀ s, ContDiff ℝ ∞ (PlaneScalarMild.sourceValue hT 3 q s))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) (x : Plane) :
    HasDerivAt
      (fun s => evolution ℝ f (ν*s) x + PlaneScalarMild.heatSourceValue hT hν 3 q s x)
      (ν * ∑ j : Fin 2, spatialPartial ℝ j (spatialPartial ℝ j
        (fun y => evolution ℝ f (ν*t) y + PlaneScalarMild.heatSourceValue hT hν 3 q t y)) x +
          PlaneScalarMild.sourceValue hT 3 q t x) t := by
  have hi : ContDiff ℝ 3 (evolution ℝ f (ν*t)) := by
    have he := evolutionOperator_function ℝ 3 (ν*t) J
    have he' : (BoundedSpatialJets.function Plane ℝ 3 (evolutionOperator ℝ 3 (ν*t) J) : Plane → ℝ) =
        evolution ℝ f (ν*t) := by
      funext y
      rw [he, hJ]
    rw [← he']
    exact BoundedSpatialJets.function_contDiff Plane ℝ 3 _
  have hs : ContDiff ℝ 3 (PlaneScalarMild.heatSourceValue hT hν 3 q t) :=
    BoundedSpatialJets.function_contDiff Plane ℝ 3 _
  have hd := (hasDerivAt_initial_evolution hν ht.1 f hf J hJ x).add
    (PlaneScalarMild.hasDerivAt_heatSourceValue hT hν q hq ht x)
  convert hd using 1
  simp only [spatialPartial_twice_add (hi.of_le (by norm_num)) (hs.of_le (by norm_num)),
    Finset.sum_add_distrib]
  ring

end ForcedComputation.PlaneHeat

end

end OAI
