import OAI.Geometry.SurfaceImmersion.Geometry.ScalarFlatTaylor
import Mathlib.Topology.MetricSpace.HausdorffDimension

namespace OAI

/-! The flat second-jet stratum of a smooth scalar surface function has
locally cubic Hölder control. -/
noncomputable section
open Set Metric
open scoped ContDiff Topology NNReal ENNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
local instance holderFirstNormed : NormedAddCommGroup (Base →L[ℝ] ℝ) := inferInstance
local instance holderFirstSpace : NormedSpace ℝ (Base →L[ℝ] ℝ) := inferInstance
local instance holderSecondNormed : NormedAddCommGroup (Base →L[ℝ] Base →L[ℝ] ℝ) := inferInstance
local instance holderSecondSpace : NormedSpace ℝ (Base →L[ℝ] Base →L[ℝ] ℝ) := inferInstance
local instance holderThirdNormed : NormedAddCommGroup (Base →L[ℝ] Base →L[ℝ] Base →L[ℝ] ℝ) := inferInstance
local instance holderThirdSpace : NormedSpace ℝ (Base →L[ℝ] Base →L[ℝ] Base →L[ℝ] ℝ) := inferInstance

def scalarFlatTwo (f : Base → ℝ) : Set Base :=
  {x | fderiv ℝ f x = 0 ∧ fderiv ℝ (fderiv ℝ f) x = 0}

theorem scalarFlatTwo_local_holder {f : Base → ℝ} (hf : ContDiff ℝ ∞ f) (p : Base) :
    ∃ C : ℝ≥0, HolderOnWith C 3 f (scalarFlatTwo f ∩ ball p (1/4)) := by
  have hD := hf.fderiv_right (m := ∞) (by simp)
  have hDD := hD.fderiv_right (m := ∞) (by simp)
  have hc := hDD.continuous_fderiv (by simp)
  obtain ⟨M,hM⟩ := (isCompact_closedBall p 1).exists_bound_of_continuousOn hc.continuousOn
  let C : ℝ≥0 := ⟨max M 0,le_max_right _ _⟩
  refine ⟨C,?_⟩
  intro x hx y hy
  have hsub : closedBall y ‖x-y‖ ⊆ closedBall p 1 := by
    intro z hz
    have hzp := dist_triangle z y p
    have hxy := dist_triangle x p y
    have hz' : dist z y ≤ dist x y := by simpa only [mem_closedBall,dist_eq_norm] using hz
    have hxp : dist x p < 1/4 := hx.2
    have hyp : dist y p < 1/4 := hy.2
    rw [dist_comm p y] at hxy
    change dist z p ≤ 1
    linarith
  have hbound : ‖f x-f y‖ ≤ (C:ℝ)*‖x-y‖^3 :=
    scalar_flat_cubic_bound hf y x hy.1.1 hy.1.2 C.2 (fun z hz =>
      (hM z (hsub hz)).trans (le_max_left _ _))
  change edist (f x) (f y) ≤ (C : ℝ≥0∞)*edist x y ^ (3 : ℝ)
  rw [edist_dist,edist_dist,show (3 : ℝ) = (3 : ℕ) by norm_num,ENNReal.rpow_natCast]
  have he := ENNReal.ofReal_le_ofReal hbound
  rw [ENNReal.ofReal_mul (p := (C:ℝ)) C.2,
    ENNReal.ofReal_pow (norm_nonneg (x-y)) 3,ENNReal.ofReal_coe_nnreal] at he
  simpa only [dist_eq_norm] using he

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
