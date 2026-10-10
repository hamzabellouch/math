import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarGroundDuality
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarProjectionGap

namespace OAI

/-! Ground-state duality on the full closed planar Sobolev graph. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb.PlanarSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

local instance instPlanarSobolevDualityMeasurable : MeasurableSpace PlanarPosition := borel PlanarPosition
local instance instPlanarSobolevDualityBorel : BorelSpace PlanarPosition := ⟨rfl⟩
local instance instPlanarSobolevDualityMeasure : MeasureSpace PlanarPosition := measureSpaceOfInnerProductSpace

def groundDualWeight (ψ : Test) (a : Fin 2) (x : PlanarPosition) : ℝ :=
  planarPartial ψ.val (planarAxis a) x/planarResolventMode x

theorem groundDualWeight_continuous (ψ : Test) (a : Fin 2) :
    Continuous (groundDualWeight ψ a) :=
  (planarPartial_continuous ψ.property.1 _).div planarResolventMode_C7.continuous
    (fun x => (planarResolventMode_positive x).ne')

theorem groundDualWeight_compact (ψ : Test) (a : Fin 2) :
    HasCompactSupport (groundDualWeight ψ a) := by
  change HasCompactSupport (fun x => planarPartial ψ.val (planarAxis a) x *
    (planarResolventMode x)⁻¹)
  exact (ψ.property.2.fderiv_apply ℝ _).mul_right

theorem groundDualWeight_memLp (ψ : Test) (a : Fin 2) : MemLp (groundDualWeight ψ a) 2 :=
  (groundDualWeight_continuous ψ a).memLp_of_hasCompactSupport (groundDualWeight_compact ψ a)

def groundDualLp (ψ : Test) (a : Fin 2) : Lp ℝ 2 (volume : Measure PlanarPosition) :=
  (groundDualWeight_memLp ψ a).toLp (groundDualWeight ψ a)

theorem groundDualLp_inner (u : Lp ℝ 2 (volume : Measure PlanarPosition))
    (ψ : Test) (a : Fin 2) :
    inner ℝ u (groundDualLp ψ a) =
      ∫ x, (u x/planarResolventMode x)*planarPartial ψ.val (planarAxis a) x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(groundDualWeight_memLp ψ a).coeFn_toLp] with x hx
  change inner ℝ (u x) ((groundDualWeight_memLp ψ a).toLp (groundDualWeight ψ a) x) = _
  rw [hx,RCLike.inner_apply,conj_trivial]
  unfold groundDualWeight
  ring

theorem graph_groundDualLp_inner (u ψ : Test) (a : Fin 2) :
    inner ℝ (graph (μ := volume) u).1 (groundDualLp ψ a) =
      ∫ x, planarGroundQuotient u.val x*planarPartial ψ.val (planarAxis a) x := by
  rw [groundDualLp_inner]
  apply integral_congr_ae
  filter_upwards [(memLp_of_mem_C1c (μ := volume) u.property).coeFn_toLp] with x hx
  change (toL2 (μ := volume) u x/planarResolventMode x)*_ = _
  change toL2 (μ := volume) u x = u.val x at hx
  rw [hx]
  rfl

theorem graph_ground_dual_bound (u ψ : Test) (a : Fin 2) :
    (inner ℝ (graph (μ := volume) u).1 (groundDualLp ψ a))^2 ≤
      originalIntegral (fun x => (ψ.val x/planarResolventMode x)^2)*
        (2*shiftedForm (graph (μ := volume) u)) := by
  have h := planar_ground_dual_bound u.val ψ.val u.property.1 u.property.2
    ψ.property.1 ψ.property.2 a
  change (originalIntegral (fun x => planarGroundQuotient u.val x*
    planarPartial ψ.val (planarAxis a) x))^2 ≤
    originalIntegral (fun x => (ψ.val x/planarResolventMode x)^2)*
      (2*planarTestForm manufacturedPlanarWell u.val+originalIntegral (fun x => u.val x^2)) at h
  rw [graph_groundDualLp_inner,shiftedForm,graph_form,graph_mass]
  simp_rw [planar_integral_change_borel (borel PlanarPosition) ⟨rfl⟩]
  convert h using 1
  ring

theorem sobolev_ground_dual_bound (u : Sobolev) (ψ : Test) (a : Fin 2) :
    (inner ℝ u.val.1 (groundDualLp ψ a))^2 ≤
      originalIntegral (fun x => (ψ.val x/planarResolventMode x)^2)*(2*shiftedForm u.val) := by
  have hS : Continuous (fun v : Target => shiftedForm v) :=
    form_continuous.add (continuous_const.mul (continuous_fst.norm.pow 2))
  have hc : IsClosed {v : Target | (inner ℝ v.1 (groundDualLp ψ a))^2 ≤
      originalIntegral (fun x => (ψ.val x/planarResolventMode x)^2)*(2*shiftedForm v)} :=
    isClosed_le ((continuous_fst.inner continuous_const).pow 2)
      (continuous_const.mul (continuous_const.mul hS))
  apply closure_minimal (s := (LinearMap.range (graph (μ := volume) (E := PlanarPosition)) : Set Target))
    (t := {v : Target | (inner ℝ v.1 (groundDualLp ψ a))^2 ≤
      originalIntegral (fun x => (ψ.val x/planarResolventMode x)^2)*(2*shiftedForm v)}) ?_ hc u.property
  rintro _ ⟨f,rfl⟩
  exact graph_ground_dual_bound f ψ a

theorem zero_ground_form_axis_distribution (u : Sobolev) (hzero : shiftedForm u.val = 0)
    (ψ : PlanarPosition → ℝ) (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (a : Fin 2) :
    (∫ x, (u.val.1 x/planarResolventMode x)*planarPartial ψ (planarAxis a) x) = 0 := by
  let p : Test := ⟨ψ,hψ,hψc⟩
  have hb := sobolev_ground_dual_bound u p a
  rw [hzero,mul_zero,mul_zero] at hb
  have he : inner ℝ u.val.1 (groundDualLp p a) = 0 := by nlinarith [sq_nonneg (inner ℝ u.val.1 (groundDualLp p a))]
  rw [groundDualLp_inner] at he
  exact he

end ContinuumCoulomb.PlanarSobolev

end

end OAI
