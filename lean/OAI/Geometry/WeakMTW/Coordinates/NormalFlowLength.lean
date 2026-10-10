import Mathlib
import OAI.Geometry.WeakMTW.Coordinates.NormalLength

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace NormalNeighborhood.NormalFlow
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
open CoordinateGeometry RadialCoordinates
variable {G : E → MetricTensor E} {S : Set E} {x₀ : E}

theorem normalAt_zero (N : NormalFlow G S x₀)
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hpos : ∀ z ∈ S, ∀ v : E, v ≠ 0 → 0 < G z v v)
    {x : E} (hx : (0 : E) ∈ (N.normalAt x).source) : N.normalAt x 0 = x := by
  have he := FlowLinearization.equilibrium N.domain_open
    (N.flow_smooth.of_le (show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) from WithTop.coe_le_coe.mpr le_top))
    (hS.prod isOpen_univ) ((contDiffOn_geodesicSpray hS hG hpos).of_le (by simp))
    N.initial (fun q hq => ⟨⟨(N.ode q hq).1, mem_univ _⟩, (N.ode q hq).2⟩)
    (x := (x, 0)) ⟨N.base_mem hx, mem_univ _⟩ (geodesicSpray_zero G x)
    N.time_pos.le (N.source_stays (x, 0) hx)
  rw [N.normalAt_apply, he N.time ⟨N.time_pos.le, le_rfl⟩]

theorem center_target (N : NormalFlow G S x₀)
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hpos : ∀ z ∈ S, ∀ v : E, v ≠ 0 → 0 < G z v v) :
    x₀ ∈ (N.normalAt x₀).target := by
  have h := (N.normalAt x₀).map_source N.center_mem
  rwa [N.normalAt_zero hS hG hpos N.center_mem] at h

omit [FiniteDimensional ℝ E] in
theorem flow_curve_smooth (N : NormalFlow G S x₀) {x v : E}
    (hv : v ∈ (N.normalAt x).source) :
    ContDiffOn ℝ ∞ (fun t => (N.flow (t, (x, v))).1) (Icc (0 : ℝ) N.time) :=
  (N.flow_smooth.comp (contDiff_id.prodMk contDiff_const).contDiffOn
    (N.source_stays (x, v) hv)).fst

theorem flow_curve_length (N : NormalFlow G S x₀)
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hsym : ∀ z ∈ S, ∀ v w, G z v w = G z w v)
    (hpos : ∀ z ∈ S, ∀ v : E, v ≠ 0 → 0 < G z v v)
    {x v : E} (hv : v ∈ (N.normalAt x).source) :
    coordinateLength G (fun t => (N.flow (t, (x, v))).1) 0 N.time =
      ENNReal.ofReal (N.time * Real.sqrt (G x v v)) := by
  have hseg := N.source_stays (x, v) hv
  have h0 := N.initial (x, v) (hseg 0 ⟨le_rfl, N.time_pos.le⟩)
  have hE := geodesic_energy_constant hS (hG.differentiableOn (by simp)) hsym hpos
    (fun t ht => (N.ode _ (hseg t ht)).1)
    (fun t ht => (N.ode _ (hseg t ht)).2.fst)
    (fun t ht => (N.ode _ (hseg t ht)).2.snd)
  rw [coordinateLength]
  have heq : (∫⁻ t in Icc (0 : ℝ) N.time,
      ENNReal.ofReal (Real.sqrt (G (N.flow (t, (x, v))).1
        (deriv (fun s => (N.flow (s, (x, v))).1) t)
        (deriv (fun s => (N.flow (s, (x, v))).1) t)))) =
      ∫⁻ _t in Icc (0 : ℝ) N.time, ENNReal.ofReal (Real.sqrt (G x v v)) := by
    apply setLIntegral_congr_fun measurableSet_Icc
    intro t ht
    have hd : HasDerivAt (fun s => (N.flow (s, (x, v))).1) (N.flow (t, (x, v))).2 t :=
      (N.ode _ (hseg t ht)).2.fst
    dsimp only
    rw [hd.deriv]
    change ENNReal.ofReal (Real.sqrt (G (N.flow (t, (x, v))).1
      (geodesicSpray G (N.flow (t, (x, v)))).1 (geodesicSpray G (N.flow (t, (x, v)))).1)) = _
    rw [hE t ht, h0]
    rfl
  rw [heq, lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
  simp only [sub_zero]
  rw [mul_comm, ← ENNReal.ofReal_mul N.time_pos.le]

end
end NormalNeighborhood.NormalFlow
end

end WeakMTWGlobalSupport

end OAI
