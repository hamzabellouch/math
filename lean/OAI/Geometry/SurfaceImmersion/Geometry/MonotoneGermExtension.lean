import OAI.Geometry.SurfaceImmersion.Correction.CompactSmoothCutoffs
import OAI.Geometry.SurfaceImmersion.Primitive.PeriodicPrimitive

namespace OAI

/-! Extending an oriented smooth coordinate germ to a globally increasing
smooth real function, with derivative one outside a compact set. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

theorem increasing_smooth_germ_extension {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (a : ℝ) (ha : 0 < deriv h a) :
    ∃ (g : ℝ → ℝ) (K : Set ℝ), ContDiff ℝ ∞ g ∧ StrictMono g ∧
      g =ᶠ[𝓝 a] h ∧ (∀ x, 0 < deriv g x) ∧ IsCompact K ∧
      ∀ x ∉ K, deriv g x = 1 := by
  have hd : ContDiff ℝ ∞ (deriv h) := (contDiff_infty_iff_deriv.mp hh).2
  let U := {x | 0 < deriv h x}
  have hU : IsOpen U := isOpen_lt continuous_const hd.continuous
  obtain ⟨W,hW,haW,hWU,φ,χ,hφ,hχ,hφc,hχc,hφr,hχr,hχs,hφs,hφone,hχone⟩ :=
    CollarVelocity.nested_compact_cutoffs (isCompact_singleton (x := a)) hU
      (singleton_subset_iff.mpr ha)
  let v : ℝ → ℝ := fun x => φ x * deriv h x + (1-φ x)
  have hv : ContDiff ℝ ∞ v := (hφ.mul hd).add (contDiff_const.sub hφ)
  have hvpos : ∀ x, 0 < v x := by
    intro x
    by_cases hx : x ∈ U
    · have hdpos : 0 < deriv h x := hx
      have hφnonneg := (hφr x).1
      have hφle := (hφr x).2
      by_cases hzero : φ x = 0
      · simp [v,hzero]
      · have hφpos : 0 < φ x := lt_of_le_of_ne hφnonneg (Ne.symm hzero)
        have hmul := mul_pos hφpos hdpos
        dsimp [v]
        linarith
    · have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun hin => hx (hφs hin))
      simp [v,hz]
  let g : ℝ → ℝ := fun x => h a +
    PeriodicPrimitive.rawPrimitive v x - PeriodicPrimitive.rawPrimitive v a
  have hg : ContDiff ℝ ∞ g :=
    (contDiff_const.add (PeriodicPrimitive.rawPrimitive_contDiff hv)).sub contDiff_const
  have hgder : ∀ x, deriv g x = v x := by
    intro x
    exact (((PeriodicPrimitive.rawPrimitive_hasDerivAt hv.continuous x).const_add (h a)).sub_const _).deriv
  have hag : g a = h a := by dsimp [g]; ring
  obtain ⟨r,hr,hrW⟩ := Metric.isOpen_iff.mp hW a (haW (by simp))
  have heq : EqOn g h (Metric.ball a r) := by
    apply isOpen_ball.eqOn_of_deriv_eq (convex_ball a r).isPreconnected
      (hg.differentiable (by simp)).differentiableOn (hh.differentiable (by simp)).differentiableOn
    · intro x hx
      rw [hgder]
      dsimp [v]
      rw [hφone x (hrW hx)]
      ring
    · exact Metric.mem_ball_self hr
    · exact hag
  refine ⟨g,tsupport φ,hg,strictMono_of_deriv_pos (fun x => (hgder x) ▸ hvpos x),
    heq.eventuallyEq_of_mem (isOpen_ball.mem_nhds (Metric.mem_ball_self hr)),
    fun x => (hgder x) ▸ hvpos x,hφc,?_⟩
  intro x hx
  rw [hgder]
  have hz := image_eq_zero_of_notMem_tsupport hx
  simp [v,hz]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
