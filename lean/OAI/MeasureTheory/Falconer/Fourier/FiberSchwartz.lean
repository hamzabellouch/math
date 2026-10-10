import OAI.MeasureTheory.Falconer.Radial.ProjectionDensity
import OAI.MeasureTheory.Falconer.Graphs.FiberTrace
import Mathlib.Analysis.Calculus.ContDiff.Convolution

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal SchwartzMap FourierTransform Convolution

@[fun_prop] theorem contDiff_sourceFrame (θ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (sourceFrame θ) := by
  have h : sourceFrame θ = fun p : ℝ × ℝ =>
      p.1 • sourceNormal θ + p.2 • sourceDirection θ := by
    funext p
    exact sourceFrame_eq θ p.1 p.2
  rw [h]
  fun_prop

@[fun_prop] theorem continuous_sourceAlong (θ : ℝ) : Continuous (sourceAlong θ) := by
  unfold sourceAlong
  fun_prop

theorem sourceAlong_frame (θ z r : ℝ) : sourceAlong θ (sourceFrame θ (z,r)) = r := by
  rw [sourceFrame_eq]
  simp [sourceAlong,sourceNormal,sourceDirection,
    Complex.orthonormalBasisOneI_repr_apply,-Complex.ofReal_cos,-Complex.ofReal_sin]
  nlinarith [congrArg (fun a : ℝ => r*a) (Real.sin_sq_add_cos_sq θ)]

noncomputable def sourceRealFiber (a : Plane → ℝ) (θ z : ℝ) : ℝ :=
  ∫ r : ℝ, a (sourceFrame θ (z,r))

theorem sourceFiber_line_compact (a : Plane → ℝ) (hc : HasCompactSupport a) (θ z : ℝ) :
    HasCompactSupport (fun r : ℝ => a (sourceFrame θ (z,r))) := by
  apply HasCompactSupport.intro (hc.image (continuous_sourceAlong θ))
  intro r hr
  by_contra hn
  apply hr
  exact ⟨sourceFrame θ (z,r), subset_tsupport a hn, sourceAlong_frame θ z r⟩

theorem sourceRealFiber_compact (a : Plane → ℝ) (hc : HasCompactSupport a) (θ : ℝ) :
    HasCompactSupport (sourceRealFiber a θ) := by
  have hP : Continuous (sourceProjection θ) := by unfold sourceProjection; fun_prop
  apply HasCompactSupport.intro (hc.image hP)
  intro z hz
  apply integral_eq_zero_of_ae
  filter_upwards with r
  by_contra hn
  exact hz ⟨sourceFrame θ (z,r), subset_tsupport a hn, sourceProjection_frame θ z r⟩

theorem sourceRealFiber_smooth (a : Plane → ℝ) (hc : HasCompactSupport a)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (θ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (sourceRealFiber a θ) := by
  let g : ℝ → ℝ → ℝ := fun z r => a (sourceFrame θ (z,r))
  have hgs : ∀ z r, z ∈ (univ : Set ℝ) → r ∉ sourceAlong θ '' tsupport a → g z r = 0 := by
    intro z r _ hr
    by_contra hn
    exact hr ⟨sourceFrame θ (z,r), subset_tsupport a hn, sourceAlong_frame θ z r⟩
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry g) (univ ×ˢ univ) :=
    (ha.comp (contDiff_sourceFrame θ)).contDiffOn
  have h := contDiffOn_convolution_right_with_param_comp (μ := (volume : Measure ℝ))
    (ContinuousLinearMap.mul ℝ ℝ) (v := fun _ : ℝ => (0 : ℝ)) contDiffOn_const
    isOpen_univ (hc.image (continuous_sourceAlong θ)) hgs
    (f := fun _ : ℝ => (1 : ℝ)) (continuous_const.locallyIntegrable) hg
  rw [contDiffOn_univ] at h
  convert h using 1
  funext z
  simp only [convolution,ContinuousLinearMap.mul_apply',one_mul,zero_sub,g,sourceRealFiber]
  exact (integral_neg_eq_self (fun r : ℝ => a (sourceFrame θ (z,r))) volume).symm

noncomputable def sourceSchwartzFiber (a : Plane → ℝ) (hc : HasCompactSupport a)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (θ : ℝ) : 𝓢(ℝ, ℝ) :=
  (sourceRealFiber_compact a hc θ).toSchwartzMap (sourceRealFiber_smooth a hc ha θ)

@[simp] theorem sourceSchwartzFiber_apply (a : Plane → ℝ) (hc : HasCompactSupport a)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (θ z : ℝ) :
    sourceSchwartzFiber a hc ha θ z = ∫ r : ℝ, a (sourceFrame θ (z,r)) := rfl

theorem sourceSchwartzFiber_nonneg (a : Plane → ℝ) (hc : HasCompactSupport a)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hn : ∀ x, 0 ≤ a x) (θ z : ℝ) :
    0 ≤ sourceSchwartzFiber a hc ha θ z := integral_nonneg (fun _ => hn _)

theorem sourceSchwartzFiber_density (a : Plane → ℝ) (hc : HasCompactSupport a)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hn : ∀ x, 0 ≤ a x) (θ z : ℝ) :
    ENNReal.ofReal (sourceSchwartzFiber a hc ha θ z) =
      projectedDensity (fun x => ENNReal.ofReal (a x)) θ z := by
  apply ofReal_integral_eq_lintegral_ofReal
  · exact (ha.continuous.comp ((continuous_sourceFrame θ).comp (by fun_prop))).integrable_of_hasCompactSupport
      (sourceFiber_line_compact a hc θ z)
  · exact Filter.Eventually.of_forall (fun r => hn _)

end PlanarFalconer

end OAI
