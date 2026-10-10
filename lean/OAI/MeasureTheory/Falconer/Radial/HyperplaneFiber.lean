import OAI.MeasureTheory.Falconer.Radial.HyperplaneFrame
import OAI.MeasureTheory.Falconer.Geometry.EuclideanLpTrace
import Mathlib.Analysis.Calculus.ContDiff.Convolution

namespace OAI

/-! Smooth compactly supported fibers in the actual hyperplane coordinates. -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal SchwartzMap FourierTransform Convolution

noncomputable def hyperplaneFiberDensity {n : ℕ} (a : Space (n+1) → ℝ≥0∞)
    (w : Sphere (n+1)) (y : Space n) : ℝ≥0∞ :=
  ∫⁻ r : ℝ, a (hyperplaneFrame w (y,r))

theorem hyperplaneFiberDensity_measurable {n : ℕ} (a : Space (n+1) → ℝ≥0∞)
    (ha : Measurable a) (w : Sphere (n+1)) : Measurable (hyperplaneFiberDensity a w) :=
  (ha.comp (contDiff_hyperplaneFrame w).continuous.measurable).lintegral_prod_right'

theorem hyperplaneCoordinateMeasure_withDensity {n : ℕ} (a : Space (n+1) → ℝ≥0∞)
    (ha : Measurable a) (w : Sphere (n+1)) :
    hyperplaneCoordinateMeasure (volume.withDensity a) w =
      volume.withDensity (hyperplaneFiberDensity a w) := by
  have hP := (contDiff_hyperplaneProjection w).continuous.measurable
  ext S hS
  rw [hyperplaneCoordinateMeasure, Measure.map_apply hP hS,
    withDensity_apply _ (hS.preimage hP), withDensity_apply _ hS]
  have h := (hyperplaneFrame_volume w).setLIntegral_comp_preimage (hS.preimage hP) ha
  have hset : hyperplaneFrame w ⁻¹' (hyperplaneProjection w ⁻¹' S) = S ×ˢ univ := by
    ext ⟨y,r⟩
    simp only [mem_preimage, hyperplaneProjection_frame, mem_prod, mem_univ, and_true]
  rw [hset] at h
  have hm : Measurable (fun p : Space n × ℝ => a (hyperplaneFrame w p)) :=
    ha.comp (contDiff_hyperplaneFrame w).continuous.measurable
  rw [setLIntegral_prod _ hm.aemeasurable] at h
  simpa only [setLIntegral_univ, hyperplaneFiberDensity] using h.symm

theorem hyperplaneFrame_line {n : ℕ} (w : Sphere (n+1)) (x : Space (n+1)) (r : ℝ) :
    hyperplaneFrame w (hyperplaneProjection w x, r+inner ℝ x (w : Space (n+1))) =
      x + r • (w : Space (n+1)) := by
  have h := hyperplaneFrame_reconstruct w x
  rw [hyperplaneFrame_fiber] at h ⊢
  rw [add_smul]
  calc
    _ = (hyperplaneSliceEmbedding w (hyperplaneProjection w x) +
        inner ℝ x (w : Space (n+1)) • (w : Space (n+1))) + r • (w : Space (n+1)) := by abel
    _ = _ := by rw [h]

theorem hyperplaneFiberDensity_line {n : ℕ} (a : Space (n+1) → ℝ≥0∞)
    (w : Sphere (n+1)) (x : Space (n+1)) :
    hyperplaneFiberDensity a w (hyperplaneProjection w x) =
      ∫⁻ r : ℝ, a (x+r • (w : Space (n+1))) := by
  have h := lintegral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun r => a (hyperplaneFrame w (hyperplaneProjection w x,r)))
      (inner ℝ x (w : Space (n+1)))
  simp_rw [hyperplaneFrame_line] at h
  exact h.symm

noncomputable def hyperplaneRealFiber {n : ℕ} (a : Space (n+1) → ℝ)
    (w : Sphere (n+1)) (y : Space n) : ℝ := ∫ r : ℝ, a (hyperplaneFrame w (y,r))

theorem hyperplaneFiber_line_compact {n : ℕ} (a : Space (n+1) → ℝ)
    (hc : HasCompactSupport a) (w : Sphere (n+1)) (y : Space n) :
    HasCompactSupport (fun r : ℝ => a (hyperplaneFrame w (y,r))) := by
  apply HasCompactSupport.intro (hc.image (show Continuous
    (fun x : Space (n+1) => inner ℝ x (w : Space (n+1))) by fun_prop))
  intro r hr
  by_contra hn
  apply hr
  exact ⟨hyperplaneFrame w (y,r), subset_tsupport a hn, hyperplaneFrame_inner w (y,r)⟩

theorem hyperplaneRealFiber_compact {n : ℕ} (a : Space (n+1) → ℝ)
    (hc : HasCompactSupport a) (w : Sphere (n+1)) :
    HasCompactSupport (hyperplaneRealFiber a w) := by
  apply HasCompactSupport.intro (hc.image (contDiff_hyperplaneProjection w).continuous)
  intro y hy
  apply integral_eq_zero_of_ae
  filter_upwards with r
  by_contra hn
  exact hy ⟨hyperplaneFrame w (y,r), subset_tsupport a hn, hyperplaneProjection_frame w y r⟩

theorem hyperplaneRealFiber_smooth {n : ℕ} (a : Space (n+1) → ℝ)
    (hc : HasCompactSupport a) (ha : ContDiff ℝ (⊤ : ℕ∞) a) (w : Sphere (n+1)) :
    ContDiff ℝ (⊤ : ℕ∞) (hyperplaneRealFiber a w) := by
  let g : Space n → ℝ → ℝ := fun y r => a (hyperplaneFrame w (y,r))
  let K := (fun x : Space (n+1) => inner ℝ x (w : Space (n+1))) '' tsupport a
  have hK : IsCompact K := hc.image (by fun_prop)
  have hgs : ∀ y r, y ∈ (univ : Set (Space n)) → r ∉ K → g y r = 0 := by
    intro y r _ hr
    by_contra hn
    exact hr ⟨hyperplaneFrame w (y,r), subset_tsupport a hn, hyperplaneFrame_inner w (y,r)⟩
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry g) (univ ×ˢ univ) :=
    (ha.comp (contDiff_hyperplaneFrame w)).contDiffOn
  have h := contDiffOn_convolution_right_with_param_comp (μ := (volume : Measure ℝ))
    (ContinuousLinearMap.mul ℝ ℝ) (v := fun _ : Space n => (0 : ℝ)) contDiffOn_const
    isOpen_univ hK hgs (f := fun _ : ℝ => (1 : ℝ)) (continuous_const.locallyIntegrable) hg
  rw [contDiffOn_univ] at h
  convert h using 1
  funext y
  simp only [convolution, ContinuousLinearMap.mul_apply', one_mul, zero_sub, g, hyperplaneRealFiber]
  exact (integral_neg_eq_self (fun r : ℝ => a (hyperplaneFrame w (y,r))) volume).symm

noncomputable def hyperplaneSchwartzFiber {n : ℕ} (a : Space (n+1) → ℝ)
    (hc : HasCompactSupport a) (ha : ContDiff ℝ (⊤ : ℕ∞) a) (w : Sphere (n+1)) :
    𝓢(Space n, ℝ) :=
  (hyperplaneRealFiber_compact a hc w).toSchwartzMap (hyperplaneRealFiber_smooth a hc ha w)

theorem hyperplaneSchwartzFiber_nonneg {n : ℕ} (a : Space (n+1) → ℝ)
    (hc : HasCompactSupport a) (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hn : ∀ x, 0 ≤ a x)
    (w : Sphere (n+1)) (y : Space n) : 0 ≤ hyperplaneSchwartzFiber a hc ha w y :=
  integral_nonneg (fun _ => hn _)

theorem hyperplaneSchwartzFiber_density {n : ℕ} (a : Space (n+1) → ℝ)
    (hc : HasCompactSupport a) (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hn : ∀ x, 0 ≤ a x)
    (w : Sphere (n+1)) (y : Space n) :
    ENNReal.ofReal (hyperplaneSchwartzFiber a hc ha w y) =
      hyperplaneFiberDensity (fun x => ENNReal.ofReal (a x)) w y := by
  apply ofReal_integral_eq_lintegral_ofReal
  · exact (ha.continuous.comp ((contDiff_hyperplaneFrame w).continuous.comp
      (by fun_prop))).integrable_of_hasCompactSupport (hyperplaneFiber_line_compact a hc w y)
  · exact Filter.Eventually.of_forall (fun r => hn _)

end Falconer

end OAI
