import OAI.MathematicalPhysics.Transonic.Core

namespace OAI

section

namespace SepticProfile.Fuchsian
open Set Filter Metric MeasureTheory
open scoped Topology NNReal

lemma continuous_coordinateMul : Continuous coordinateMul := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro f g
  rw [dist_eq_norm,dist_eq_norm,← coordinateMul_sub]
  simpa only [NNReal.coe_one,one_mul] using norm_coordinateMul_le (f-g)

/-- The regular-singular inverse varies continuously with the positive
indicial shift. Restricting the displayed global extension by max c 1 incurs
no change for the shifts 76-rho>2 used in the selected source family. -/
lemma continuous_radialIntegral_shift (f : analyticDisk) :
    Continuous (fun c : ℝ => radialIntegral (max c 1) f) := by
  have hweight : Continuous (fun p : ℝ×ℝ => p.2 ^ max p.1 1) :=
    continuous_snd.rpow (continuous_fst.max continuous_const)
      (fun p => Or.inr (lt_of_lt_of_le (by norm_num) (le_max_right p.1 1)))
  have hi : Continuous (fun p : ℝ×ℝ => radialIntegrand (max p.1 1) f p.2) := by
    exact hweight.smul ((continuous_dilate f).comp
      ((continuous_projIcc (h := show (0:ℝ)≤1 by norm_num)).comp continuous_snd))
  have hh := continuous_parametric_integral_of_continuous
    (μ := volume) (f := fun c t : ℝ => radialIntegrand (max c 1) f t) hi
    (s := Icc (0:ℝ) 1) isCompact_Icc
  simpa only [radialIntegral,integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)] using hh

lemma continuous_inverse_shift (f : analyticDisk) :
    Continuous (fun c : ℝ => inverse (max c 1) f) :=
  continuous_coordinateMul.comp (continuous_radialIntegral_shift f)

lemma inverse_lipschitz {c : ℝ} (hc : 0≤c) : LipschitzWith 1 (inverse c) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  rw [dist_eq_norm,dist_eq_norm,← inverse_sub hc]
  simpa only [NNReal.coe_one,one_mul] using norm_inverse_le hc (f-g)

lemma continuous_inverse_family {A : Type*} [TopologicalSpace A]
    (c : A → ℝ) (hc : Continuous c) (hc1 : ∀ a, 1≤c a)
    (f : A → analyticDisk) (hf : Continuous f) :
    Continuous (fun a => inverse (c a) (f a)) := by
  rw [continuous_iff_continuousAt]
  intro a
  have hfixed : Continuous (fun b => inverse (c b) (f a)) := by
    convert (continuous_inverse_shift (f a)).comp hc using 1
    funext b
    simp only [Function.comp_apply,max_eq_left (hc1 b)]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he2 : 0<ε/2 := by linarith
  have he1 := (hf.tendsto a).eventually (Metric.ball_mem_nhds (f a) he2)
  have he0 := (hfixed.tendsto a).eventually (Metric.ball_mem_nhds (inverse (c a) (f a)) he2)
  filter_upwards [he1,he0] with b hb hb0
  have hl := (inverse_lipschitz (le_trans (by norm_num) (hc1 b))).dist_le_mul (f b) (f a)
  simp only [NNReal.coe_one,one_mul] at hl
  exact (dist_triangle _ (inverse (c b) (f a)) _).trans_lt
    (by linarith)

/-- Stability of fixed-point selection, used below for the parameterized
sonic analytic family. The conclusion is derived, not a continuity assumption
on the selected germs. -/
lemma continuous_fixedPoint_family {A E : Type*} [TopologicalSpace A]
    [MetricSpace E] (T : A → E → E) (f : A → E)
    (hT : ∀ a, ContractingWith (1/2 : ℝ≥0) (T a))
    (hfix : ∀ a, Function.IsFixedPt (T a) (f a))
    (hcont : ∀ x, Continuous (fun a => T a x)) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro a
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hh := ((hcont (f a)).tendsto a).eventually
    (Metric.ball_mem_nhds (T a (f a)) (by linarith : 0<ε/2))
  filter_upwards [hh] with b hb
  have hbd := (hT b).dist_le_of_fixedPoint (f a) (hfix b)
  rw [hfix a] at hb
  have hd : dist (f a) (T b (f a)) < ε/2 := by simpa only [dist_comm] using hb
  have he : (1:ℝ)-(↑(1/2:ℝ≥0))=1/2 := by norm_num
  rw [he] at hbd
  rw [dist_comm]
  linarith

end SepticProfile.Fuchsian


end

end OAI
