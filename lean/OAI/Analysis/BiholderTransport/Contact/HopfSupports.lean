import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.Calculus
import OAI.Analysis.BiholderTransport.LinearAlgebra.HalfCostUniform
import OAI.Analysis.BiholderTransport.Duality.GeometricEnvelope
import OAI.Analysis.BiholderTransport.Contact.MatchedSupports

namespace OAI

noncomputable section
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] in
lemma uniform_cTransform_chart_lower (a : M) :
    ∃ B>0, ∃ r>0,
      ball (extChartAt 𝓘(ℝ,Model n) a a) r ⊆ (extChartAt 𝓘(ℝ,Model n) a).target ∧
      ∀ v : M → ℝ, Continuous v →
        ∀ x∈ball (extChartAt 𝓘(ℝ,Model n) a a) r,
          ∃ L : Model n →L[ℝ] ℝ,
            ∀ y∈ball (extChartAt 𝓘(ℝ,Model n) a a) r,
              cTransform v ((extChartAt 𝓘(ℝ,Model n) a).symm x)+L (y-x)-B*‖y-x‖^2 ≤
                cTransform v ((extChartAt 𝓘(ℝ,Model n) a).symm y) := by
  obtain ⟨B,hB,r,hr,hrT,hjet⟩ := uniform_half_cost_hessian (n := n) a
  refine ⟨2*B,by positivity,r,hr,hrT,?_⟩
  intro v hv x hx
  let χ := extChartAt 𝓘(ℝ,Model n) a
  obtain ⟨p,hp⟩ := nonempty_activeLogs (n := n) hv (χ.symm x)
  let f := chartCost (n := n) a (riemannianExp (χ.symm x) ((1/2:ℝ) • p))
  refine ⟨(-2:ℝ) • fderiv ℝ f x,?_⟩
  intro y hy
  have hrem := first_order_remainder_le_of_hessian_bound (convex_ball _ _) hB.le
    (fun w hw => (hjet x hx p hp.1 w hw).1)
    (fun w hw => (hjet x hx p hp.1 w hw).2) hx hy
  have hlow := active_split_lower_support hv hp.1 hp.2
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1) (χ.symm y)
  change |f y-f x-fderiv ℝ f x (y-x)|≤B*‖y-x‖^2 at hrem
  change -(f y-f x)/(1/2:ℝ)≤cTransform v (χ.symm y)-cTransform v (χ.symm x) at hlow
  have hU := (abs_le.mp hrem).2
  simp only [_root_.smul_apply,smul_eq_mul]
  norm_num at hlow
  nlinarith

lemma uniform_hopfLax_chart_upper (a : M) :
    ∃ B>0, ∃ r>0,
      ball (extChartAt 𝓘(ℝ,Model n) a a) r ⊆ (extChartAt 𝓘(ℝ,Model n) a).target ∧
      ∀ t : ℝ, 0<t → ∀ u : M → ℝ, Continuous u →
        ∀ x∈ball (extChartAt 𝓘(ℝ,Model n) a a) r,
          ∃ U : Model n →L[ℝ] ℝ,
            ∀ y∈ball (extChartAt 𝓘(ℝ,Model n) a a) r,
              hopfLax t u ((extChartAt 𝓘(ℝ,Model n) a).symm y) ≤
                hopfLax t u ((extChartAt 𝓘(ℝ,Model n) a).symm x)+U (y-x)+(B/t)*‖y-x‖^2 := by
  obtain ⟨B,hB,r,hr,hrT,H⟩ := uniform_cTransform_chart_lower (n := n) a
  refine ⟨B,hB,r,hr,hrT,?_⟩
  intro t ht u hu x hx
  obtain ⟨L,hL⟩ := H (fun x => t*u x) (continuous_const.mul hu) x hx
  refine ⟨(-t⁻¹) • L,?_⟩
  intro y hy
  rw [hopfLax_eq_neg_transform hu ht,hopfLax_eq_neg_transform hu ht]
  simp only [_root_.smul_apply,smul_eq_mul]
  have H' := mul_le_mul_of_nonpos_left (hL y hy) (neg_nonpos.mpr (inv_nonneg.mpr ht.le))
  convert H' using 1
  all_goals first | rfl | (simp only [div_eq_mul_inv]; ring)

lemma WeakMTW.uniform_hopfLax_C11 (hmtw : WeakMTW (n := n) (M := M)) (a : M) :
    ∃ B>0, ∃ r>0,
      ball (extChartAt 𝓘(ℝ,Model n) a a) r ⊆ (extChartAt 𝓘(ℝ,Model n) a).target ∧
      ∀ t : ℝ, 0<t → t<1 → ∀ u v : M → ℝ, Continuous u → Continuous v →
        IsCostDualPair u v →
        (∀ x∈ball (extChartAt 𝓘(ℝ,Model n) a a) r,
          DifferentiableAt ℝ (fun z => hopfLax t u ((extChartAt 𝓘(ℝ,Model n) a).symm z)) x) ∧
        LipschitzOnWith (Real.toNNReal (6*(B/t+B/(1-t))))
          (fderiv ℝ (fun z => hopfLax t u ((extChartAt 𝓘(ℝ,Model n) a).symm z)))
          (ball (extChartAt 𝓘(ℝ,Model n) a a) (r/4)) := by
  obtain ⟨B,hB,r,hr,hrT,H⟩ := uniform_hopfLax_chart_upper (n := n) a
  refine ⟨B,hB,r,hr,hrT,?_⟩
  intro t ht ht1 u v hu hv hdual
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let S := ball (χ a) r
  let f := fun z => hopfLax t u (χ.symm z)
  let C := B/t+B/(1-t)
  have hC : 0≤C := by dsimp [C]; positivity
  have hid := hmtw.dual_hopfLax_identity hu hv hdual ht ht1
  have hsup : ∀ x∈S, ∃ L U : Model n →L[ℝ] ℝ, ∀ y∈S,
      f x+L (y-x)-C*‖y-x‖^2≤f y ∧ f y≤f x+U (y-x)+C*‖y-x‖^2 := by
    intro x hx
    obtain ⟨U,hU⟩ := H t ht u hu x hx
    obtain ⟨V,hV⟩ := H (1-t) (sub_pos.mpr ht1) v hv x hx
    refine ⟨-V,U,?_⟩
    intro y hy
    have hUy := hU y hy
    have hVy := hV y hy
    have hf (z : Model n) : hopfLax (1-t) v (χ.symm z) = -f z := by
      dsimp [f]
      rw [hid]
      simp only [neg_neg]
    change f y≤f x+U (y-x)+(B/t)*‖y-x‖^2 at hUy
    rw [hf y,hf x] at hVy
    have htB : 0≤B/t := by positivity
    have htB' : 0≤B/(1-t) := by positivity
    simp only [_root_.neg_apply]
    dsimp only [C]
    constructor
    · nlinarith [mul_nonneg htB (sq_nonneg ‖y-x‖)]
    · nlinarith [mul_nonneg htB' (sq_nonneg ‖y-x‖)]
  have hrem := quadratic_remainder_of_two_supports isOpen_ball hC hsup
  refine ⟨fun x hx => (hrem x hx).1,?_⟩
  change LipschitzOnWith (Real.toNNReal (6*C)) (fderiv ℝ f) (ball (χ a) (r/4))
  have he : Real.toNNReal (6*C) = (⟨6*C, mul_nonneg (by norm_num : (0:ℝ)≤6) hC⟩ : ℝ≥0) := by
    exact Real.toNNReal_of_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤6) hC)
  rw [he]
  exact derivative_lipschitz_of_quadratic_remainder hr hC (fun x hx => (hrem x hx).2)

end WeakMTWTransport

end

end OAI
