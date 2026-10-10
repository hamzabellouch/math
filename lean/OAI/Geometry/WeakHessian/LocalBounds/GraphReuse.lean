import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.ChangeLpLp
import OAI.Geometry.WeakHessian.Measure.IntegralExponentialMeasure
import OAI.Geometry.WeakHessian.LocalBounds.Smul
import OAI.Geometry.WeakHessian.LocalBounds.CoreAlgebra
import OAI.Geometry.WeakHessian.HeatFlow.DriftResolvent
import OAI.Geometry.WeakHessian.HeatFlow.LaplacianResolventUnique

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile173
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [BorelSpace X] [CompleteSpace X] [ProperSpace X]
  [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma IsLaplacian.gradient_energy {u A : X → ℝ} (hu : IsLaplacian m u A) :
    ‖hu.1.2.2.toLp (weakGradient m u)‖^2 = -(∫ x, A x*u x ∂m) := by
  rw [norm_toLp_sq_eq_integral,← integral_congr_ae (gamma_self u)]
  exact hu.2.2 u hu.1

omit [BorelSpace X] [CompleteSpace X] [ProperSpace X]
  [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma IsLaplacian.gradient_norm_sq_le {u A : X → ℝ} (hu : IsLaplacian m u A) :
    ‖hu.1.2.2.toLp (weakGradient m u)‖^2 ≤ ‖hu.1.1.toLp u‖*‖hu.2.1.toLp A‖ := by
  have hinner : (∫ x, A x*u x ∂m) = ⟪hu.1.1.toLp u,hu.2.1.toLp A⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hu.1.1.coeFn_toLp,hu.2.1.coeFn_toLp] with x hx hy
    simp only [hx,hy]
    rfl
  rw [hu.gradient_energy,hinner]
  exact (neg_le_abs _).trans (abs_real_inner_le_norm _ _)

omit [ProperSpace X] [SigmaFinite m] in
lemma graph_tendsto_gradient_difference (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {un An : ℕ → X → ℝ} {u A : X → ℝ}
    (hn : ∀ n, IsLaplacian m (un n) (An n)) (hu : IsLaplacian m u A)
    (ht : Tendsto (fun n => (hn n).1.1.toLp (un n)) atTop (𝓝 (hu.1.1.toLp u)))
    (hAt : Tendsto (fun n => (hn n).2.1.toLp (An n)) atTop (𝓝 (hu.2.1.toLp A))) :
    Tendsto (fun n => ‖((hn n).sub hfinite hpar hu).1.2.2.toLp
      (weakGradient m (fun x => un n x-u x))‖) atTop (𝓝 0) := by
  have hU : Tendsto (fun n => ‖(hn n).1.1.toLp (un n)-hu.1.1.toLp u‖) atTop (𝓝 0) := by
    simpa using (ht.sub_const (hu.1.1.toLp u)).norm
  have hA : Tendsto (fun n => ‖(hn n).2.1.toLp (An n)-hu.2.1.toLp A‖) atTop (𝓝 0) := by
    simpa using (hAt.sub_const (hu.2.1.toLp A)).norm
  have hb (n : ℕ) := ((hn n).sub hfinite hpar hu).gradient_norm_sq_le
  have hb' (n : ℕ) : ‖((hn n).sub hfinite hpar hu).1.2.2.toLp
      (weakGradient m (fun x => un n x-u x))‖^2 ≤
        ‖(hn n).1.1.toLp (un n)-hu.1.1.toLp u‖ *
        ‖(hn n).2.1.toLp (An n)-hu.2.1.toLp A‖ := by
    have eu : ((hn n).sub hfinite hpar hu).1.1.toLp (fun x => un n x-u x) =
        (hn n).1.1.toLp (un n)-hu.1.1.toLp u := by
      simpa only [Pi.sub_def] using (hn n).1.1.toLp_sub hu.1.1
    have ea : ((hn n).sub hfinite hpar hu).2.1.toLp (fun x => An n x-A x) =
        (hn n).2.1.toLp (An n)-hu.2.1.toLp A := by
      simpa only [Pi.sub_def] using (hn n).2.1.toLp_sub hu.2.1
    simpa only [eu,ea] using hb n
  have hs := squeeze_zero (fun n => sq_nonneg _) hb' (by simpa using hU.mul hA)
  have H := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using H

omit [ProperSpace X] [SigmaFinite m] in
lemma graph_tendsto_weakGradient (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {un An : ℕ → X → ℝ} {u A : X → ℝ}
    (hn : ∀ n, IsLaplacian m (un n) (An n)) (hu : IsLaplacian m u A)
    (ht : Tendsto (fun n => (hn n).1.1.toLp (un n)) atTop (𝓝 (hu.1.1.toLp u)))
    (hAt : Tendsto (fun n => (hn n).2.1.toLp (An n)) atTop (𝓝 (hu.2.1.toLp A))) :
    Tendsto (fun n => (hn n).1.2.2.toLp (weakGradient m (un n))) atTop
      (𝓝 (hu.1.2.2.toLp (weakGradient m u))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => ?_) (graph_tendsto_gradient_difference hfinite hpar hn hu ht hAt)
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [Lp.coeFn_sub ((hn n).1.2.2.toLp (weakGradient m (un n)))
      (hu.1.2.2.toLp (weakGradient m u)), (hn n).1.2.2.coeFn_toLp,
    hu.1.2.2.coeFn_toLp,((hn n).sub hfinite hpar hu).1.2.2.coeFn_toLp,
    weakGradient_dist_le hfinite (hn n).1.2.1 hu.1.2.1,
    weakGradient_nonneg (m := m) (fun x => un n x-u x)] with x hs hn' hu' hd hab hp
  rw [hs,Pi.sub_apply,hn',hu',hd,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hp]
  exact hab

section
omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
  [TopologicalSpace.SeparableSpace X] [SigmaFinite m]

lemma tendsto_toLp_mul_bounded {fn : ℕ → X → ℝ} {f b : X → ℝ}
    (hn : ∀ n, MemLp (fn n) 2 m) (hf : MemLp f 2 m)
    (hb : AEStronglyMeasurable b m) {B : ℝ} (hB : ∀ᵐ x ∂m, |b x| ≤ B)
    (ht : Tendsto (fun n => (hn n).toLp (fn n)) atTop (𝓝 (hf.toLp f))) :
    Tendsto (fun n => (memLp_mul_bounded (hn n) hb hB).toLp (fun x => fn n x*b x))
      atTop (𝓝 ((memLp_mul_bounded hf hb hB).toLp (fun x => f x*b x))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hzero : Tendsto (fun n => |B| * ‖(hn n).toLp (fn n)-hf.toLp f‖) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul ((ht.sub_const (hf.toLp f)).norm))
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hzero
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub ((memLp_mul_bounded (hn n) hb hB).toLp _) ((memLp_mul_bounded hf hb hB).toLp _),
    (memLp_mul_bounded (hn n) hb hB).coeFn_toLp,(memLp_mul_bounded hf hb hB).coeFn_toLp,
    Lp.coeFn_sub ((hn n).toLp _) (hf.toLp _),(hn n).coeFn_toLp,hf.coeFn_toLp,hB]
    with x hs hfn hf' hd hn' hff hx
  rw [hs,Pi.sub_apply,hfn,hf',hd,Pi.sub_apply,hn',hff,← sub_mul]
  simp only [Real.norm_eq_abs,abs_mul]
  exact (mul_le_mul_of_nonneg_left (hx.trans (le_abs_self _)) (abs_nonneg _)).trans_eq
    (mul_comm _ _)

lemma integral_mul_eq_inner {f g : X → ℝ} (hf : MemLp f 2 m) (hg : MemLp g 2 m) :
    (∫ x, f x*g x ∂m) = ⟪hg.toLp g,hf.toLp f⟫_ℝ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hx hy
  simp only [hx,hy]
  rfl

lemma tendsto_integral_mul_L2 {fn gn : ℕ → X → ℝ} {f g : X → ℝ}
    (hfn : ∀ n, MemLp (fn n) 2 m) (hf : MemLp f 2 m)
    (hgn : ∀ n, MemLp (gn n) 2 m) (hg : MemLp g 2 m)
    (htf : Tendsto (fun n => (hfn n).toLp (fn n)) atTop (𝓝 (hf.toLp f)))
    (htg : Tendsto (fun n => (hgn n).toLp (gn n)) atTop (𝓝 (hg.toLp g))) :
    Tendsto (fun n => ∫ x, fn n x*gn n x ∂m) atTop (𝓝 (∫ x, f x*g x ∂m)) := by
  simpa only [integral_mul_eq_inner (hfn _) (hgn _),integral_mul_eq_inner hf hg] using
    htg.inner htf

end

omit [ProperSpace X] [SigmaFinite m] in
lemma graph_tendsto_gamma (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {un An : ℕ → X → ℝ} {u A ξ : X → ℝ}
    (hn : ∀ n, IsLaplacian m (un n) (An n)) (hu : IsLaplacian m u A)
    {L : ℝ≥0} (hξ : LipschitzWith L ξ)
    (ht : Tendsto (fun n => (hn n).1.1.toLp (un n)) atTop (𝓝 (hu.1.1.toLp u)))
    (hAt : Tendsto (fun n => (hn n).2.1.toLp (An n)) atTop (𝓝 (hu.2.1.toLp A))) :
    Tendsto (fun n => (memLp_gamma_of_lipschitz hfinite hpar hξ (hn n).1).toLp (gamma m ξ (un n)))
      atTop (𝓝 ((memLp_gamma_of_lipschitz hfinite hpar hξ hu.1).toLp (gamma m ξ u))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht0 := graph_tendsto_gradient_difference hfinite hpar hn hu ht hAt
  have htB : Tendsto (fun n => (L:ℝ)*‖((hn n).sub hfinite hpar hu).1.2.2.toLp
      (weakGradient m (fun x => un n x-u x))‖) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul ht0
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) htB
  have he : (memLp_gamma_of_lipschitz hfinite hpar hξ (hn n).1).toLp (gamma m ξ (un n)) -
      (memLp_gamma_of_lipschitz hfinite hpar hξ hu.1).toLp (gamma m ξ u) =
      (memLp_gamma_of_lipschitz hfinite hpar hξ ((hn n).sub hfinite hpar hu).1).toLp
        (gamma m ξ (fun x => un n x-u x)) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub ((memLp_gamma_of_lipschitz hfinite hpar hξ (hn n).1).toLp _)
        ((memLp_gamma_of_lipschitz hfinite hpar hξ hu.1).toLp _),
      (memLp_gamma_of_lipschitz hfinite hpar hξ (hn n).1).coeFn_toLp,
      (memLp_gamma_of_lipschitz hfinite hpar hξ hu.1).coeFn_toLp,
      (memLp_gamma_of_lipschitz hfinite hpar hξ ((hn n).sub hfinite hpar hu).1).coeFn_toLp,
      gamma_comm (m := m) ξ (fun x => un n x-u x),
      gamma_sub_left hfinite hpar (hn n).1.2.1 hu.1.2.1 (localSobolev_of_lipschitz hfinite hξ),
      gamma_comm (m := m) ξ (un n),gamma_comm (m := m) ξ u] with x hs h1 h2 h3 hc hd hc1 hc2
    rw [hs,Pi.sub_apply,h1,h2,h3,hc,hd,← hc1,← hc2]
  rw [he]
  exact norm_gamma_toLp_le hfinite hpar hξ ((hn n).sub hfinite hpar hu).1

def graphBochner (m : Measure X) (u A ξ B : X → ℝ) : ℝ :=
  (1/2)*(∫ x, B x*gamma m u u x ∂m) +
    (∫ x, A x*gamma m ξ u x ∂m) + ∫ x, ξ x*(A x)^2 ∂m

omit [ProperSpace X] [SigmaFinite m] in
lemma graphBochner_tendsto (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {un An : ℕ → X → ℝ} {u A ξ B : X → ℝ}
    (hn : ∀ n, IsLaplacian m (un n) (An n)) (hu : IsLaplacian m u A)
    {L : ℝ≥0} (hξ : LipschitzWith L ξ)
    {C D : ℝ} (hC : ∀ x, |ξ x| ≤ C) (hB : AEStronglyMeasurable B m)
    (hD : ∀ᵐ x ∂m, |B x| ≤ D)
    (ht : Tendsto (fun n => (hn n).1.1.toLp (un n)) atTop (𝓝 (hu.1.1.toLp u)))
    (hAt : Tendsto (fun n => (hn n).2.1.toLp (An n)) atTop (𝓝 (hu.2.1.toLp A))) :
    Tendsto (fun n => graphBochner m (un n) (An n) ξ B) atTop
      (𝓝 (graphBochner m u A ξ B)) := by
  have hDt := graph_tendsto_weakGradient hfinite hpar hn hu ht hAt
  have hξM := hξ.continuous.aestronglyMeasurable (μ := m)
  have hξB : ∀ᵐ x ∂m, |ξ x| ≤ C := ae_of_all _ hC
  have h1 := tendsto_integral_mul_L2 (fun n => memLp_mul_bounded (hn n).1.2.2 hB hD)
    (memLp_mul_bounded hu.1.2.2 hB hD) (fun n => (hn n).1.2.2) hu.1.2.2
    (tendsto_toLp_mul_bounded _ _ hB hD hDt) hDt
  have h1' : Tendsto (fun n => ∫ x, B x*gamma m (un n) (un n) x ∂m) atTop
      (𝓝 (∫ x, B x*gamma m u u x ∂m)) := by
    have he (v : X → ℝ) : (∫ x, B x*gamma m v v x ∂m) =
        ∫ x, (weakGradient m v x*B x)*weakGradient m v x ∂m := by
      apply integral_congr_ae
      filter_upwards [gamma_self (m := m) v] with x hx
      rw [hx]; ring
    simpa only [he] using h1
  have h2 := tendsto_integral_mul_L2 (fun n => (hn n).2.1) hu.2.1
    (fun n => memLp_gamma_of_lipschitz hfinite hpar hξ (hn n).1)
    (memLp_gamma_of_lipschitz hfinite hpar hξ hu.1) hAt
    (graph_tendsto_gamma hfinite hpar hn hu hξ ht hAt)
  have h3 := tendsto_integral_mul_L2 (fun n => memLp_mul_bounded (hn n).2.1 hξM hξB)
    (memLp_mul_bounded hu.2.1 hξM hξB) (fun n => (hn n).2.1) hu.2.1
    (tendsto_toLp_mul_bounded _ _ hξM hξB hAt) hAt
  have h3' : Tendsto (fun n => ∫ x, ξ x*(An n x)^2 ∂m) atTop
      (𝓝 (∫ x, ξ x*(A x)^2 ∂m)) := by
    have he (v : X → ℝ) : (∫ x, ξ x*(v x)^2 ∂m) = ∫ x, (v x*ξ x)*v x ∂m := by
      congr 1
      funext x
      ring
    simpa only [he] using h3
  exact (h1'.const_mul (1/2) |>.add h2).add h3'

omit [ProperSpace X] [SigmaFinite m] in
lemma graph_tendsto_weighted_gamma (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {un An : ℕ → X → ℝ} {u A b : X → ℝ}
    (hn : ∀ n, IsLaplacian m (un n) (An n)) (hu : IsLaplacian m u A)
    (hb : AEStronglyMeasurable b m) {B : ℝ} (hB : ∀ᵐ x ∂m, |b x| ≤ B)
    (ht : Tendsto (fun n => (hn n).1.1.toLp (un n)) atTop (𝓝 (hu.1.1.toLp u)))
    (hAt : Tendsto (fun n => (hn n).2.1.toLp (An n)) atTop (𝓝 (hu.2.1.toLp A))) :
    Tendsto (fun n => ∫ x, b x*gamma m (un n) (un n) x ∂m) atTop
      (𝓝 (∫ x, b x*gamma m u u x ∂m)) := by
  have hD := graph_tendsto_weakGradient hfinite hpar hn hu ht hAt
  have H := tendsto_integral_mul_L2 (fun n => memLp_mul_bounded (hn n).1.2.2 hb hB)
    (memLp_mul_bounded hu.1.2.2 hb hB) (fun n => (hn n).1.2.2) hu.1.2.2
    (tendsto_toLp_mul_bounded _ _ hb hB hD) hD
  have he (v : X → ℝ) : (∫ x, b x*gamma m v v x ∂m) =
      ∫ x, (weakGradient m v x*b x)*weakGradient m v x ∂m := by
    apply integral_congr_ae
    filter_upwards [gamma_self (m := m) v] with x hx
    rw [hx]; ring
  simpa only [he] using H

omit [ProperSpace X] [SigmaFinite m] in
lemma graphBochner_bound_of_approx (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {un An : ℕ → X → ℝ} {u A ξ B b : X → ℝ}
    (hn : ∀ n, IsLaplacian m (un n) (An n)) (hu : IsLaplacian m u A)
    {L : ℝ≥0} (hξ : LipschitzWith L ξ)
    {C D E : ℝ} (hC : ∀ x, |ξ x| ≤ C) (hB : AEStronglyMeasurable B m)
    (hD : ∀ᵐ x ∂m, |B x| ≤ D) (hb : AEStronglyMeasurable b m)
    (hE : ∀ᵐ x ∂m, |b x| ≤ E)
    (ht : Tendsto (fun n => (hn n).1.1.toLp (un n)) atTop (𝓝 (hu.1.1.toLp u)))
    (hAt : Tendsto (fun n => (hn n).2.1.toLp (An n)) atTop (𝓝 (hu.2.1.toLp A)))
    (hcore : ∀ n, (∫ x, b x*gamma m (un n) (un n) x ∂m) ≤
      graphBochner m (un n) (An n) ξ B) :
    (∫ x, b x*gamma m u u x ∂m) ≤ graphBochner m u A ξ B := by
  exact le_of_tendsto_of_tendsto (graph_tendsto_weighted_gamma hfinite hpar hn hu hb hE ht hAt)
    (graphBochner_tendsto hfinite hpar hn hu hξ hC hB hD ht hAt) (Eventually.of_forall hcore)

omit [ProperSpace X] [SigmaFinite m] in
lemma graphBochner_eq_core (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u A ξ B q : X → ℝ}
    (hu : IsLaplacian m u A) (hξA : IsLaplacian m ξ B)
    {L : ℝ≥0} (hξ : LipschitzWith L ξ) {C : ℝ} (hC : ∀ x, |ξ x| ≤ C)
    (hq : Sobolev m q) (heq : gamma m u u =ᵐ[m] (fun x => 2*q x)) :
    graphBochner m u A ξ B =
      -(∫ x, gamma m ξ q x ∂m) + ∫ x, (ξ x*A x+gamma m ξ u x)*A x ∂m := by
  have hfirst : (1/2)*(∫ x, B x*gamma m u u x ∂m) = -(∫ x, gamma m ξ q x ∂m) := by
    have he : (∫ x, B x*gamma m u u x ∂m) = 2*(∫ x, B x*q x ∂m) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [heq] with x hx
      rw [hx]; ring
    rw [he,hξA.2.2 q hq]
    ring
  have hprod : MemLp (fun x => A x*ξ x) 2 m :=
    memLp_mul_bounded hu.2.1 hξ.continuous.aestronglyMeasurable (ae_of_all _ hC)
  have hIA : Integrable (fun x => (ξ x*A x)*A x) m := by
    have htmp : Integrable (fun x => (A x*ξ x)*A x) m := hprod.integrable_mul hu.2.1
    convert htmp using 1
    funext x
    ring
  have hIG : Integrable (fun x => gamma m ξ u x*A x) m :=
    (memLp_gamma_of_lipschitz hfinite hpar hξ hu.1).integrable_mul hu.2.1
  unfold graphBochner
  rw [hfirst]
  simp_rw [add_mul]
  rw [integral_add hIA hIG]
  have hE1 : (∫ x, (ξ x*A x)*A x ∂m) = ∫ x, ξ x*(A x)^2 ∂m := by
    congr 1; funext x; ring
  rw [hE1]
  have hE2 : (∫ x, gamma m ξ u x*A x ∂m) = ∫ x, A x*gamma m ξ u x ∂m := by
    congr 1; funext x; ring
  rw [hE2]
  ring

omit [ProperSpace X] [SigmaFinite m] in
lemma graphBochner_eq_BE (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u A ξ B : X → ℝ}
    (hu : IsLaplacian m u A) (hAS : Sobolev m A)
    {L : ℝ≥0} (hξ : LipschitzWith L ξ) {C : ℝ} (hC : ∀ x, |ξ x| ≤ C) :
    graphBochner m u A ξ B = (1/2)*(∫ x, B x*gamma m u u x ∂m) -
      ∫ x, ξ x*gamma m u A x ∂m := by
  have hξS := localSobolev_of_lipschitz hfinite hξ
  have hξB : ∀ᵐ x ∂m, |ξ x| ≤ C := ae_of_all _ hC
  have hDξ : ∀ᵐ x ∂m, |weakGradient m ξ x| ≤ (L:ℝ) := by
    filter_upwards [weakGradient_le_lipschitz hfinite hξ,weakGradient_nonneg (m := m) ξ] with x hx hn
    rwa [abs_of_nonneg hn]
  have htest := hu.2.2 (fun x => A x*ξ x) (hAS.mul_bounded hfinite hξS hξB hDξ)
  have he : gamma m u (fun x => A x*ξ x) =ᵐ[m]
      (fun x => A x*gamma m ξ u x+ξ x*gamma m u A x) := by
    filter_upwards [gamma_comm (m := m) u (fun x => A x*ξ x),
      gamma_mul_left hfinite hpar hAS.2.1 hξS hu.1.2.1 hξB hDξ,
      gamma_comm (m := m) A u] with x hc hp ha
    rw [hc,hp,ha]
  have hI1 : Integrable (fun x => A x*gamma m ξ u x) m :=
    hu.2.1.integrable_mul (memLp_gamma_of_lipschitz hfinite hpar hξ hu.1)
  have hI2 : Integrable (fun x => ξ x*gamma m u A x) m :=
    (integrable_gamma hfinite hu.1 hAS).bdd_mul hξ.continuous.aestronglyMeasurable
      (by simpa only [Real.norm_eq_abs] using hξB)
  rw [integral_congr_ae he,integral_add hI1 hI2] at htest
  have heA : (∫ x, A x*(A x*ξ x) ∂m) = ∫ x, ξ x*(A x)^2 ∂m := by
    congr 1; funext x; ring
  rw [heA] at htest
  unfold graphBochner
  linarith

omit [ProperSpace X] [SigmaFinite m] in
lemma graph_tendsto_reweight (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {un An : ℕ → X → ℝ} {u A V : X → ℝ}
    (hn : ∀ n, IsLaplacian m (un n) (An n)) (hu : IsLaplacian m u A)
    {L : ℝ≥0} (hV : LipschitzWith L V) {B : ℝ} (hB : ∀ x, |V x| ≤ B)
    (ht : Tendsto (fun n => (hn n).1.1.toLp (un n)) atTop (𝓝 (hu.1.1.toLp u)))
    (hAt : Tendsto (fun n => (hn n).2.1.toLp (An n)) atTop (𝓝 (hu.2.1.toLp A))) :
    Tendsto (fun n => ((hn n).reweight hfinite hpar hV hB).1.1.toLp (un n)) atTop
      (𝓝 ((hu.reweight hfinite hpar hV hB).1.1.toLp u)) ∧
    Tendsto (fun n => ((hn n).reweight hfinite hpar hV hB).2.1.toLp
      (fun x => An n x+gamma m V (un n) x)) atTop
      (𝓝 ((hu.reweight hfinite hpar hV hB).2.1.toLp (fun x => A x+gamma m V u x))) := by
  obtain ⟨hm,hν⟩ := exponentialMeasure_comparable (m := m) hB
  refine ⟨tendsto_toLp_changeMeasure ENNReal.ofReal_ne_top hν (fun n => (hn n).1.1) hu.1.1 ht, ?_⟩
  have hg := graph_tendsto_gamma hfinite hpar hn hu hV ht hAt
  have hsum : Tendsto (fun n => ((hn n).2.1.add
      (memLp_gamma_of_lipschitz hfinite hpar hV (hn n).1)).toLp
      (fun x => An n x+gamma m V (un n) x)) atTop
      (𝓝 ((hu.2.1.add (memLp_gamma_of_lipschitz hfinite hpar hV hu.1)).toLp
        (fun x => A x+gamma m V u x))) := by
    have en (n : ℕ) : ((hn n).2.1.add
        (memLp_gamma_of_lipschitz hfinite hpar hV (hn n).1)).toLp
        (fun x => An n x+gamma m V (un n) x) =
        (hn n).2.1.toLp (An n)+(memLp_gamma_of_lipschitz hfinite hpar hV (hn n).1).toLp
          (gamma m V (un n)) := by
      simpa only [Pi.add_def] using (hn n).2.1.toLp_add
        (memLp_gamma_of_lipschitz hfinite hpar hV (hn n).1)
    have e0 : (hu.2.1.add (memLp_gamma_of_lipschitz hfinite hpar hV hu.1)).toLp
        (fun x => A x+gamma m V u x) = hu.2.1.toLp A+
        (memLp_gamma_of_lipschitz hfinite hpar hV hu.1).toLp (gamma m V u) := by
      simpa only [Pi.add_def] using hu.2.1.toLp_add
        (memLp_gamma_of_lipschitz hfinite hpar hV hu.1)
    simp_rw [en,e0]
    exact hAt.add hg
  exact tendsto_toLp_changeMeasure ENNReal.ofReal_ne_top hν _ _ hsum

def OriginalTestGraphCore (m : Measure X) : Prop :=
  ∀ (u A : X → ℝ) (hu : IsLaplacian m u A),
    ∃ (gs : ℕ → X → ℝ) (htest : ∀ n, IsTestFunction m (gs n)),
      (∀ n, HasCompactSupport (gs n)) ∧
      Tendsto (fun n => (laplacian_isLaplacian (htest n).1).1.1.toLp (gs n)) atTop
        (𝓝 (hu.1.1.toLp u)) ∧
      Tendsto (fun n => (laplacian_isLaplacian (htest n).1).2.1.toLp (laplacian m (gs n)))
        atTop (𝓝 (hu.2.1.toLp A))

omit [ProperSpace X] [SigmaFinite m] in
lemma graphBochner_reweight_eq_drift (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {V g ξ B : X → ℝ}
    (hg : IsTestFunction m g) (hq : Sobolev m (fun y => gamma m g g y/2))
    {L T : ℝ≥0} (hV : LipschitzWith L V) (hξ : LipschitzWith T ξ)
    {C D : ℝ} (hC : ∀ x, |V x| ≤ C) (hD : ∀ x, |ξ x| ≤ D)
    (hξA : IsLaplacian (exponentialMeasure m V) ξ B) :
    graphBochner (exponentialMeasure m V) g (fun x => laplacian m g x+gamma m V g x) ξ B =
      driftBochner m V g ξ := by
  obtain ⟨hm,hν⟩ := exponentialMeasure_comparable (m := m) hC
  have hnfinite := hfinite.of_le_smul (C := (Real.exp C).toNNReal) hν
  have hnpar := hpar.change_measure (C := (Real.exp C).toNNReal)
    (D := (Real.exp C).toNNReal) hm hν
  have hgA := (laplacian_isLaplacian hg.1).reweight hfinite hpar hV hC
  have hqn := (sobolev_exponentialMeasure_iff hC (fun y => gamma m g g y/2)).mp hq
  have heq : gamma (exponentialMeasure m V) g g =ᵐ[exponentialMeasure m V]
      (fun x => 2*(gamma m g g x/2)) := by
    apply (Measure.absolutelyContinuous_of_le_smul hν).ae_eq
    filter_upwards [gamma_exponentialMeasure (m := m) hC g g] with x hx
    rw [hx]; ring
  rw [graphBochner_eq_core hnfinite hnpar hgA hξA hξ hD hqn heq]
  rw [integral_exponentialMeasure hV.continuous.aemeasurable,
    integral_exponentialMeasure hV.continuous.aemeasurable]
  unfold driftBochner
  congr 1
  · congr 1
    apply integral_congr_ae
    filter_upwards [gamma_exponentialMeasure (m := m) hC ξ (fun y => gamma m g g y/2)] with x hx
    rw [hx]
  · apply integral_congr_ae
    filter_upwards [gamma_exponentialMeasure (m := m) hC ξ g] with x hx
    rw [hx]
    ring

omit [ProperSpace X] [SigmaFinite m] in
lemma OriginalTestGraphCore.reweight_approx (hcore : OriginalTestGraphCore m)
    (hfinite : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {V u A : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    {C : ℝ} (hC : ∀ x, |V x| ≤ C) (hu : IsLaplacian (exponentialMeasure m V) u A) :
    ∃ (gs : ℕ → X → ℝ) (htest : ∀ n, IsTestFunction m (gs n)),
      (∀ n, HasCompactSupport (gs n)) ∧
      Tendsto (fun n => ((laplacian_isLaplacian (htest n).1).reweight hfinite hpar hV hC).1.1.toLp
        (gs n)) atTop (𝓝 (hu.1.1.toLp u)) ∧
      Tendsto (fun n => ((laplacian_isLaplacian (htest n).1).reweight hfinite hpar hV hC).2.1.toLp
        (fun x => laplacian m (gs n) x+gamma m V (gs n) x)) atTop (𝓝 (hu.2.1.toLp A)) := by
  have hu0 := hu.of_exponentialMeasure hfinite hpar hV hC
  obtain ⟨gs,htest,hsupp,ht,hAt⟩ := hcore u (fun x => A x-gamma m V u x) hu0
  refine ⟨gs,htest,hsupp,?_⟩
  have H := graph_tendsto_reweight hfinite hpar (fun n => laplacian_isLaplacian (htest n).1)
    hu0 hV hC ht hAt
  have he : (fun x => A x-gamma m V u x+gamma m V u x) = A := by funext x; ring
  aesop

end WeakHessian

end
end InlinedFile173

end OAI
