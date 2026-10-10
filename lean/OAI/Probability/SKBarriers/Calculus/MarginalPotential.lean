import Mathlib
import OAI.Probability.SKBarriers.Calculus.MarginalVariance
import OAI.Probability.SKBarriers.Calculus.BilinearSchur

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace SK.Analytic
 theorem hasDerivAt_score_comp
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : E → ℝ) (hV : ContDiff ℝ 2 V) {g : ℝ → E} {u : E} {t : ℝ}
    (hg : HasDerivAt g u t) (v : E) :
    HasDerivAt (fun s => fderiv ℝ V (g s) v) (Hessian V (g t) u v) t := by
  have hd : Differentiable ℝ (fderiv ℝ V) :=
    (hV.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h := (hd (g t)).hasFDerivAt.comp_hasDerivAt t hg
  simpa only [map_zero, add_zero, Function.comp_def, Hessian] using
    h.clm_apply (hasDerivAt_const t v)

def marginalPotential {E : Type} (V : E × ℝ → ℝ) (a b : ℝ) (x : E) : ℝ :=
  -Real.log (intervalPartition (fun y => V (x,y)) a b)

theorem contDiff_marginalPotential
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (V : E × ℝ → ℝ) (n : ℕ) (hV : ContDiff ℝ n V) {a b : ℝ} (hab : a < b) :
    ContDiff ℝ n (marginalPotential V a b) := by
  have hp : ContDiff ℝ n (fun z => Real.exp (-V z)) := hV.neg.exp
  have hZ := contDiff_intervalIntegral n (fun z => Real.exp (-V z)) hp a b
  exact (hZ.log (fun x => ne_of_gt (intervalPartition_pos
    (hV.continuous.comp (continuous_const.prodMk continuous_id)) hab))).neg

theorem marginal_hessian_lower
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (V : E × ℝ → ℝ) (hV : ContDiff ℝ 2 V)
    (q : E → ℝ) (hq : q 0 = 0) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ z u s, c * (q u + s^2) ≤ Hessian V z (u,s) (u,s))
    {a b : ℝ} (hab : a < b) (x u : E) :
    c*q u ≤ Hessian (marginalPotential V a b) x u u := by
  let g : ℝ × ℝ → E × ℝ := fun z => (x+z.1 • u, z.2)
  let e₁ : E × ℝ := (u,0)
  let e₂ : E × ℝ := (0,1)
  let v : ℝ → ℝ → ℝ := fun t y => V (g (t,y))
  let v₁ : ℝ → ℝ → ℝ := fun t y => fderiv ℝ V (g (t,y)) e₁
  let v₂ : ℝ → ℝ → ℝ := fun t y => Hessian V (g (t,y)) e₁ e₁
  let w₁ : ℝ → ℝ → ℝ := fun t y => fderiv ℝ V (g (t,y)) e₂
  let w₂ : ℝ → ℝ → ℝ := fun t y => Hessian V (g (t,y)) e₂ e₂
  let hxy : ℝ → ℝ → ℝ := fun t y => Hessian V (g (t,y)) e₂ e₁
  have hg : ContDiff ℝ 2 g := by dsimp only [g]; fun_prop
  have hd : ContDiff ℝ 1 (fderiv ℝ V) := hV.fderiv_right (by norm_num)
  have hdd : Continuous (fderiv ℝ (fderiv ℝ V)) := hd.continuous_fderiv (by norm_num)
  have hvc : Continuous (Function.uncurry v) := hV.continuous.comp hg.continuous
  have hdcont (e : E × ℝ) : Continuous (fun z => fderiv ℝ V (g z) e) :=
    (hd.continuous.comp hg.continuous).clm_apply continuous_const
  have hddcont (e e' : E × ℝ) : Continuous (fun z => Hessian V (g z) e e') :=
    ((hdd.comp hg.continuous).clm_apply continuous_const).clm_apply continuous_const
  have hg₁ (t y : ℝ) : HasDerivAt (fun s => g (s,y)) e₁ t := by
    simpa only [g, e₁, one_smul, id_eq] using
      (((hasDerivAt_id t).smul_const u).const_add x).prodMk (hasDerivAt_const t y)
  have hg₂ (t y : ℝ) : HasDerivAt (fun s => g (t,s)) e₂ y := by
    simpa only [g, e₂, id_eq] using
      (hasDerivAt_const y (x+t • u)).prodMk (hasDerivAt_id y)
  have hvd (t y : ℝ) : HasDerivAt (fun s => v s y) (v₁ t y) t := by
    exact (hV.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt t (hg₁ t y)
  have hv₁d (t y : ℝ) : HasDerivAt (fun s => v₁ s y) (v₂ t y) t :=
    hasDerivAt_score_comp V hV (hg₁ t y) e₁
  have hwd (t y : ℝ) : HasDerivAt (v t) (w₁ t y) y := by
    exact (hV.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt y (hg₂ t y)
  have hw₁d (t y : ℝ) : HasDerivAt (w₁ t) (w₂ t y) y :=
    hasDerivAt_score_comp V hV (hg₂ t y) e₂
  have hv₁yd (t y : ℝ) : HasDerivAt (v₁ t) (hxy t y) y :=
    hasDerivAt_score_comp V hV (hg₂ t y) e₁
  have hs (t y : ℝ) : 0 < w₂ t y ∧ c*q u ≤ v₂ t y - hxy t y^2/w₂ t y := by
    apply bilinear_schur_lower (fderiv ℝ (fderiv ℝ V) (g (t,y)))
      (hV.contDiffAt.isSymmSndFDerivAt (by norm_num)) q hq hc
      (hlower (g (t,y))) u
  have hBL := brascampLieb_interval_schur hab (v 0) (w₁ 0) (w₂ 0) (v₁ 0)
    (hxy 0) (v₂ 0) (hwd 0) (hw₁d 0) (hv₁yd 0)
    ((hddcont e₂ e₂).comp (continuous_const.prodMk continuous_id))
    ((hddcont e₂ e₁).comp (continuous_const.prodMk continuous_id))
    ((hddcont e₁ e₁).comp (continuous_const.prodMk continuous_id))
    (fun y => (hs 0 y).1) (fun y => (hs 0 y).2)
  have hW := contDiff_marginalPotential V 2 hV hab
  have hfirst (t : ℝ) := hasDerivAt_neg_log_intervalPartition v v₁ hvc
    (hdcont e₁) hvd hab t
  have hsecond := hasDerivAt_interval_score v v₁ v₂ hvc (hdcont e₁)
    (hddcont e₁ e₁) hvd hv₁d hab 0
  have hscore : (fun t => fderiv ℝ (marginalPotential V a b) (x+t • u) u) =
      (fun t => intervalMean (v t) (v₁ t) a b) := by
    ext t
    exact (hasDerivAt_affine_comp (marginalPotential V a b)
      (hW.differentiable (by norm_num)) x u t).unique (hfirst t)
  have hsecond' := hasDerivAt_affine_score (marginalPotential V a b) hW x u u 0
  rw [hscore] at hsecond'
  have heq := hsecond'.unique hsecond
  simp only [zero_smul, add_zero] at heq
  rw [heq]
  exact hBL
end SK.Analytic

end
end
end
end
end

end OAI
