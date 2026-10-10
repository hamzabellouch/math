import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarHeatEvolution

namespace OAI

/-! Two integrations by parts transfer the planar Laplacian from the
Gaussian kernel to the compact forcing. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem planarPartial_reflect {f : PlanarPosition → ℝ} (hf : ContDiff ℝ 1 f)
    (r e x : PlanarPosition) :
    planarPartial (fun y => f (r - y)) e x = -planarPartial f e (r - x) := by
  have hd := ((hf.differentiable (by norm_num) (r - x)).hasFDerivAt).comp x
    ((hasFDerivAt_const r x).sub (hasFDerivAt_id x))
  change fderiv ℝ (fun y => f (r - y)) x e = -(fderiv ℝ f (r - x) e)
  rw [show fderiv ℝ (fun y => f (r - y)) x = _ from hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, zero_sub, neg_apply,
    ContinuousLinearMap.id_apply, map_neg]

theorem planarPartial_neg {f : PlanarPosition → ℝ} (hf : ContDiff ℝ 1 f)
    (e x : PlanarPosition) :
    planarPartial (fun y => -f y) e x = -planarPartial f e x := by
  have hd := (hf.differentiable (by norm_num) x).hasFDerivAt.neg
  change fderiv ℝ (fun y => -f y) x e = -(fderiv ℝ f x e)
  rw [show fderiv ℝ (fun y => -f y) x = _ from hd.fderiv]
  simp only [neg_apply]

theorem planarLaplacian_reflect {f : PlanarPosition → ℝ} (hf : ContDiff ℝ 2 f)
    (r x : PlanarPosition) :
    planarLaplacian (fun y => f (r - y)) x = planarLaplacian f (r - x) := by
  apply Finset.sum_congr rfl
  intro a _
  have hp := planarPartial_C1 hf (planarAxis a)
  have hpr : ContDiff ℝ 1 (fun y => planarPartial f (planarAxis a) (r - y)) :=
    hp.comp (contDiff_const.sub contDiff_id)
  rw [show planarPartial (fun y => f (r - y)) (planarAxis a) =
      fun y => -planarPartial f (planarAxis a) (r - y) from
    funext (planarPartial_reflect (hf.of_le (by norm_num)) r (planarAxis a)),
    planarPartial_neg hpr, planarPartial_reflect hp, neg_neg]

theorem planar_integral_mul_laplacian_C2 (f phi : PlanarPosition → ℝ)
    (hf : ContDiff ℝ 2 f) (hphi : ContDiff ℝ 2 phi) (hc : HasCompactSupport phi) :
    (∫ x, f x * planarLaplacian phi x) = ∫ x, planarLaplacian f x * phi x := by
  have hp (g : PlanarPosition → ℝ) (hg : ContDiff ℝ 2 g) (v : PlanarPosition) :
      ContDiff ℝ 1 (planarPartial g v) :=
    (hg.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).clm_apply contDiff_const
  have hpp (g : PlanarPosition → ℝ) (hg : ContDiff ℝ 2 g) (v : PlanarPosition) :
      Continuous (planarPartial (planarPartial g v) v) :=
    (((hp g hg v).fderiv_right (show (0 : WithTop ℕ∞) + 1 ≤ 1 by norm_num)).clm_apply
      contDiff_const).continuous
  have hpc (v : PlanarPosition) : HasCompactSupport (planarPartial phi v) :=
    hc.fderiv_apply ℝ v
  have hppc (v : PlanarPosition) : HasCompactSupport (planarPartial (planarPartial phi v) v) :=
    (hpc v).fderiv_apply ℝ v
  have hleft (v : PlanarPosition) : Integrable (fun x => f x * planarPartial (planarPartial phi v) v x) :=
    (hf.continuous.mul (hpp phi hphi v)).integrable_of_hasCompactSupport (hppc v).mul_left
  have hright (v : PlanarPosition) : Integrable (fun x => planarPartial (planarPartial f v) v x * phi x) :=
    ((hpp f hf v).mul hphi.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hcross (v : PlanarPosition) : Integrable (fun x => planarPartial f v x * planarPartial phi v x) :=
    ((hp f hf v).continuous.mul (hp phi hphi v).continuous).integrable_of_hasCompactSupport
      (hpc v).mul_left
  have hfg (v : PlanarPosition) : Integrable (fun x => f x * planarPartial phi v x) :=
    (hf.continuous.mul (hp phi hphi v).continuous).integrable_of_hasCompactSupport
      (hpc v).mul_left
  have hfpg (v : PlanarPosition) : Integrable (fun x => planarPartial f v x * phi x) :=
    ((hp f hf v).continuous.mul hphi.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hby (v : PlanarPosition) :
      (∫ x, f x * planarPartial (planarPartial phi v) v x) =
        ∫ x, planarPartial (planarPartial f v) v x * phi x := by
    calc
      _ = -(∫ x, planarPartial f v x * planarPartial phi v x) :=
        integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
          (hcross v) (hleft v) (hfg v)
          (fun x _ => hf.differentiable (by norm_num) x)
          (fun x _ => (hp phi hphi v).differentiable (by norm_num) x)
      _ = _ := by
        have h : (∫ x, planarPartial f v x * planarPartial phi v x) =
            -(∫ x, planarPartial (planarPartial f v) v x * phi x) :=
          integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
            (hright v) (hcross v) (hfpg v)
            (fun x _ => (hp f hf v).differentiable (by norm_num) x)
            (fun x _ => hphi.differentiable (by norm_num) x)
        rw [h, neg_neg]
  simp_rw [planarLaplacian, Finset.mul_sum]
  rw [integral_finsetSum _ (fun a _ => hleft (planarAxis a))]
  simp_rw [hby]
  rw [← integral_finsetSum _ (fun a _ => hright (planarAxis a))]
  simp_rw [Finset.sum_mul]

theorem planarLaplacian_continuous {f : PlanarPosition → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (planarLaplacian f) :=
  continuous_finsetSum _ (fun a _ =>
    planarPartial_continuous (planarPartial_C1 hf (planarAxis a)) (planarAxis a))

theorem planarLaplacian_hasCompactSupport {f : PlanarPosition → ℝ} (hc : HasCompactSupport f) :
    HasCompactSupport (planarLaplacian f) := by
  change HasCompactSupport (fun x => ∑ a : Fin 2,
    fderiv ℝ (fun y => fderiv ℝ f y (planarAxis a)) x (planarAxis a))
  have h := HasCompactSupport.finset_sum (s := Finset.univ)
    (fun a _ => (hc.fderiv_apply ℝ (planarAxis a)).fderiv_apply ℝ (planarAxis a))
  simpa only [Finset.sum_fn] using h

theorem planarHeatAverage_hasDerivAt_laplacian {t : ℝ} (ht : 0 < t) (r : PlanarPosition) :
    HasDerivAt (fun s => planarHeatAverage s r)
      (∫ b, planarHeatKernel t b * planarLaplacian planarForcing (r - b)) t := by
  have hf2 : ContDiff ℝ 2 planarForcing := planarForcing_C7.of_le (by norm_num)
  have hr : ContDiff ℝ 2 (fun b : PlanarPosition => planarForcing (r - b)) :=
    hf2.comp (contDiff_const.sub contDiff_id)
  have hrc : HasCompactSupport (fun b : PlanarPosition => planarForcing (r - b)) :=
    planarForcing_hasCompactSupport.comp_homeomorph (Homeomorph.subLeft r)
  have heq : (∫ b, planarHeatTimeDerivative t (r - b) * planarForcing b) =
      ∫ b, planarHeatKernel t b * planarLaplacian planarForcing (r - b) := by
    calc
      _ = ∫ b, planarHeatTimeDerivative t b * planarForcing (r - b) := by
        rw [← integral_sub_left_eq_self _ volume r]
        simp only [sub_sub_self]
      _ = ∫ b, planarLaplacian (planarHeatKernel t) b * planarForcing (r - b) := by
        simp only [planarHeatKernel_laplacian]
      _ = ∫ b, planarHeatKernel t b * planarLaplacian (fun y => planarForcing (r - y)) b :=
        (planar_integral_mul_laplacian_C2 _ _ (planarHeatKernel_C2 t) hr hrc).symm
      _ = _ := by simp only [planarLaplacian_reflect hf2]
  rw [← heq]
  exact planarHeatAverage_hasDerivAt ht r

end ContinuumCoulomb

end

end OAI
