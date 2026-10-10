import OAI.Geometry.Perimeter.Regularity.NonlinearDerivativeGain
import OAI.Geometry.Perimeter.Regularity.GeoComposition

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

 theorem norm_apply_difference (A B : Euc n →L[ℝ] Euc n) (v w : Euc n) :
    ‖A v-B w‖ ≤ ‖A‖*‖v-w‖+‖A-B‖*‖w‖ := by
  have he : A v-B w=A (v-w)+(A-B) w := by simp only [map_sub,sub_apply]; abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (A.le_opNorm _) ((A-B).le_opNorm _))

 theorem linear_directional_gain {θ δ K : ℝ}
    (hθ : 0<θ) (hθ' : θ ≤ 1/2) (hK : 1 ≤ K)
    (hc : LinearContractionProperty n θ δ K)
    {A : Euc n → Euc n →L[ℝ] Euc n} (hA : ContDiff ℝ 1 A) (hAc : HasCompactSupport A)
    {F : Euc n → Euc n} (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F)
    {f : Euc n → ℝ} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    {U : Set (Euc n)} (hU : IsOpen U) {p : Euc n} (hp : p∈U)
    (heq : WeakLinearEquation A f F U)
    (hmod : GeometricHolderAt θ (gradient f) p)
    (hDA : GeometricHolderAt θ (fderiv ℝ A) p)
    (hDF : GeometricHolderAt θ (fderiv ℝ F) p)
    (hnear : ‖ContinuousLinearMap.id ℝ (Euc n)-A p‖ < min δ (1/2))
    (e : Euc n) :
    ∃ r : ℝ, 0<r ∧ Metric.ball p r⊆U ∧
      ContDiffOn ℝ 1 (fun x ↦ fderiv ℝ f x e) (Metric.ball p r) ∧
      GeometricHolderAt θ (gradient (fun x ↦ fderiv ℝ f x e)) p := by
  have hθ1 : θ<1 := by linarith
  have hAm := geometricHolderAt_of_C1_on hθ.le hθ' isOpen_univ hA.contDiffOn (mem_univ p)
  have hJ := hAm.prodMk hθ.le (hDA.prodMk hθ.le (hDF.prodMk hθ.le hmod))
  have hcn : ContinuousAt (fun x ↦ ‖ContinuousLinearMap.id ℝ (Euc n)-A x‖) p :=
    (continuousAt_const.sub hA.continuous.continuousAt).norm
  obtain ⟨τ,hτ,hτn⟩ := Metric.eventually_nhds_iff.mp (hcn.eventually (gt_mem_nhds hnear))
  obtain ⟨S,hS,hSU⟩ := Metric.isOpen_iff.mp hU p hp
  let a := 1/(32*K^2)
  have ha : 0<a := by dsimp [a]; positivity
  obtain ⟨b,hb,hbs,hbm⟩ := hJ.shrink_amplitude hθ ha (lt_min hτ hS)
  let r := b/8
  have hr : 0<r := by dsimp [r]; positivity
  have hrb : 5*r<b := by dsimp [r]; linarith
  have hbS : b ≤ S := hbs.trans (min_le_right _ _)
  have hbτ : b ≤ τ := hbs.trans (min_le_left _ _)
  have hshift (i : ℕ) (R : ℝ) (x : Euc n) (hx : x∈Metric.ball p R)
      (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : x+t•(quotientSteps r e i•e)∈Metric.ball p (R+r) := by
    rw [Metric.mem_ball,dist_eq_norm]
    have he : x+t•(quotientSteps r e i•e)-p=(x-p)+t•(quotientSteps r e i•e) := by abel
    rw [he]
    have hnorm : ‖t•(quotientSteps r e i•e)‖ ≤ ‖quotientSteps r e i•e‖ := by
      rw [norm_smul,Real.norm_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg _) ht.2
    have hh := norm_add_le (x-p) (t•(quotientSteps r e i•e))
    have hd := Metric.mem_ball.mp hx
    rw [dist_eq_norm] at hd
    linarith [quotientSteps_shift_lt hr e i]
  have hm (j : ℕ) (x : Euc n) (hx : x∈Metric.ball p b) (y : Euc n)
      (hy : y∈Metric.ball p b) (hxy : dist x y ≤ θ^j*b) :
      ‖A x-A y‖ ≤ a*(1/2)^j ∧ ‖fderiv ℝ A x-fderiv ℝ A y‖ ≤ a*(1/2)^j ∧
      ‖fderiv ℝ F x-fderiv ℝ F y‖ ≤ a*(1/2)^j ∧ ‖gradient f x-gradient f y‖ ≤ a*(1/2)^j := by
    have hh := hbm j x hx y hy hxy
    simp only [Prod.dist_eq,max_le_iff] at hh
    exact ⟨(dist_eq_norm (A x) (A y)) ▸ hh.1,
      (dist_eq_norm (fderiv ℝ A x) (fderiv ℝ A y)) ▸ hh.2.1,
      (dist_eq_norm (fderiv ℝ F x) (fderiv ℝ F y)) ▸ hh.2.2.1,
      (dist_eq_norm (gradient f x) (gradient f y)) ▸ hh.2.2.2⟩
  obtain ⟨Bg,hBg,hBgall⟩ := compact_C1_gradient_bound hf hfc
  have : CompleteSpace (Euc n →L[ℝ] Euc n) := ContinuousLinearMap.instCompleteSpace
  obtain ⟨LA,hLA,hLAall⟩ := compact_C1_fderiv_bound hA hAc
  obtain ⟨LF,hLF,hLFall⟩ := compact_C1_fderiv_bound hF hFc
  let v : ℕ → Euc n → ℝ := fun i ↦ differenceQuotient f e (quotientSteps r e i)
  let H : ℕ → Euc n → Euc n := fun i x ↦ vectorQuotient F e (quotientSteps r e i) x-
    vectorQuotient A e (quotientSteps r e i) x (gradient f (x+quotientSteps r e i•e))
  have hH (i : ℕ) : Continuous (H i) := (vectorQuotient_continuous hF.continuous e _).sub
    ((vectorQuotient_continuous hA.continuous e _).clm_apply
      ((gradient_continuous_C1 hf).comp (continuous_id.add continuous_const)))
  have hv (i : ℕ) : ContDiff ℝ 1 (v i) := differenceQuotient_contDiff hf e _
  have h4b : Metric.ball p (4*r)⊆Metric.ball p b := Metric.ball_subset_ball (by linarith)
  have h4U : Metric.ball p (4*r)⊆U := h4b.trans ((Metric.ball_subset_ball hbS).trans hSU)
  have hE (i : ℕ) : WeakLinearEquation A (v i) (H i) (Metric.ball p (4*r)) :=
    weak_linear_difference hA.continuous hf hF.continuous heq h4U e _ (fun x hx ↦ by
      have hh := hshift i (4*r) x hx 1 (by norm_num)
      simp only [one_smul] at hh
      exact hSU (Metric.ball_subset_ball (by linarith : 4*r+r ≤ S) hh))
  have hN (i : ℕ) (x : Euc n) (hx : x∈Metric.ball p (4*r)) :
      ‖ContinuousLinearMap.id ℝ (Euc n)-A x‖ ≤ min δ (1/2) :=
    (hτn ((Metric.mem_ball.mp (h4b hx)).trans_le hbτ)).le
  let B := a*‖e‖*(1+LA+Bg)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hosc (i : ℕ) (x : Euc n) (hx : x∈Metric.closedBall p r) (j : ℕ)
      (y : Euc n) (hy : y∈Metric.ball x (θ^j*r)) :
      ‖A x-A y‖ ≤ a*(1/2)^j ∧ ‖H i y-H i x‖ ≤ B*(1/2)^j := by
    have hj : θ^j ≤ 1 := pow_le_one₀ hθ.le hθ1.le
    have hx2 : x∈Metric.ball p (2*r) := Metric.mem_ball.mpr
      ((Metric.mem_closedBall.mp hx).trans_lt (by linarith))
    have hy2 : y∈Metric.ball p (2*r) := by
      have hd := dist_triangle y x p
      have hdx := Metric.mem_closedBall.mp hx
      have hdy := Metric.mem_ball.mp hy
      have hrj := mul_le_mul_of_nonneg_right hj hr.le
      rw [Metric.mem_ball]
      linarith
    have h2b : Metric.ball p (2*r)⊆Metric.ball p b := Metric.ball_subset_ball (by linarith)
    have hxy : dist x y ≤ θ^j*b := by
      rw [dist_comm]
      exact (Metric.mem_ball.mp hy).le.trans (mul_le_mul_of_nonneg_left (by dsimp [r]; linarith)
        (pow_nonneg hθ.le j))
    have hsmod (t : ℝ) (ht : t∈Icc (0:ℝ) 1) := hm j
      _ (Metric.ball_subset_ball (by linarith : 2*r+r ≤ b) (hshift i (2*r) x hx2 t ht))
      _ (Metric.ball_subset_ball (by linarith : 2*r+r ≤ b) (hshift i (2*r) y hy2 t ht))
      (by simpa only [dist_add_right] using hxy)
    have hqA := vectorQuotient_difference hA e (quotientSteps_pos hr e i).ne' x y
      (fun t ht ↦ (hsmod t ht).2.1)
    have hqF := vectorQuotient_difference hF e (quotientSteps_pos hr e i).ne' x y
      (fun t ht ↦ (hsmod t ht).2.2.1)
    have hg : ‖gradient f (x+quotientSteps r e i•e)-gradient f (y+quotientSteps r e i•e)‖ ≤ a*(1/2)^j := by
      simpa only [one_smul] using (hsmod 1 (by norm_num)).2.2.2
    have haB := vectorQuotient_bound hA hLA hLAall e (quotientSteps r e i) x
    have hfg := hBgall (y+quotientSteps r e i•e)
    have hap := norm_apply_difference (vectorQuotient A e (quotientSteps r e i) x)
      (vectorQuotient A e (quotientSteps r e i) y) (gradient f (x+quotientSteps r e i•e))
      (gradient f (y+quotientSteps r e i•e))
    have hap' : ‖vectorQuotient A e (quotientSteps r e i) x (gradient f (x+quotientSteps r e i•e))-
        vectorQuotient A e (quotientSteps r e i) y (gradient f (y+quotientSteps r e i•e))‖ ≤
        LA*‖e‖*(a*(1/2)^j)+(a*(1/2)^j*‖e‖)*Bg :=
      hap.trans (add_le_add (mul_le_mul haB hg (norm_nonneg _) (by positivity))
        (mul_le_mul hqA hfg (norm_nonneg _) (by positivity)))
    refine ⟨(hm j x (h2b hx2) y (h2b hy2) hxy).1,?_⟩
    rw [norm_sub_rev]
    have he : H i x-H i y=(vectorQuotient F e (quotientSteps r e i) x-vectorQuotient F e (quotientSteps r e i) y)-
        (vectorQuotient A e (quotientSteps r e i) x (gradient f (x+quotientSteps r e i•e))-
        vectorQuotient A e (quotientSteps r e i) y (gradient f (y+quotientSteps r e i•e))) := by dsimp [H]; abel
    rw [he]
    exact (norm_sub_le _ _).trans ((add_le_add hqF hap').trans_eq (by dsimp [B]; ring))
  have hglobal (i : ℕ) (x : Euc n) : ‖H i x‖ ≤ LF*‖e‖+LA*‖e‖*Bg := by
    apply (norm_sub_le _ _).trans
    apply add_le_add (vectorQuotient_bound hF hLF hLFall e _ x)
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (vectorQuotient_bound hA hLA hLAall e _ x) (hBgall _) (norm_nonneg _) (by positivity))
  obtain ⟨hg,hgmod⟩ := linear_family_C1_limit hθ hθ1 hK hc ha.le hB hr
    (by dsimp [a]; field_simp; norm_num) (fun _ ↦ hA.continuous) hv hH hE hN hosc
    (fun i x ↦ differenceQuotient_bound (hf.differentiable (by simp)) hBg hBgall e _ x) hglobal
    (fun x _ ↦ (differenceQuotient_tendsto (hf.differentiable (by simp)) e x).comp (quotientSteps_tendsto hr e))
  exact ⟨r,hr,(Metric.ball_subset_ball (by linarith : r ≤ 4*r)).trans h4U,hg,hgmod⟩

end RPISingularHarnack

end

end OAI
