import OAI.Geometry.Perimeter.Regularity.EllipticFamilyEstimate
import OAI.Geometry.Perimeter.Regularity.EllipticLocality

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

 theorem linear_gradient_holder_global {θ δ K : ℝ}
    (hθ : 0<θ) (hθ' : θ ≤ 1/2) (hK : 1 ≤ K)
    (hc : LinearContractionProperty n θ δ K)
    {A : Euc n → Euc n →L[ℝ] Euc n} (hA : Continuous A)
    {F : Euc n → Euc n} (hF : Continuous F) (hFc : HasCompactSupport F)
    {f : Euc n → ℝ} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    {U : Set (Euc n)} (hU : IsOpen U) {p : Euc n} (hp : p∈U)
    (heq : WeakLinearEquation A f F U)
    (hAm : GeometricHolderAt θ A p) (hFm : GeometricHolderAt θ F p)
    (hnear : ‖ContinuousLinearMap.id ℝ (Euc n)-A p‖ < min δ (1/2)) :
    GeometricHolderAt θ (gradient f) p := by
  have hθ1 : θ<1 := by linarith
  have hcn : ContinuousAt (fun x ↦ ‖ContinuousLinearMap.id ℝ (Euc n)-A x‖) p :=
    (continuousAt_const.sub hA.continuousAt).norm
  obtain ⟨τ,hτ,hτn⟩ := Metric.eventually_nhds_iff.mp (hcn.eventually (gt_mem_nhds hnear))
  obtain ⟨S,hS,hSU⟩ := Metric.isOpen_iff.mp hU p hp
  let a := 1/(32*K^2)
  have ha : 0<a := by dsimp [a]; positivity
  obtain ⟨b,hb,hbs,hbm⟩ := (hAm.prodMk hθ.le hFm).shrink_amplitude hθ ha (lt_min hτ hS)
  let r := b/8
  have hr : 0<r := by dsimp [r]; positivity
  have hrb : 4*r<b := by dsimp [r]; linarith
  have hbS : b ≤ S := hbs.trans (min_le_right _ _)
  have hbτ : b ≤ τ := hbs.trans (min_le_left _ _)
  obtain ⟨B,hB,hBb⟩ := compact_continuous_bound hf.continuous hfc
  obtain ⟨N,hN,hNb⟩ := compact_continuous_bound hF hFc
  have hsmall : 32*K^2*a ≤ 1 := by dsimp [a]; rw [mul_one_div_cancel (by positivity : 32*K^2≠0)]
  have hh := linear_family_C1_limit hθ hθ1 hK hc ha.le ha.le hr hsmall
    (p := p) (A := fun _ ↦ A) (f := fun _ ↦ f) (F := fun _ ↦ F)
    (fun _ ↦ hA) (fun _ ↦ hf) (fun _ ↦ hF)
    (fun _ ↦ heq.mono ((Metric.ball_subset_ball (hrb.le.trans hbS)).trans hSU))
    (fun _ x hx ↦ (hτn ((Metric.mem_ball.mp hx).trans_le (hrb.le.trans hbτ))).le)
    (fun _ x hx j y hy ↦ ?_) (fun _ x ↦ by simpa only [Real.norm_eq_abs] using hBb x)
    (fun _ x ↦ hNb x) (g := f) (fun _ _ ↦ tendsto_const_nhds)
  · exact hh.2
  · have hθj : θ^j ≤ 1 := pow_le_one₀ hθ.le hθ1.le
    have hxb : x∈Metric.ball p b := Metric.closedBall_subset_ball (by linarith) hx
    have hyb : y∈Metric.ball p b := by
      have ht := dist_triangle y x p
      have hhx := Metric.mem_closedBall.mp hx
      have hhy := Metric.mem_ball.mp hy
      rw [Metric.mem_ball]
      nlinarith [mul_le_mul_of_nonneg_right hθj hr.le]
    have hxy : dist x y ≤ θ^j*b := by
      rw [dist_comm]
      exact (Metric.mem_ball.mp hy).le.trans (mul_le_mul_of_nonneg_left (by linarith : r≤b) (pow_nonneg hθ.le _))
    have hm := hbm j x hxb y hyb hxy
    simp only [Prod.dist_eq,max_le_iff] at hm
    exact ⟨(dist_eq_norm (A x) (A y)) ▸ hm.1,by simpa only [dist_eq_norm,norm_sub_rev] using hm.2⟩

 theorem linear_gradient_holder {θ δ K : ℝ}
    (hθ : 0<θ) (hθ' : θ ≤ 1/2) (hK : 1 ≤ K)
    (hc : LinearContractionProperty n θ δ K)
    {A : Euc n → Euc n →L[ℝ] Euc n} {F : Euc n → Euc n}
    {f : Euc n → ℝ} {U : Set (Euc n)} (hU : IsOpen U) {p : Euc n} (hp : p∈U)
    (hA : GeoC θ 0 A U) (hF : GeoC θ 0 F U) (hf : ContDiffOn ℝ 1 f U)
    (heq : WeakLinearEquation A f F U)
    (hnear : ‖ContinuousLinearMap.id ℝ (Euc n)-A p‖ < min δ (1/2)) :
    GeometricHolderAt θ (gradient f) p := by
  obtain ⟨W,hW,hpW,hWU,B,g,G,hB,hBc,hg,hgc,hG,hGc,heB,heg,heG⟩ :=
    local_compact_triple hU hp (contDiffOn_zero.mpr hA.1) hf (contDiffOn_zero.mpr hF.1)
  have he := (heq.mono hWU).congr hW heB.symm heg.symm heG.symm
  have hBm := (hA.2 p hp).congr hθ.le (Filter.eventually_of_mem (hW.mem_nhds hpW) (fun x hx ↦ (heB hx).symm))
  have hGm := (hF.2 p hp).congr hθ.le (Filter.eventually_of_mem (hW.mem_nhds hpW) (fun x hx ↦ (heG hx).symm))
  have hm := linear_gradient_holder_global hθ hθ' hK hc hB.continuous hG.continuous hGc hg hgc
    hW hpW he hBm hGm (by rwa [heB hpW])
  exact hm.congr hθ.le (Filter.eventually_of_mem (hW.mem_nhds hpW) (fun x hx ↦ gradient_eqOn hW heg hx))

 theorem linear_geoC_one {θ δ K : ℝ} (hθ : 0<θ) (hθ' : θ ≤ 1/2) (hK : 1 ≤ K)
    (hc : LinearContractionProperty n θ δ K)
    {A : Euc n → Euc n →L[ℝ] Euc n} {F : Euc n → Euc n}
    {f : Euc n → ℝ} {U : Set (Euc n)} (hU : IsOpen U)
    (hA : GeoC θ 0 A U) (hF : GeoC θ 0 F U) (hf : ContDiffOn ℝ 1 f U)
    (heq : WeakLinearEquation A f F U)
    (hnear : ∀ p∈U, ‖ContinuousLinearMap.id ℝ (Euc n)-A p‖ < min δ (1/2)) :
    GeoC θ 1 f U := by
  have hg : GeoC θ 0 (gradient f) U := ⟨
    (InnerProductSpace.toDual ℝ (Euc n)).symm.continuous.comp_continuousOn
      (hf.continuousOn_fderiv_of_isOpen hU (by norm_num)),
    fun p hp ↦ linear_gradient_holder hθ hθ' hK hc hU hp hA hF hf heq (hnear p hp)⟩
  refine ⟨hf,geoC_zero_of_C1 hθ.le hθ' hU hf,fun e ↦ ?_⟩
  have hh := hg.linear hθ.le hU (innerSL ℝ e)
  apply hh.congr hθ.le hU
  intro x hx
  dsimp only
  rw [innerSL_apply_apply,real_inner_comm,inner_gradient_left]

end RPISingularHarnack

end

end OAI
