import Mathlib
import OAI.Analysis.SymmetricDomains.MontelExpandingDomains

namespace OAI


namespace Release061
open Set Filter Metric
open scoped Topology NNReal
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem tendstoUniformlyOn_fderiv_half_ball
    {f : ℕ → E → F} {g : E → F} {c : E} {R : ℝ} (hR : 0 < R)
    (hf : ∀ᶠ j in atTop, DifferentiableOn ℂ (f j) (ball c R))
    (hg : DifferentiableOn ℂ g (ball c R))
    (hfg : TendstoUniformlyOn f g atTop (ball c R)) :
    TendstoUniformlyOn (fun j => fderiv ℂ (f j)) (fderiv ℂ g) atTop (ball c (R/2)) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hf,Metric.tendstoUniformlyOn_iff.mp hfg (ε*R/8) (by positivity)] with j hj he
  intro x hx
  have hb : ∀ z ∈ ball c R, ‖f j z-g z‖ ≤ ε*R/8 := by
    intro z hz
    exact le_of_lt (by simpa only [dist_eq_norm,norm_sub_rev] using he z hz)
  have hest := bounded_fderiv_on_half_ball hR (hj.sub hg) hb hx
  have hxR : x ∈ ball c R := ball_subset_ball (by linarith) hx
  rw [fderiv_sub (hj.differentiableAt (isOpen_ball.mem_nhds hxR))
    (hg.differentiableAt (isOpen_ball.mem_nhds hxR))] at hest
  rw [dist_eq_norm,norm_sub_rev]
  apply hest.trans_lt
  field_simp
  nlinarith

theorem tendstoLocallyUniformlyOn_fderiv [ProperSpace E] [CompleteSpace F]
    {S : Set E} (hS : IsOpen S) {f : ℕ → E → F} {g : E → F}
    (hfg : TendstoLocallyUniformlyOn f g atTop S)
    (hf : ∀ x ∈ S, ∃ W ∈ 𝓝 x, ∀ᶠ j in atTop, DifferentiableOn ℂ (f j) W) :
    TendstoLocallyUniformlyOn (fun j => fderiv ℂ (f j)) (fderiv ℂ g) atTop S := by
  have hg := differentiableOn_of_locally_uniform_limit hS hfg hf
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro x hx
  obtain ⟨W,hW,hhol⟩ := hf x hx
  obtain ⟨R,hR,hsub⟩ := Metric.mem_nhds_iff.mp (inter_mem hW (hS.mem_nhds hx))
  have hball : ball x (R/2) ⊆ W ∩ S :=
    fun y hy => hsub (ball_subset_ball (by linarith) hy)
  have hc : TendstoUniformlyOn f g atTop (ball x (R/2)) := by
    apply (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      (isCompact_closedBall x (R/2))).mp (hfg.mono (fun y hy => ?_)) |>.mono
    · exact ball_subset_closedBall
    · exact (hsub (closedBall_subset_ball (by linarith) hy)).2
  refine ⟨ball x ((R/2)/2),mem_nhdsWithin_of_mem_nhds
    (ball_mem_nhds _ (by positivity)),?_⟩
  exact tendstoUniformlyOn_fderiv_half_ball (half_pos hR)
    (hhol.mono (fun _ hj => hj.mono (fun y hy => (hball hy).1)))
    (hg.mono (fun y hy => (hball hy).2)) hc

theorem approximatesLinearOn_of_fderiv_close {s : Set E} (hs : Convex ℝ s)
    {f : E → F} (L : E →L[ℂ] F) {c : ℝ≥0}
    (hf : ∀ x ∈ s, DifferentiableAt ℂ f x)
    (hd : ∀ x ∈ s, ‖fderiv ℂ f x-L‖ ≤ c) :
    ApproximatesLinearOn f L s c := by
  apply LipschitzOnWith.approximatesLinearOn
  apply hs.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℂ)
  · intro x hx
    exact (hf x hx).sub L.differentiableAt
  · intro x hx
    change ‖fderiv ℂ (fun y => f y-L y) x‖ ≤ (c : ℝ)
    simpa only [fderiv_fun_sub (hf x hx) L.differentiableAt,L.fderiv] using hd x hx

theorem stable_image_ball [CompleteSpace E] [Nontrivial F]
    {f : E → F} (L : E ≃L[ℂ] F) {x : E} {y : F} {R : ℝ} (hR : 0 < R)
    (hf : ∀ z ∈ closedBall x R, DifferentiableAt ℂ f z)
    (hd : ∀ z ∈ closedBall x R,
      ‖fderiv ℂ f z-(L : E →L[ℂ] F)‖ ≤ ‖(L.symm : F →L[ℂ] E)‖⁻¹/2)
    (hc : dist y (f x) < ‖(L.symm : F →L[ℂ] E)‖⁻¹*R/4) :
    ball y (‖(L.symm : F →L[ℂ] E)‖⁻¹*R/4) ⊆ f '' closedBall x R := by
  let c : ℝ≥0 := ⟨‖(L.symm : F →L[ℂ] E)‖⁻¹/2, by positivity⟩
  have ha : ApproximatesLinearOn f (L : E →L[ℂ] F) (closedBall x R) c :=
    approximatesLinearOn_of_fderiv_close (c := c) (f := f)
      (convex_closedBall x R) (L : E →L[ℂ] F) hf hd
  have hsur := ha.surjOn_closedBall_of_nonlinearRightInverse L.toNonlinearRightInverse hR.le Subset.rfl
  intro z hz
  apply hsur
  change dist z (f x) ≤ (‖(L.symm : F →L[ℂ] E)‖⁻¹ -
    ‖(L.symm : F →L[ℂ] E)‖⁻¹/2)*R
  have hz' := mem_ball.mp hz
  have ht := dist_triangle z y (f x)
  linarith

theorem eventually_image_ball [CompleteSpace E] [ProperSpace E] [CompleteSpace F]
    {S : Set E} (hS : IsOpen S) {f : ℕ → E → F} {g : E → F}
    (hfg : TendstoLocallyUniformlyOn f g atTop S)
    (hf : ∀ x ∈ S, ∃ W ∈ 𝓝 x, ∀ᶠ j in atTop, DifferentiableOn ℂ (f j) W)
    {x : E} (hx : x ∈ S) (L : E ≃L[ℂ] F)
    (hL : fderiv ℂ g x = (L : E →L[ℂ] F))
    (hdg : ContinuousAt (fderiv ℂ g) x) :
    ∃ r : ℝ, 0 < r ∧ ∃ R : ℝ, 0 < R ∧ closedBall x R ⊆ S ∧
      ∀ᶠ j in atTop, ball (g x) r ⊆ f j '' closedBall x R := by
  rcases subsingleton_or_nontrivial F with hF | hF
  · obtain ⟨R,hR,hsub⟩ := Metric.mem_nhds_iff.mp (hS.mem_nhds hx)
    refine ⟨1,by norm_num,R/2,half_pos hR,
      (closedBall_subset_ball (by linarith)).trans hsub,Filter.Eventually.of_forall ?_⟩
    intro j y hy
    exact ⟨x,mem_closedBall_self (by positivity),Subsingleton.elim _ _⟩
  let A : ℝ := ‖(L.symm : F →L[ℂ] E)‖⁻¹
  have hA : 0 < A := inv_pos.mpr L.symm.norm_pos
  have hnear : ∀ᶠ z in 𝓝 x, ‖fderiv ℂ g z-(L : E →L[ℂ] F)‖ < A/4 := by
    have ht : Tendsto (fun z => ‖fderiv ℂ g z-(L : E →L[ℂ] F)‖) (𝓝 x) (𝓝 0) := by
      simpa [hL] using (hdg.sub_const (L : E →L[ℂ] F)).norm
    exact (tendsto_order.mp ht).2 (A/4) (by positivity)
  obtain ⟨W,hW,hhol⟩ := hf x hx
  obtain ⟨R,hR,hsub⟩ := Metric.mem_nhds_iff.mp (inter_mem (hS.mem_nhds hx) (inter_mem hW hnear))
  have hbsub : ball x R ⊆ S := fun z hz => (hsub hz).1
  have hclsub : closedBall x (R/2) ⊆ ball x R := closedBall_subset_ball (by linarith)
  have hconv := tendstoLocallyUniformlyOn_fderiv hS hfg hf
  have hdunif : TendstoUniformlyOn (fun j => fderiv ℂ (f j)) (fderiv ℂ g) atTop
      (closedBall x (R/2)) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      (isCompact_closedBall x (R/2))).mp (hconv.mono (hclsub.trans hbsub))
  have hcenter : ∀ᶠ j in atTop, dist (g x) (f j x) < A*(R/2)/4 := by
    have ht : Tendsto (fun j => dist (g x) (f j x)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => g x) atTop (𝓝 (g x))).dist (hfg.tendsto_at hx)
    exact (tendsto_order.mp ht).2 _ (by positivity)
  refine ⟨A*(R/2)/4,by positivity,R/2,half_pos hR,hclsub.trans hbsub,?_⟩
  filter_upwards [hhol,hcenter,Metric.tendstoUniformlyOn_iff.mp hdunif (A/4) (by positivity)] with j hj hc hd
  apply stable_image_ball L (half_pos hR) ?_ ?_ hc
  · intro z hz
    exact (hj.mono (fun y hy => (hsub hy).2.1)).differentiableAt
      (isOpen_ball.mem_nhds (hclsub hz))
  · intro z hz
    have he : ‖fderiv ℂ (f j) z-fderiv ℂ g z‖ < A/4 := by
      simpa only [dist_eq_norm,norm_sub_rev] using hd z hz
    have hn := (hsub (hclsub hz)).2.2
    change ‖fderiv ℂ g z-(L : E →L[ℂ] F)‖ < A/4 at hn
    have ht : ‖fderiv ℂ (f j) z-(L : E →L[ℂ] F)‖ ≤
        ‖fderiv ℂ (f j) z-fderiv ℂ g z‖ + ‖fderiv ℂ g z-(L : E →L[ℂ] F)‖ := by
      simpa only [dist_eq_norm] using dist_triangle (fderiv ℂ (f j) z) (fderiv ℂ g z) (L : E →L[ℂ] F)
    change ‖fderiv ℂ (f j) z-(L : E →L[ℂ] F)‖ ≤ A/2
    linarith

theorem continuousAt_fderiv_of_locally_uniform_analytic [ProperSpace E] [CompleteSpace F]
    {S : Set E} (hS : IsOpen S) {f : ℕ → E → F} {g : E → F}
    (hfg : TendstoLocallyUniformlyOn f g atTop S)
    (hf : ∀ x ∈ S, ∃ W ∈ 𝓝 x, ∀ᶠ j in atTop, AnalyticOnNhd ℂ (f j) W)
    {x : E} (hx : x ∈ S) : ContinuousAt (fderiv ℂ g) x := by
  have hdiff : ∀ x ∈ S, ∃ W ∈ 𝓝 x, ∀ᶠ j in atTop, DifferentiableOn ℂ (f j) W := by
    intro x hx
    obtain ⟨W,hW,hF⟩ := hf x hx
    exact ⟨W,hW,hF.mono (fun _ hj => hj.differentiableOn)⟩
  have hconv := tendstoLocallyUniformlyOn_fderiv hS hfg hdiff
  obtain ⟨W,hW,hhol⟩ := hf x hx
  obtain ⟨R,hR,hsub⟩ := Metric.mem_nhds_iff.mp (inter_mem hW (hS.mem_nhds hx))
  have hc : ContinuousOn (fderiv ℂ g) (ball x R) := by
    apply (hconv.mono (fun z hz => (hsub hz).2)).continuousOn
    exact (hhol.mono (fun _ hj => (hj.fderiv.continuousOn.mono
      (fun z hz => (hsub hz).1)))).frequently
  exact hc.continuousAt (ball_mem_nhds _ hR)

end Release061



end OAI
