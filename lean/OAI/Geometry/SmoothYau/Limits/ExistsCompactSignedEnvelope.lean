import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.GlobalPrepDualNorm
import OAI.Geometry.SmoothYau.Smoothness.SmDualNorm

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
local instance perturbDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance perturbDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance perturbFormNorm : NormedAddCommGroup (CoordinateForm E) := inferInstance
local instance perturbFormSpace : NormedSpace ℝ (CoordinateForm E) := inferInstance
lemma actualCoordinateHessian_const_mul (g : SmoothMetric E E) {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (s : ℝ) (x v w : E) :
    actualCoordinateHessian g (fun y => s*f y) x v w = s*actualCoordinateHessian g f x v w := by
  let L : ℝ →L[ℝ] ℝ := s • ContinuousLinearMap.id ℝ ℝ
  change actualCoordinateHessian g (fun y => L (f y)) x v w = _
  rw [actualCoordinateHessian_apply,fderiv_second_clm_comp_apply L hf,
    fderiv_clm_comp_apply L hf,actualCoordinateHessian_apply]
  simp only [L,smul_apply,ContinuousLinearMap.id_apply,smul_eq_mul]
  ring

theorem exists_compact_strict_perturbation (g : SmoothMetric E E) {f h : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h) {K : Set E} (hK : IsCompact K)
    (hstrict : ∀ x ∈ K, coordinateMetricGradient g f x ≠ 0 ∧ actualProfileStrict g f x) :
    ∃ ε>0, ∀ s : ℝ, |s|<ε → ∀ x ∈ K,
      coordinateMetricGradient g (fun y => f y+s*h y) x ≠ 0 ∧
      actualProfileStrict g (fun y => f y+s*h y) x := by
  let J : E × ℝ → MetricJet E := fun z =>
    (z.1,actualCoordinateHessian g f z.1+z.2 • actualCoordinateHessian g h z.1,
      fderiv ℝ f z.1+z.2 • fderiv ℝ h z.1)
  have hHf : Continuous (actualCoordinateHessian g f) :=
    continuous_coordinateCovariantSecond _ (contDiff_metricChristoffel g).continuous hf
  have hHh : Continuous (actualCoordinateHessian g h) :=
    continuous_coordinateCovariantSecond _ (contDiff_metricChristoffel g).continuous hh
  have hJ : Continuous J := continuous_fst.prodMk
    (((hHf.comp continuous_fst).add (continuous_snd.smul (hHh.comp continuous_fst))).prodMk
      (((hf.continuous_fderiv (by simp)).comp continuous_fst).add
        (continuous_snd.smul ((hh.continuous_fderiv (by simp)).comp continuous_fst))))
  have hsub : K ×ˢ ({0}:Set ℝ) ⊆ J ⁻¹' {z | metricJetStrict g z} := by
    rintro ⟨x,s⟩ ⟨hx,hs⟩
    simp only [mem_singleton_iff] at hs
    subst s
    simpa only [mem_preimage,mem_ofPred_eq,J,zero_smul,add_zero,metricJetStrict_actual] using hstrict x hx
  obtain ⟨U,V,hU,hV,hKU,h0V,hUV⟩ := generalized_tube_lemma hK isCompact_singleton
    ((isOpen_metricJetStrict g).preimage hJ) hsub
  obtain ⟨ε,hε,hεV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds (h0V (mem_singleton 0)))
  refine ⟨ε,hε,?_⟩
  intro s hs x hx
  have hj := hUV (show (x,s) ∈ U ×ˢ V from
    ⟨hKU hx,hεV (by simpa only [mem_ball,dist_zero_right,Real.norm_eq_abs] using hs)⟩)
  have heH : actualCoordinateHessian g (fun y => f y+s*h y) x =
      actualCoordinateHessian g f x+s • actualCoordinateHessian g h x := by
    ext v w
    rw [actualCoordinateHessian_add g hf (contDiff_const.mul hh),
      actualCoordinateHessian_const_mul g hh]
    rfl
  have heD : fderiv ℝ (fun y => f y+s*h y) x = fderiv ℝ f x+s • fderiv ℝ h x := by
    rw [fderiv_fun_add (hf.differentiable (by simp) x)
      ((contDiff_const.mul hh).differentiable (by simp) x),
      fderiv_const_mul (hh.differentiable (by simp) x)]
  rw [← metricJetStrict_actual,heH,heD]
  exact hj
end


open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_compact_signed_envelope (g : SmoothMetric E E) {f l : E → ℝ}
    (hf : ContDiff ℝ ∞ f) {R : ℝ} (hR : 0<R) (C : ℝ)
    (hmin : ∀ x, C+1≤l x) (heq : ∀ x ∈ closedBall 0 R, f x=l x)
    (hstrict : ∀ x ∈ closedBall 0 R,
      coordinateMetricGradient g f x ≠ 0 ∧ actualProfileStrict g f x) :
    ∃ δ>0, δ≤1/2 ∧ ∃ φ : E → ℝ, ContDiff ℝ ∞ φ ∧
      HasCompactSupport (fun x => φ x-C) ∧
      tsupport (fun x => φ x-C) ⊆ closedBall 0 (3*R/4) ∧
      (∀ x ∈ closedBall 0 (R/3),
        coordinateMetricGradient g φ x ≠ 0 ∧ actualProfileStrict g φ x) ∧
      (∀ x ∈ closedBall 0 (R/8), φ x=l x+δ) ∧
      (∀ x ∉ closedBall 0 (R/3), φ x≤l x-δ) := by
  let β : ContDiffBump (0:E) := ⟨R/8,R/4,by positivity,by linarith⟩
  let χ : ContDiffBump (0:E) := ⟨R/2,3*R/4,by positivity,by linarith⟩
  let h : E → ℝ := fun x => 2*β x-1
  have hh : ContDiff ℝ ∞ h := (contDiff_const.mul β.contDiff).sub contDiff_const
  obtain ⟨ε,hε,hstable⟩ := exists_compact_strict_perturbation g hf hh
    (isCompact_closedBall 0 (R/3)) (fun x hx => hstrict x
      (closedBall_subset_closedBall (by linarith) hx))
  let δ := min (ε/2) (1/2)
  have hδ : 0<δ := lt_min (half_pos hε) (by norm_num)
  have hδε : |δ|<ε := by rw [abs_of_pos hδ]; exact (min_le_left _ _).trans_lt (half_lt_self hε)
  have hδ1 : δ≤1/2 := min_le_right _ _
  let φ : E → ℝ := fun x => C+χ x*(f x-δ-C)+2*δ*β x
  have hφ : ContDiff ℝ ∞ φ :=
    (contDiff_const.add (χ.contDiff.mul ((hf.sub contDiff_const).sub contDiff_const))).add
      (contDiff_const.mul β.contDiff)
  have hcover : tsupport (fun x => φ x-C) ⊆ closedBall 0 (3*R/4) := by
    apply closure_minimal ?_ isClosed_closedBall
    intro x hx
    by_contra hh
    have hχ : χ x=0 := χ.zero_of_le_dist (by
      have hn : 3*R/4 < dist x 0 := by simpa only [mem_closedBall,not_le] using hh
      exact hn.le)
    have hβ : β x=0 := β.zero_of_le_dist (by
      have hn : 3*R/4 < dist x 0 := by simpa only [mem_closedBall,not_le] using hh
      dsimp [β]; linarith)
    exact hx (by simp [φ,hχ,hβ])
  refine ⟨δ,hδ,hδ1,φ,hφ,?_,hcover,?_,?_,?_⟩
  · exact (isCompact_closedBall 0 (3*R/4)).of_isClosed_subset (isClosed_tsupport _) hcover
  · intro x hx
    have heχ := χ.eventuallyEq_one_of_mem_ball (show x ∈ ball 0 χ.rIn from
      closedBall_subset_ball (by dsimp [χ]; linarith) hx)
    have he : φ =ᶠ[𝓝 x] (fun y => f y+δ*h y) := by
      filter_upwards [heχ] with y hy
      dsimp [φ,h]
      change χ y=1 at hy
      rw [hy]
      ring
    have hj := actualJet_eventuallyEq g he
    rw [hj.1,hj.2.2.1]
    exact hstable δ hδε x hx
  · intro x hx
    have hβ := β.one_of_mem_closedBall hx
    have hχ := χ.one_of_mem_closedBall (closedBall_subset_closedBall (by dsimp [χ]; linarith) hx)
    have he := heq x (closedBall_subset_closedBall (by linarith) hx)
    dsimp [φ]
    rw [hβ,hχ,he]
    ring
  · intro x hx
    have hd : R/3 < dist x 0 := by simpa only [mem_closedBall,not_le] using hx
    have hβ : β x=0 := β.zero_of_le_dist (by dsimp [β]; linarith)
    have hlow : C≤l x-δ := by have hm:=hmin x; linarith
    dsimp [φ]
    rw [hβ,mul_zero,add_zero]
    by_cases hz : χ x=0
    · simpa [hz] using hlow
    · have hmem : x ∈ ball 0 χ.rOut := by rwa [←χ.support_eq]
      have he := heq x (ball_subset_closedBall.trans
        (closedBall_subset_closedBall (by dsimp [χ]; linarith)) hmem)
      rw [he]
      have hc := χ.le_one (x:=x)
      have hn := χ.nonneg (x:=x)
      nlinarith

end YauCounterexamples
end

end OAI
