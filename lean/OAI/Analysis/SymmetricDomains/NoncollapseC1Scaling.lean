import Mathlib
import OAI.Analysis.SymmetricDomains.CompactPeakRatio

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
namespace Release061
open Set Filter Metric
open scoped Topology NNReal Pointwise

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem real_approximatesLinearOn_of_fderiv_close {s : Set E} (hs : Convex ℝ s)
    {f : E → F} (L : E →L[ℝ] F) {c : ℝ≥0}
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hd : ∀ x ∈ s, ‖fderiv ℝ f x-L‖ ≤ c) :
    ApproximatesLinearOn f L s c := by
  apply LipschitzOnWith.approximatesLinearOn
  apply hs.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
  · intro x hx
    exact (hf x hx).sub L.differentiableAt
  · intro x hx
    change ‖fderiv ℝ (fun y => f y-L y) x‖ ≤ (c : ℝ)
    simpa only [fderiv_fun_sub (hf x hx) L.differentiableAt,L.fderiv] using hd x hx

theorem real_stable_image_ball [CompleteSpace E] [Nontrivial F]
    {f : E → F} (L : E ≃L[ℝ] F) {x : E} {y : F} {R : ℝ} (hR : 0 < R)
    (hf : ∀ z ∈ closedBall x R, DifferentiableAt ℝ f z)
    (hd : ∀ z ∈ closedBall x R,
      ‖fderiv ℝ f z-(L : E →L[ℝ] F)‖ ≤ ‖(L.symm : F →L[ℝ] E)‖⁻¹/2)
    (hc : dist y (f x) < ‖(L.symm : F →L[ℝ] E)‖⁻¹*R/4) :
    ball y (‖(L.symm : F →L[ℝ] E)‖⁻¹*R/4) ⊆ f '' closedBall x R := by
  let c : ℝ≥0 := ⟨‖(L.symm : F →L[ℝ] E)‖⁻¹/2, by positivity⟩
  have ha : ApproximatesLinearOn f (L : E →L[ℝ] F) (closedBall x R) c :=
    real_approximatesLinearOn_of_fderiv_close (c := c) (f := f)
      (convex_closedBall x R) (L : E →L[ℝ] F) hf hd
  have hsur := ha.surjOn_closedBall_of_nonlinearRightInverse L.toNonlinearRightInverse hR.le Subset.rfl
  intro z hz
  apply hsur
  change dist z (f x) ≤ (‖(L.symm : F →L[ℝ] E)‖⁻¹ -
    ‖(L.symm : F →L[ℝ] E)‖⁻¹/2)*R
  have hz' := mem_ball.mp hz
  have ht := dist_triangle z y (f x)
  linarith

theorem noncollapse_of_C1_scaling [CompleteSpace E] [Nontrivial F]
    {Ω : Set F} {ψ : E → F} {Ψ : ℝ → E → F} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (J : E ≃L[ℝ] F) (hJ : fderiv ℝ ψ 0 = (J : E →L[ℝ] F))
    (hcont : ContinuousAt (fderiv ℝ ψ) 0)
    (hderiv : TendstoUniformlyOn (fun t => fderiv ℝ (Ψ t)) (fderiv ℝ ψ)
      (𝓝[Set.Ioi 0] 0) (closedBall 0 r₀))
    (hcenter : Tendsto (fun t => Ψ t 0) (𝓝[Set.Ioi 0] 0) (𝓝 (ψ 0)))
    (hdiff : ∀ᶠ t in 𝓝[Set.Ioi 0] 0, ∀ x ∈ closedBall 0 r₀,
      DifferentiableAt ℝ (Ψ t) x)
    (himage : ∀ᶠ t in 𝓝[Set.Ioi 0] 0, ∀ x ∈ closedBall 0 r₀, t • Ψ t x ∈ Ω) :
    ∃ c C t₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < t₀ ∧ ∀ t, 0 < t → t < t₀ →
      ∃ a : F, ‖a‖ ≤ C*t ∧ ball a (c*t) ⊆ Ω := by
  let A : ℝ := ‖(J.symm : F →L[ℝ] E)‖⁻¹
  have hA : 0 < A := inv_pos.mpr J.symm.norm_pos
  have hnear : ∀ᶠ x in 𝓝 (0 : E), ‖fderiv ℝ ψ x-(J : E →L[ℝ] F)‖ < A/4 := by
    have ht : Tendsto (fun x => ‖fderiv ℝ ψ x-(J : E →L[ℝ] F)‖)
        (𝓝 (0 : E)) (𝓝 0) := by
      simpa [hJ] using (hcont.sub_const (J : E →L[ℝ] F)).norm
    exact (tendsto_order.mp ht).2 (A/4) (by positivity)
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp hnear
  let R : ℝ := min r₀ (ε/2)
  have hR : 0 < R := lt_min hr₀ (half_pos hε)
  have hRr : closedBall (0 : E) R ⊆ closedBall 0 r₀ :=
    closedBall_subset_closedBall (min_le_left _ _)
  have hRε : closedBall (0 : E) R ⊆ ball 0 ε :=
    closedBall_subset_ball (lt_of_le_of_lt (min_le_right _ _) (by linarith))
  let c : ℝ := A*R/4
  have hc : 0 < c := by positivity
  let C : ℝ := ‖ψ 0‖+1
  have hC : 0 < C := by positivity
  have hbd : ∀ᶠ t in 𝓝[Set.Ioi 0] 0, ‖Ψ t 0‖ < C :=
    (tendsto_order.mp hcenter.norm).2 C (by dsimp [C]; linarith)
  have hevent : ∀ᶠ t in 𝓝[Set.Ioi 0] 0,
      ‖Ψ t 0‖ < C ∧ ball (Ψ t 0) c ⊆ Ψ t '' closedBall 0 R ∧
        ∀ x ∈ closedBall 0 R, t • Ψ t x ∈ Ω := by
    filter_upwards [hbd, hdiff, himage,
      Metric.tendstoUniformlyOn_iff.mp hderiv (A/4) (by positivity)] with t ht hdt hit hclose
    refine ⟨ht, ?_, fun x hx => hit x (hRr hx)⟩
    apply real_stable_image_ball J hR (fun x hx => hdt x (hRr hx)) ?_ ?_
    · intro x hx
      have he : ‖fderiv ℝ (Ψ t) x-fderiv ℝ ψ x‖ < A/4 := by
        simpa only [dist_eq_norm, norm_sub_rev] using hclose x (hRr hx)
      have hn := hsub (hRε hx)
      change ‖fderiv ℝ ψ x-(J : E →L[ℝ] F)‖ < A/4 at hn
      have htri : ‖fderiv ℝ (Ψ t) x-(J : E →L[ℝ] F)‖ ≤
          ‖fderiv ℝ (Ψ t) x-fderiv ℝ ψ x‖ + ‖fderiv ℝ ψ x-(J : E →L[ℝ] F)‖ := by
        simpa only [dist_eq_norm] using dist_triangle (fderiv ℝ (Ψ t) x)
          (fderiv ℝ ψ x) (J : E →L[ℝ] F)
      change ‖fderiv ℝ (Ψ t) x-(J : E →L[ℝ] F)‖ ≤ A/2
      linarith
    · simpa only [dist_self] using hc
  obtain ⟨t₀,ht₀,hsmall⟩ := Metric.mem_nhdsWithin_iff.mp hevent
  refine ⟨c,C,t₀,hc,hC,ht₀,?_⟩
  intro t ht htt
  have htb : t ∈ ball (0 : ℝ) t₀ := by simpa [mem_ball,Real.dist_eq,abs_of_pos ht] using htt
  obtain ⟨hb,hball,hi⟩ := hsmall ⟨htb,ht⟩
  refine ⟨t • Ψ t 0,?_,?_⟩
  · rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    nlinarith
  · have heq : ball (t • Ψ t 0) (c*t) = t • ball (Ψ t 0) c := by
      rw [_root_.smul_ball ht.ne']; congr 1
      rw [Real.norm_eq_abs,abs_of_pos ht,mul_comm]
    rw [heq]
    rintro y ⟨z,hz,rfl⟩
    obtain ⟨x,hx,rfl⟩ := hball hz
    exact hi x hx

end Release061

end

end OAI
