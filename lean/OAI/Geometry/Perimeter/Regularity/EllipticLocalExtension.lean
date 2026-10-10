import OAI.Geometry.Perimeter.Regularity.EllipticDifference

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

 theorem contDiff_cutoff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Euc n → V} {U : Set (Euc n)} (hU : IsOpen U) {k : ℕ∞}
    (hf : ContDiffOn ℝ k f U) {χ : Euc n → ℝ} (hχ : ContDiff ℝ k χ)
    (hsχ : tsupport χ⊆U) : ContDiff ℝ k (fun x ↦ χ x•f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x∈tsupport χ
  · exact hχ.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds (hsχ hx)))
  · apply (contDiffAt_const (c := (0:V))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
    simp only [image_eq_zero_of_notMem_tsupport hy,zero_smul]

 theorem local_compact_extension {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Euc n → V} {U : Set (Euc n)} (hU : IsOpen U) {p : Euc n} (hp : p∈U)
    {k : ℕ∞} (hf : ContDiffOn ℝ k f U) :
    ∃ r : ℝ, 0<r ∧ Metric.closedBall p (4*r)⊆U ∧ ∃ g : Euc n → V,
      ContDiff ℝ k g ∧ HasCompactSupport g ∧ ∀ x∈Metric.ball p (2*r), g x=f x := by
  obtain ⟨s,hs,hsU⟩ := Metric.isOpen_iff.mp hU p hp
  let r := s/8
  let χ : ContDiffBump p := ⟨s/4,s/2,by positivity,by linarith⟩
  have hsc : tsupport χ⊆U := by
    rw [χ.tsupport_eq]
    exact (Metric.closedBall_subset_ball (by dsimp [χ]; linarith)).trans hsU
  refine ⟨r,by dsimp [r]; positivity,?_,fun x ↦ χ x•f x,
    contDiff_cutoff hU hf χ.contDiff hsc,χ.hasCompactSupport.smul_right,?_⟩
  · exact (Metric.closedBall_subset_ball (by dsimp [r]; linarith)).trans hsU
  · intro x hx
    have hh : x∈Metric.closedBall p χ.rIn := by
      rw [Metric.mem_closedBall]
      have hd := Metric.mem_ball.mp hx
      dsimp [χ,r] at *
      linarith
    change χ x•f x=f x
    rw [χ.one_of_mem_closedBall hh,one_smul]

 theorem compact_C1_gradient_bound {f : Euc n → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) : ∃ B : ℝ, 0≤B ∧ ∀ x, ‖gradient f x‖≤B := by
  have hg := gradient_continuous_C1 hf
  have hgc := gradient_hasCompactSupport hc
  obtain ⟨B,hB⟩ := hgc.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨max 0 B,le_max_left _ _,fun x ↦ ?_⟩
  by_cases hx : x∈tsupport (gradient f)
  · exact (hB x hx).trans (le_max_right _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx,norm_zero]
    exact le_max_left _ _

 theorem differenceQuotient_bound {f : Euc n → ℝ} (hf : Differentiable ℝ f)
    {B : ℝ} (hB : 0≤B) (hb : ∀ x, ‖gradient f x‖≤B) (e : Euc n) (s : ℝ) (x : Euc n) :
    |differenceQuotient f e s x|≤B*‖e‖ := by
  have hnorm (y : Euc n) : ‖fderiv ℝ f y‖≤B := by
    have he : ‖fderiv ℝ f y‖=‖gradient f y‖ := by
      rw [gradient,LinearIsometryEquiv.norm_map]
    rw [he]
    exact hb y
  have hh := (convex_univ : Convex ℝ (univ : Set (Euc n))).norm_image_sub_le_of_norm_fderiv_le
    (fun y _ ↦ hf y) (fun y _ ↦ hnorm y) (mem_univ x) (mem_univ (x+s•e))
  by_cases hs : s=0
  · simp only [differenceQuotient,hs,inv_zero,zero_mul,abs_zero]
    positivity
  · rw [differenceQuotient,abs_mul,abs_inv]
    rw [Real.norm_eq_abs,add_sub_cancel_left,norm_smul,Real.norm_eq_abs] at hh
    have h := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (abs_nonneg s))
    have he : |s|⁻¹*(B*(|s| *‖e‖))=B*‖e‖ := by field_simp [abs_ne_zero.mpr hs]
    exact h.trans_eq he

end RPISingularHarnack

end

end OAI
