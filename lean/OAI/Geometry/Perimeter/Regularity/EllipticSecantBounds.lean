import OAI.Geometry.Perimeter.Regularity.EllipticSecant

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

 theorem segment_in_ball {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {p a b : V} {r t : ℝ} (ha : a∈Metric.ball p r) (hb : b∈Metric.ball p r)
    (ht : t∈Icc (0:ℝ) 1) : a+t•(b-a)∈Metric.ball p r := by
  have hh := (convex_ball p r) ha hb (sub_nonneg.mpr ht.2) ht.1 (by ring : 1-t+t=1)
  convert hh using 1
  module

 theorem segment_difference_bound {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a b a' b' : V) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    ‖(a+t•(b-a))-(a'+t•(b'-a'))‖ ≤ ‖a-a'‖+‖b-b'‖ := by
  have he : (a+t•(b-a))-(a'+t•(b'-a'))=(1-t)•(a-a')+t•(b-b') := by module
  rw [he]
  have hh := norm_add_le ((1-t)•(a-a')) (t•(b-b'))
  rw [norm_smul,norm_smul,Real.norm_of_nonneg (sub_nonneg.mpr ht.2),Real.norm_of_nonneg ht.1] at hh
  nlinarith [norm_nonneg (a-a'),norm_nonneg (b-b'),mul_nonneg ht.1 (norm_nonneg (a-a')),
    mul_nonneg (sub_nonneg.mpr ht.2) (norm_nonneg (b-b'))]

 theorem derivativeSecant_lipschitz_ball {G : Euc n → Euc n} (hG : ContDiff ℝ 1 G)
    {p a b a' b' : Euc n} {r L : ℝ} (hL : 0 ≤ L)
    (ha : a∈Metric.ball p r) (hb : b∈Metric.ball p r)
    (ha' : a'∈Metric.ball p r) (hb' : b'∈Metric.ball p r)
    (hLip : ∀ x∈Metric.ball p r, ∀ y∈Metric.ball p r,
      ‖fderiv ℝ G x-fderiv ℝ G y‖ ≤ L*‖x-y‖) :
    ‖derivativeSecant G a b-derivativeSecant G a' b'‖ ≤ L*(‖a-a'‖+‖b-b'‖) := by
  apply derivativeSecant_difference hG
  intro t ht
  exact (hLip _ (segment_in_ball ha hb ht) _ (segment_in_ball ha' hb' ht)).trans
    (mul_le_mul_of_nonneg_left (segment_difference_bound a b a' b' ht) hL)

 theorem contDiff_local_lipschitz {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {f : V → W} (hf : ContDiff ℝ 1 f) (p : V) :
    ∃ r L : ℝ, 0<r ∧ 0≤L ∧ ∀ x∈Metric.ball p r, ∀ y∈Metric.ball p r,
      ‖f x-f y‖≤L*‖x-y‖ := by
  have hc := ((hf.continuous_fderiv (by simp)).continuousAt (x := p)).norm
  obtain ⟨r,hr,hh⟩ := Metric.eventually_nhds_iff.mp
    (hc.eventually (gt_mem_nhds (lt_add_one ‖fderiv ℝ f p‖)))
  refine ⟨r,‖fderiv ℝ f p‖+1,hr,by positivity,fun x hx y hy ↦ ?_⟩
  exact (convex_ball p r).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ ↦ hf.differentiable (by simp) z)
    (fun z hz ↦ (hh (Metric.mem_ball.mp hz)).le) hy hx

end RPISingularHarnack

end

end OAI
