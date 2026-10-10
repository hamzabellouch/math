import OAI.Analysis.StrictMeans.BoxExtension

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section

lemma line_hasDerivAt {u : ℂ → ℝ} {z d : ℂ} {t : ℝ}
    (hu : DifferentiableAt ℝ u (z+t•d)) :
    HasDerivAt (fun t : ℝ=>u (z+t•d)) (fderiv ℝ u (z+t•d) d) t := by
  have hl : HasDerivAt (fun t : ℝ=>z+t•d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add z
  exact hu.hasFDerivAt.comp_hasDerivAt t hl

lemma line_second_hasDerivAt {u : ℂ → ℝ} {z d : ℂ} {t : ℝ}
    (hu : ContDiffAt ℝ 2 u (z+t•d)) :
    HasDerivAt (fun t : ℝ=>fderiv ℝ u (z+t•d) d) (second u (z+t•d) d d) t := by
  have hl : HasDerivAt (fun t : ℝ=>z+t•d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add z
  have hf := (hu.fderiv_right (m:=1) (by norm_num)).differentiableAt one_ne_zero
  have hd : HasDerivAt (fun t : ℝ=>fderiv ℝ u (z+t•d))
      (fderiv ℝ (fderiv ℝ u) (z+t•d) d) t := hf.hasFDerivAt.comp_hasDerivAt t hl
  simpa only [second,map_zero,add_zero] using hd.clm_apply (hasDerivAt_const t d)

lemma centered_difference_lower {u : ℂ → ℝ} {z d : ℂ} {s a : ℝ}
    (hs : 0 ≤ s) (hu : ∀ t∈Icc (-s) s, ContDiffAt ℝ 2 u (z+t•d))
    (ha : ∀ t∈Icc (-s) s, a ≤ second u (z+t•d) d d) :
    a*s^2 ≤ u (z+s•d)+u (z-s•d)-2*u z := by
  let f : ℝ → ℝ := fun t=>u (z+t•d)-a*t^2/2
  let f' : ℝ → ℝ := fun t=>fderiv ℝ u (z+t•d) d-a*t
  let f'' : ℝ → ℝ := fun t=>second u (z+t•d) d d-a
  have hf (t : ℝ) (ht : t∈Icc (-s) s) : HasDerivAt f (f' t) t := by
    have hu' := line_hasDerivAt ((hu t ht).differentiableAt (by norm_num))
    convert hu'.sub ((((hasDerivAt_id t).pow 2).const_mul a).div_const 2) using 1 <;>
      first | rfl | (dsimp only [f',id_eq]; ring)
  have hf' (t : ℝ) (ht : t∈Icc (-s) s) : HasDerivAt f' (f'' t) t := by
    convert (line_second_hasDerivAt (hu t ht)).sub ((hasDerivAt_id t).const_mul a) using 1 <;>
      first | rfl | (simp only [f'',mul_one])
  have hc : ConvexOn ℝ (Icc (-s) s) f := convexOn_of_hasDerivWithinAt2_nonneg
    (convex_Icc _ _) (fun t ht=>(hf t ht).continuousAt.continuousWithinAt)
    (fun t ht=>(hf t (interior_subset ht)).hasDerivWithinAt)
    (fun t ht=>(hf' t (interior_subset ht)).hasDerivWithinAt)
    (fun t ht=>sub_nonneg.mpr (ha t (interior_subset ht)))
  have he := hc.2 (show -s∈Icc (-s) s by constructor <;> linarith)
    (show s∈Icc (-s) s by constructor <;> linarith)
    (show (0:ℝ)≤1/2 by norm_num) (show (0:ℝ)≤1/2 by norm_num) (by norm_num)
  change f ((1/2:ℝ)*(-s)+1/2*s) ≤ (1/2:ℝ)*f (-s)+(1/2:ℝ)*f s at he
  have hz : (1/2:ℝ)*(-s)+1/2*s=0 := by ring
  rw [hz] at he
  simp only [f] at he
  simp only [zero_smul,add_zero,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,zero_div,sub_zero,
    neg_smul,← sub_eq_add_neg,neg_sq] at he
  nlinarith

lemma second_continuousAt {u : ℂ → ℝ} {p : ℂ} (hu : ContDiffAt ℝ 2 u p) (d : ℂ) :
    ContinuousAt (fun z=>second u z d d) p := by
  have hf := ((hu.fderiv_right (m:=1) (by norm_num)).fderiv_right (m:=0) (by norm_num)).continuousAt
  exact (hf.clm_apply continuousAt_const).clm_apply continuousAt_const

lemma positive_laplace_ascent {u : ℂ → ℝ} {p : ℂ}
    (hu : ContDiffAt ℝ 2 u p)
    (htr : 0<second u p 1 1+second u p Complex.I Complex.I) :
    ∀ᶠ q : ℝ × ℂ in 𝓝 (0,p), 0<q.1 →
      u q.2 < u (q.2+q.1•(1:ℂ)) ∨ u q.2 < u (q.2+q.1•Complex.I) ∨
      u q.2 < u (q.2-q.1•(1:ℂ)) ∨ u q.2 < u (q.2-q.1•Complex.I) := by
  let A := second u p 1 1
  let B := second u p Complex.I Complex.I
  let e := (A+B)/4
  have he : 0<e := by dsimp [e,A,B]; positivity
  have hx : ∀ᶠ z in 𝓝 p, A-e < second u z 1 1 :=
    (second_continuousAt hu 1).eventually (lt_mem_nhds (by change A-e<A; linarith))
  have hy : ∀ᶠ z in 𝓝 p, B-e < second u z Complex.I Complex.I :=
    (second_continuousAt hu Complex.I).eventually (lt_mem_nhds (by change B-e<B; linarith))
  have hh := (hu.eventually (by norm_num)).and (hx.and hy)
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp hh
  have hn : ∀ᶠ q : ℝ × ℂ in 𝓝 (0,p), |q.1|<R/2 ∧ dist q.2 p<R/2 := by
    apply ((continuous_fst.norm.continuousAt.eventually (gt_mem_nhds (by simpa using half_pos hR))).and
      ((continuous_snd.dist continuous_const).continuousAt.eventually (gt_mem_nhds (by simpa using half_pos hR))))
  filter_upwards [hn] with q hq
  intro hs
  have hpoint (d : ℂ) (hd : ‖d‖≤1) (t : ℝ) (ht : t∈Icc (-q.1) q.1) :
      ContDiffAt ℝ 2 u (q.2+t•d) ∧ A-e < second u (q.2+t•d) 1 1 ∧
        B-e < second u (q.2+t•d) Complex.I Complex.I := by
    apply hball
    rw [Metric.mem_ball]
    have ht' : |t|≤q.1 := abs_le.mpr ht
    have hb : dist (q.2+t•d) q.2≤q.1 := by
      rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left hd (abs_nonneg t)).trans (by simpa using ht')
    have := dist_triangle (q.2+t•d) q.2 p
    rw [abs_of_pos hs] at hq
    linarith
  have hdx := centered_difference_lower hs.le (fun t ht=>(hpoint 1 (by simp) t ht).1)
    (fun t ht=>(hpoint 1 (by simp) t ht).2.1.le)
  have hdy := centered_difference_lower hs.le (fun t ht=>(hpoint Complex.I (by simp) t ht).1)
    (fun t ht=>(hpoint Complex.I (by simp) t ht).2.2.le)
  by_contra h
  push Not at h
  have hpos : 0<(A-e+B-e)*q.1^2 := mul_pos (by dsimp [e]; linarith [htr]) (sq_pos_of_pos hs)
  nlinarith [h.1,h.2.1,h.2.2.1,h.2.2.2]

lemma compact_laplace_ascent {u : ℂ → ℝ} {K : Set ℂ}
    (hK : IsCompact K) (hu : ∀ p∈K, ContDiffAt ℝ 2 u p)
    (htr : ∀ p∈K, 0<second u p 1 1+second u p Complex.I Complex.I) :
    ∀ᶠ s in 𝓝 (0:ℝ), ∀ p∈K, 0<s →
      u p < u (p+s•(1:ℂ)) ∨ u p < u (p+s•Complex.I) ∨
      u p < u (p-s•(1:ℂ)) ∨ u p < u (p-s•Complex.I) := by
  exact hK.eventually_forall_of_forall_eventually (fun p hp=>positive_laplace_ascent (hu p hp) (htr p hp))

end
end StrictInverseFirstPower.Grid

end

end OAI
