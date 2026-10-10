import OAI.MathematicalPhysics.Transonic.Profile.PhysicalGlobal

namespace OAI

section
noncomputable section
namespace SepticProfile.PhysicalExterior
open Set Filter
open scoped Topology ContDiff

lemma field_smooth_all {q beta a b m : ℝ}
    (hq : 1 < q) (ha : 0 < a) (hm : -1 < m ∧ m < 1)
    (hfirst : 1-q*a+(q-a)*m < 0) (hsecond : 0 < 1+q*a-(a+q)*m) :
    ContDiffOn ℝ ∞ (field (q^2) beta) (Icc a b ×ˢ Icc (-1) m) := by
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  have hn : profileDenom (q^2) p.1 p.2≠0 :=
    ne_of_lt (denominator_neg hq ha hm hfirst hsecond hp.1.1 hp.2)
  unfold field profileNumer profileDenom at *
  fun_prop

lemma solution_smooth {q beta a m : ℝ}
    (hq : 1 < q) (ha : 0 < a) (hm : -1 < m ∧ m < 1)
    (hfirst : 1-q*a+(q-a)*m < 0) (hsecond : 0 < 1+q*a-(a+q)*m)
    {v : ℝ → ℝ}
    (hb : ∀ y∈Ici a, -1 < v y ∧ v y ≤ m)
    (hd : ∀ y∈Ici a, HasDerivWithinAt v (field (q^2) beta (y,v y)) (Ici a) y) :
    ContDiffOn ℝ ∞ v (Ici a) := by
  intro y hy
  have hs := ODEGlue.smooth_arc (f:=fun y v => field (q^2) beta (y,v))
    (field_smooth_all (b:=y+1) hq ha hm hfirst hsecond)
    (fun t ht => (hd t ht.1).mono Icc_subset_Ici_self)
    (fun t ht => ⟨(hb t ht.1).1.le,(hb t ht.1).2⟩)
  apply (hs y ⟨hy,by linarith⟩).mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show y<y+1 by linarith))] with t ht ht1
  exact ⟨ht,ht1.le⟩

lemma field_reciprocal {ell beta y : ℝ} (hell : ell≠0) (hy : 1 < y) :
    field ell beta (y,1/y)= -beta/y^2 := by
  have hy0 : y≠0 := by linarith
  have hs : y^2-1≠0 := by nlinarith
  have hsub : 1/y-y≠0 := by
    apply sub_ne_zero.mpr
    intro he
    have hh := (div_eq_iff hy0).mp he
    nlinarith
  have hd : profileDenom ell y (1/y)≠0 := by
    unfold profileDenom
    rw [show y*(1/y)=1 by field_simp,sub_self,zero_pow (by norm_num : (2:ℕ)≠0),zero_sub]
    exact mul_ne_zero hy0 (neg_ne_zero.mpr (mul_ne_zero hell (pow_ne_zero 2 hsub)))
  unfold field
  apply (div_eq_iff hd).mpr
  unfold profileNumer profileDenom
  field_simp
  ring

lemma solution_below_reciprocal {q beta a m : ℝ}
    (hq : 1 < q) (hbeta : 1 < beta) (ha : a < 1) (hm : m < 1)
    {v : ℝ → ℝ}
    (hb : ∀ y∈Ici a, v y ≤ m)
    (hd : ∀ y∈Ici a, HasDerivWithinAt v (field (q^2) beta (y,v y)) (Ici a) y) :
    ∀ y, 1 ≤ y → v y < 1/y := by
  have hder (y:ℝ) (hy:1≤y) : HasDerivAt v (field (q^2) beta (y,v y)) y :=
    (hd y (ha.le.trans hy)).hasDerivAt (Ici_mem_nhds (ha.trans_le hy))
  have hB (y:ℝ) (hy:1≤y) : HasDerivAt (fun y:ℝ => 1/y) (-1/y^2) y := by
    convert (hasDerivAt_const y (1:ℝ)).div (hasDerivAt_id y) (show y≠0 by linarith) using 1 <;> first | rfl | simp
  have hb1 : v 1 < 1 := (hb 1 ha.le).trans_lt hm
  have hnon (y:ℝ) (hy:1≤y) : v y ≤ 1/y := by
    apply image_le_of_deriv_right_lt_deriv_boundary' (a:=1) (b:=y)
      (fun t ht => (hder t ht.1).continuousAt.continuousWithinAt)
      (fun t ht => (hder t ht.1).hasDerivWithinAt)
      (B:=fun y:ℝ => 1/y) (B':=fun y:ℝ => -1/y^2)
      (by simpa using hb1.le)
      (fun t ht => (hB t ht.1).continuousAt.continuousWithinAt)
      (fun t ht => (hB t ht.1).hasDerivWithinAt) ?_ ⟨hy,le_rfl⟩
    intro t ht heq
    have ht1 : 1 < t := by
      by_contra hh
      have he : t=1 := le_antisymm (le_of_not_gt hh) ht.1
      subst t
      norm_num at heq
      linarith
    rw [heq,field_reciprocal (pow_ne_zero 2 (by linarith : q≠0)) ht1]
    exact (div_lt_div_iff_of_pos_right (sq_pos_of_pos (by linarith : 0<t))).mpr (by linarith)
  intro y hy
  by_cases he : y=1
  · simpa [he] using hb1
  have hy1 : 1 < y := lt_of_le_of_ne hy (Ne.symm he)
  apply lt_of_le_of_ne (hnon y hy)
  intro heq
  have heq' : v y=1/y := heq
  have hmax : IsLocalMax (fun t:ℝ => v t-1/t) y := by
    filter_upwards [Ioi_mem_nhds hy1] with t ht
    change v t-1/t ≤ v y-1/y
    rw [heq',sub_self]
    exact sub_nonpos.mpr (hnon t ht.le)
  have hh := hmax.hasDerivAt_eq_zero ((hder y hy).sub (hB y hy))
  rw [heq',field_reciprocal (pow_ne_zero 2 (by linarith : q≠0)) hy1] at hh
  have hlt : -beta/y^2 < -1/y^2 :=
    (div_lt_div_iff_of_pos_right (sq_pos_of_pos (by linarith : 0<y))).mpr (by linarith)
  linarith

end SepticProfile.PhysicalExterior

end
end

end OAI
