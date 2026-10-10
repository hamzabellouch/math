import OAI.Probability.SLE.Geometry.TransverseCurveDifference

namespace OAI

/-! Closing an arc by a path outside the domain preserves its unique
interior crossing. This connects the small-loop obstruction to inverse
Loewner semicircles. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology

namespace SLEExactGauge

lemma path_trans_first_strict_deriv {a b d : ℂ} (c : Path a b) (q : Path b d)
    {t : ℝ} (ht : t<1) {α : ℂ} (hc : HasStrictDerivAt c.extend α t) :
    HasStrictDerivAt (c.trans q).extend ((2:ℝ) • α) (t/2) := by
  have hd : HasStrictDerivAt (fun u : ℝ => 2*u) 2 (t/2) := by
    simpa using (hasStrictDerivAt_id (t/2)).const_mul 2
  have hcomp := hc.scomp_of_eq (t/2) hd (by ring)
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds (show t/2<(1:ℝ)/2 by linarith)] with u hu
  exact (Path.extend_trans_of_le_half c q hu.le).symm

lemma small_closed_arc_no_transverse_crossing {D : Set ℂ} {a b y z : ℂ}
    (c : Path a b) (q : Path b a) (p : Path y z)
    (hpin : ∀ u, p u∈D) (hqout : ∀ u, q u∉D)
    (w : ℂ) (r : ℝ) (hr : 0<r)
    (hcball : ∀ u, c u∈ball w r) (hqball : ∀ u, q u∈ball w r)
    (hy : y∉ball w r) (hz : z∉ball w r)
    (s t : unitInterval) (hs : 0<(s:ℝ) ∧ (s:ℝ)<1) (ht : 0<(t:ℝ) ∧ (t:ℝ)<1)
    (he : c t=p s) (hu : ∀ u v, c v=p u → u=s ∧ v=t)
    (α β : ℂ) (hc : HasStrictDerivAt c.extend α t) (hp : HasStrictDerivAt p.extend β s)
    (htrans : ∀ u v : ℝ, u • α-v • β=0 → u=0 ∧ v=0) : False := by
  let l := c.trans q
  let t' : unitInterval := ⟨(t:ℝ)/2,by constructor <;> linarith [t.property.1,t.property.2]⟩
  have ht' : 0<(t':ℝ) ∧ (t':ℝ)<1 := ⟨half_pos ht.1,by dsimp [t']; linarith [ht.2]⟩
  have hlball (u : unitInterval) : l u∈ball w r := by
    have hmem : l u∈range l := mem_range_self u
    rw [Path.trans_range] at hmem
    rcases hmem with ⟨v,hv⟩ | ⟨v,hv⟩
    · exact hv ▸ hcball v
    · exact hv ▸ hqball v
  have he' : l t'=p s := by
    rw [Path.trans_apply,dite_eq_left (show (t':ℝ)≤1/2 by dsimp [t']; linarith [t.property.2])]
    convert he using 1
    congr 1
    apply Subtype.ext
    dsimp [t']
    ring
  have hu' (u v : unitInterval) (hev : l v=p u) : u=s ∧ v=t' := by
    rw [Path.trans_apply] at hev
    split_ifs at hev with hv
    · obtain ⟨hu,hv'⟩ := hu _ _ hev
      refine ⟨hu,Subtype.ext ?_⟩
      have hvR := congrArg (fun a : unitInterval => (a:ℝ)) hv'
      dsimp [t']
      dsimp at hvR
      linarith
    · exact False.elim ((hqout _) (hev ▸ hpin u))
  have htrans' (u v : ℝ) (heq : u • ((2:ℝ) • α)-v • β=0) : u=0 ∧ v=0 := by
    have heq' : (2*u) • α-v • β=0 := by simpa only [smul_smul,mul_comm] using heq
    obtain ⟨hu,hv⟩ := htrans _ _ heq'
    exact ⟨by linarith,hv⟩
  have hloc := transverse_difference_locally_injective
    (path_trans_first_strict_deriv c q ht.2 hc) hp htrans'
  apply small_loop_no_single_crossing (l : C(unitInterval,ℂ)) (p : C(unitInterval,ℂ))
    w r hr hlball (by simpa using hy) (by simpa using hz) s t' hs ht' he' hu'
  · exact hloc
  · simp [l]

end SLEExactGauge

end

end OAI
