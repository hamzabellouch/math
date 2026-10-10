import OAI.Probability.FirstPassage.LocalTravel

namespace OAI

namespace PlanarFPP
open Set

@[simp] theorem latticeEmbed_add (p q : Vertex) :
    latticeEmbed (p+q) = latticeEmbed p+latticeEmbed q := by
  ext i
  fin_cases i <;> simp [latticeEmbed]

theorem step_embed_norm_le (d : Step) : ‖latticeEmbed d.delta‖ ≤ 1 := by
  have h := plane_norm_le_coordinates (latticeEmbed d.delta)
  cases d <;> simpa [Step.delta, latticeEmbed] using h

theorem displacement_norm_le_length (ds : List Step) :
    ‖latticeEmbed (displacement ds)‖ ≤ (ds.length : ℝ) := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    rw [displacement_cons, latticeEmbed_add]
    have ht := norm_add_le (latticeEmbed d.delta) (latticeEmbed (displacement ds))
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith [step_embed_norm_le d]

theorem coordinatePath_length (p q : Vertex) :
    (coordinatePath p q).length = latticeDistance p q := by
  have hh (a : ℤ) : (horizontal a).length = a.natAbs := by
    unfold horizontal
    split_ifs <;> simp only [List.length_replicate] <;> omega
  have hv (a : ℤ) : (vertical a).length = a.natAbs := by
    unfold vertical
    split_ifs <;> simp only [List.length_replicate] <;> omega
  simp [coordinatePath, latticeDistance, hh, hv]

theorem coordinatePath_prefix_bound (p q : Vertex) (i : ℕ) :
    ‖latticeEmbed (p+displacement ((coordinatePath p q).take i)-p)‖ ≤
      (latticeDistance p q : ℝ) := by
  simp only [add_sub_cancel_left]
  exact (displacement_norm_le_length _).trans (by
    exact_mod_cast (show ((coordinatePath p q).take i).length ≤ latticeDistance p q by
      rw [List.length_take, coordinatePath_length]; exact min_le_right _ _))

theorem segmentPoint_perturbation (p q p' q' : Vertex) (r t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hp : ‖latticeEmbed (p'-p)‖ ≤ r) (hq : ‖latticeEmbed (q'-q)‖ ≤ r) :
    ‖segmentPoint p' q' t-segmentPoint p q t‖ ≤ r := by
  have he : segmentPoint p' q' t-segmentPoint p q t =
      (1-t) • latticeEmbed (p'-p)+t • latticeEmbed (q'-q) := by
    simp only [segmentPoint,latticeEmbed_sub]
    ext i
    simp [PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
    ring
  rw [he]
  have hn := norm_add_le ((1-t) • latticeEmbed (p'-p)) (t • latticeEmbed (q'-q))
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg (by linarith : 0 ≤ 1-t),abs_of_nonneg ht0] at hn
  have h1 := mul_le_mul_of_nonneg_left hp (show 0 ≤ 1-t by linarith)
  have h2 := mul_le_mul_of_nonneg_left hq ht0
  nlinarith

theorem segmentTube_perturbation (p q p' q' : Vertex) (r R : ℝ)
    (hp : ‖latticeEmbed (p'-p)‖ ≤ r) (hq : ‖latticeEmbed (q'-q)‖ ≤ r) :
    SegmentTube p' q' R ⊆ SegmentTube p q (R+r) := by
  rintro z ⟨t,ht0,ht1,ht⟩
  refine ⟨t,ht0,ht1,?_⟩
  have hb := segmentPoint_perturbation p q p' q' r t ht0 ht1 hp hq
  have hn := norm_add_le (latticeEmbed z-segmentPoint p' q' t)
    (segmentPoint p' q' t-segmentPoint p q t)
  rw [sub_add_sub_cancel] at hn
  linarith

theorem localTravel_attach (μ : Plane → ℝ) (w : Edge → ℝ)
    (β : ℝ) (hβ : 0 ≤ β) (hlip : ∀ v u, |μ v-μ u| ≤ β*‖v-u‖)
    (p q p' q' : Vertex) (r a η δ s : ℝ)
    (hp : ‖latticeEmbed (p'-p)‖ ≤ r) (hq : ‖latticeEmbed (q'-q)‖ ≤ r)
    (hleft : pathCost w p (coordinatePath p p') ≤ a)
    (hright : pathCost w q' (coordinatePath q' q) ≤ a)
    (hmid : LocalTravel μ η δ s p' q' w) :
    ∃ ds, p+displacement ds=q ∧
        pathCost w p ds ≤ μ (latticeEmbed (q-p))+η*s+2*a+2*β*r ∧
        PathIn p ds (SegmentTube p q (max (3*r) (δ*s+r))) := by
  obtain ⟨ds,hd,hcost,hin⟩ := hmid
  let l := coordinatePath p p'
  let v := coordinatePath q' q
  have hl : p+displacement l=p' := coordinatePath_endpoint p p'
  have hv : q'+displacement v=q := coordinatePath_endpoint q' q
  have hμdiff : μ (latticeEmbed (q'-p')) ≤ μ (latticeEmbed (q-p))+2*β*r := by
    have he : latticeEmbed (q'-p')-latticeEmbed (q-p) =
        latticeEmbed (q'-q)-latticeEmbed (p'-p) := by
      simp only [latticeEmbed_sub]; abel
    have hn : ‖latticeEmbed (q'-p')-latticeEmbed (q-p)‖ ≤ 2*r := by
      rw [he]
      exact (norm_sub_le _ _).trans (by linarith)
    have ht := (le_abs_self _).trans (hlip (latticeEmbed (q'-p')) (latticeEmbed (q-p)))
    have hb := mul_le_mul_of_nonneg_left hn hβ
    linarith
  have hll : PathIn p l (SegmentTube p q (max (3*r) (δ*s+r))) := by
    intro i _
    refine ⟨0,by norm_num,by norm_num,?_⟩
    have hb := coordinatePath_prefix_bound p p' i
    have hdist := latticeDistance_le_norm p p'
    rw [← latticeEmbed_sub] at hdist
    have hr : 0 ≤ r := (norm_nonneg _).trans hp
    simp only [segmentPoint,zero_smul,add_zero]
    rw [← latticeEmbed_sub]
    exact hb.trans ((hdist.trans (by linarith)).trans (le_max_left _ _))
  have hrr : PathIn q' v (SegmentTube p q (max (3*r) (δ*s+r))) := by
    intro i _
    refine ⟨1,by norm_num,by norm_num,?_⟩
    have hb := coordinatePath_prefix_bound q' q i
    have hdist := latticeDistance_le_norm q' q
    rw [norm_sub_rev,← latticeEmbed_sub] at hdist
    have hn := norm_add_le
      (latticeEmbed (q'+displacement (v.take i))-latticeEmbed q')
      (latticeEmbed q'-latticeEmbed q)
    rw [sub_add_sub_cancel,← latticeEmbed_sub,← latticeEmbed_sub,← latticeEmbed_sub] at hn
    simp only [segmentPoint,one_smul,add_sub_cancel]
    rw [← latticeEmbed_sub]
    exact (hn.trans (by dsimp [v] at *; linarith)).trans (le_max_left _ _)
  have hmm : PathIn p' ds (SegmentTube p q (max (3*r) (δ*s+r))) := by
    intro i hi
    obtain ⟨t,ht0,ht1,ht⟩ := segmentTube_perturbation p q p' q' r (δ*s) hp hq (hin i hi)
    exact ⟨t,ht0,ht1,ht.trans (le_max_right _ _)⟩
  refine ⟨l++ds++v,?_,?_,?_⟩
  · rw [displacement_append,displacement_append,← add_assoc,← add_assoc,hl,hd,hv]
  · rw [pathCost_append,pathCost_append,displacement_append,← add_assoc,hl,hd]
    dsimp [l,v]
    linarith
  · apply pathIn_append _ _ _ _ (pathIn_append _ _ _ _ hll (by simpa [hl] using hmm))
    simpa only [displacement_append,← add_assoc,hl,hd] using hrr

end PlanarFPP

end OAI
