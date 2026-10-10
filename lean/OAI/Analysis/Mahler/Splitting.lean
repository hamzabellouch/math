import OAI.Analysis.Mahler.Diamonds

namespace OAI

noncomputable section

namespace SymmetricMahler

open Set Metric

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [inst520 : FiniteDimensional ℝ E] [inst521 : Nontrivial E]

lemma maximal_unit_face_vertex_sign (hmed : HasMetricMedians E) {K : Set E}
    (hK : IsMaximalProperFace (closedBall (0:E) 1) K) (hn : K.Nonempty)
    {x : E} (hx : x ∈ (closedBall (0:E) 1).extremePoints ℝ) : x ∈ K ∨ -x ∈ K := by
  obtain ⟨f,hf,he⟩ := maximal_unit_face_support hmed hK hn
  rcases extreme_dual_eval_eq_one_or_neg_one hmed hx hf with h | h
  · exact Or.inl (he.symm ▸ ⟨hx.1,h⟩)
  · exact Or.inr (he.symm ▸ ⟨(extreme_unit_neg hx).1,by simp [h]⟩)

omit inst520 inst521 in
lemma supporting_sum_eval [FiniteDimensional ℝ E] [Nontrivial E] {a b h t : E →L[ℝ] ℝ}
    (hh : h ∈ closedBall (0 : E →L[ℝ] ℝ) 1)
    (ht : t ∈ closedBall (0 : E →L[ℝ] ℝ) 1) (he : a+b=h+t)
    {x : E} (hx : x ∈ closedBall (0:E) 1) {s : ℝ} (hs : s=1 ∨ s= -1)
    (ha : a x=s) (hb : b x=s) : h x=s := by
  have h1 := dual_eval_bounds (mem_closedBall_zero_iff.mp hh) hx
  have h2 := dual_eval_bounds (mem_closedBall_zero_iff.mp ht) hx
  have h3 := congrArg (fun f : E →L[ℝ] ℝ => f x) he
  change a x+b x=h x+t x at h3
  rcases hs with rfl | rfl <;> linarith

lemma crossing_support (hmed : HasMetricMedians E)
    (hdual : HasMetricMedians (E →L[ℝ] ℝ)) {K : Set E}
    (hK : IsMaximalProperFace (closedBall (0:E) 1) K) (hKn : K.Nonempty)
    {f1 f2 f3 f4 : E →L[ℝ] ℝ}
    (hf1 : f1 ∈ (closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints ℝ)
    (hf2 : f2 ∈ (closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints ℝ)
    (hf3 : f3 ∈ (closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints ℝ)
    (hf4 : f4 ∈ (closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints ℝ)
    (hneg : ∀ x ∈ K, ¬ (f1 x= -1 ∧ f2 x= -1))
    (hpos : ∀ x ∈ K, ¬ (f3 x=1 ∧ f4 x=1)) :
    ∃ h ∈ (closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints ℝ,
      (∀ x ∈ closedBall (0:E) 1, f1 x=1 → f3 x=1 → h x= -1) ∧
      (∀ x ∈ closedBall (0:E) 1, f1 x= -1 → f3 x= -1 → h x=1) ∧
      (∀ x ∈ closedBall (0:E) 1, f2 x=1 → f4 x=1 → h x=1) ∧
      (∀ x ∈ closedBall (0:E) 1, f2 x= -1 → f4 x= -1 → h x= -1) := by
  let B := closedBall (0 : E →L[ℝ] ℝ) 1
  let A := faceHull B ({-f1} ∪ {-f3})
  let C := faceHull B ({f2} ∪ {f4})
  have hA : IsFace B A := isFace_faceHull (convex_closedBall _ _)
    (union_subset (singleton_subset_iff.mpr (extreme_unit_neg hf1).1)
      (singleton_subset_iff.mpr (extreme_unit_neg hf3).1))
  have hC : IsFace B C := isFace_faceHull (convex_closedBall _ _)
    (union_subset (singleton_subset_iff.mpr hf2.1) (singleton_subset_iff.mpr hf4.1))
  have h1 : -f1 ∈ A := subset_faceHull (Or.inl (mem_singleton _))
  have h3 : -f3 ∈ A := subset_faceHull (Or.inr (mem_singleton _))
  have h2 : f2 ∈ C := subset_faceHull (Or.inl (mem_singleton _))
  have h4 : f4 ∈ C := subset_faceHull (Or.inr (mem_singleton _))
  have hn : (A ∩ C).Nonempty := by
    by_contra hn
    have hd : Disjoint A C := disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hn)
    obtain ⟨x,hx,hxA,hxC⟩ := dual_disjoint_faces_primal_vertex hdual hA hC ⟨_,h1⟩ ⟨_,h2⟩ hd
    have hx1 : f1 x= -1 := by have := hxA _ h1; change -f1 x=1 at this; linarith
    have hx3 : f3 x= -1 := by have := hxA _ h3; change -f3 x=1 at this; linarith
    have hx2 := hxC _ h2
    have hx4 := hxC _ h4
    rcases maximal_unit_face_vertex_sign hmed hK hKn hx with hxK | hxK
    · exact hneg x hxK ⟨hx1,hx2⟩
    · exact hpos (-x) hxK ⟨by simp [hx3],by simp [hx4]⟩
  obtain ⟨h,hh,hhA,hhC⟩ := (hA.inter hC).exists_vertex hdual hn
  obtain ⟨t,ht,het⟩ := vertex_in_two_vertex_face hdual (extreme_unit_neg hf1)
    (extreme_unit_neg hf3) hh hhA
  obtain ⟨u,hu,heu⟩ := vertex_in_two_vertex_face hdual hf2 hf4 hh hhC
  refine ⟨h,hh,?_,?_,?_,?_⟩
  · intro x hx h1 h3
    exact supporting_sum_eval hh.1 ht.1 het hx (Or.inr rfl) (by simp [h1]) (by simp [h3])
  · intro x hx h1 h3
    exact supporting_sum_eval hh.1 ht.1 het hx (Or.inl rfl) (by simp [h1]) (by simp [h3])
  · intro x hx h2 h4
    exact supporting_sum_eval hh.1 hu.1 heu hx (Or.inl rfl) h2 h4
  · intro x hx h2 h4
    exact supporting_sum_eval hh.1 hu.1 heu hx (Or.inr rfl) h2 h4

theorem mface_split_core (hmed : HasMetricMedians E)
    (hdual : HasMetricMedians (E →L[ℝ] ℝ))
    {K F F' N1 N1' N2 N2' : Set E}
    (hK : IsMaximalProperFace (closedBall (0:E) 1) K)
    (pF : IsParallelPair K F F') (hmF : HasMFaceStructure F)
    (hmax : HasMaximalMRank F)
    (p1 : IsParallelPair K N1 N1') (p2 : IsParallelPair K N2 N2')
    (hF1 : IsMaximalProperFace F (F ∩ N1))
    (_ : IsMaximalProperFace F (F ∩ N2))
    (hmeet : (F ∩ N1 ∩ N2).Nonempty) (hdis : Disjoint N1' N2')
    {x1 x2 y1 y2 : E}
    (hx1 : x1 ∈ F ∩ (closedBall (0:E) 1).extremePoints ℝ)
    (hx2 : x2 ∈ F ∩ (closedBall (0:E) 1).extremePoints ℝ)
    (hy1 : y1 ∈ F' ∩ (closedBall (0:E) 1).extremePoints ℝ)
    (hy2 : y2 ∈ F' ∩ (closedBall (0:E) 1).extremePoints ℝ)
    (hx1n : x1 ∈ N1' ∩ N2) (hx2n : x2 ∈ N1 ∩ N2')
    (he : x1+y1=x2+y2) : False := by
  have hFb := hK.1.trans pF.1
  have hFp := proper_unit_face_subface_ne hK.1 hK.2.1 pF.1.subset
  have hx1K := hK.1.extreme_mem hx1.2 (pF.1.subset hx1.1)
  have hx2K := hK.1.extreme_mem hx2.2 (pF.1.subset hx2.1)
  have hy1K := hK.1.extreme_mem hy1.2 (pF.2.1.subset hy1.1)
  have hy2K := hK.1.extreme_mem hy2.2 (pF.2.1.subset hy2.1)
  obtain ⟨G,H,hG,hH,hGn,hHn,hGH,hx1H,hx2H⟩ :
      ∃ G H, IsMaximalProperFace F G ∧ IsMaximalProperFace F H ∧
        G.Nonempty ∧ H.Nonempty ∧ Disjoint G H ∧ x1 ∈ H ∧ x2 ∈ H := by
    obtain ⟨G,H,hG,hH,hGn,hHn,hGH⟩ := hmF
    have pGH := maximal_pair_of_disjoint hmed hFb hG hH hGn hHn hGH
    obtain ⟨G',pG⟩ := (maximal_mface_children_parallel hmed hK.1 hK.2.1 pF hmax
      hG hH hGn hHn hGH).1
    have hy1G' := (pG.not_mem_iff hy1K).mp
      (fun hh => disjoint_left.mp pF.2.2.1 (hG.1.subset hh) hy1.1)
    have hy2G' := (pG.not_mem_iff hy2K).mp
      (fun hh => disjoint_left.mp pF.2.2.1 (hG.1.subset hh) hy2.1)
    have hh : x1 ∈ G ↔ x2 ∈ G := by
      constructor
      · intro hx
        by_contra hn
        have hx2G' := (pG.not_mem_iff hx2K).mp hn
        exact disjoint_left.mp pG.2.2.1 hx
          (face_mem_of_parallelogram pG.2.1 hx2G' hy2G' hx1K.1 hy1K.1 he.symm).1
      · intro hx
        by_contra hn
        have hx1G' := (pG.not_mem_iff hx1K).mp hn
        exact disjoint_left.mp pG.2.2.1 hx
          (face_mem_of_parallelogram pG.2.1 hx1G' hy1G' hx2K.1 hy2K.1 he).1
    rcases pGH.vertex_mem (hFb.extreme_mem hx1.2 hx1.1) with hx | hx
    · exact ⟨H,G,hH,hG,hHn,hGn,hGH.symm,hx,hh.mp hx⟩
    · exact ⟨G,H,hG,hH,hGn,hHn,hGH,hx,
        (pGH.not_mem_iff (hFb.extreme_mem hx2.2 hx2.1)).mp
          (fun hg => disjoint_left.mp hGH (hh.mpr hg) hx)⟩
  have pGH := maximal_pair_of_disjoint hmed hFb hG hH hGn hHn hGH
  obtain ⟨G',pG⟩ := (maximal_mface_children_parallel hmed hK.1 hK.2.1 pF hmax
    hG hH hGn hHn hGH).1
  obtain ⟨H',pH⟩ := (maximal_mface_children_parallel hmed hK.1 hK.2.1 pF hmax
    hG hH hGn hHn hGH).2
  have hx1G' := (pG.not_mem_iff hx1K).mp (fun hh => disjoint_left.mp hGH hh hx1H)
  have hx2G' := (pG.not_mem_iff hx2K).mp (fun hh => disjoint_left.mp hGH hh hx2H)
  have hy1G' := (pG.not_mem_iff hy1K).mp
    (fun hh => disjoint_left.mp pF.2.2.1 (hG.1.subset hh) hy1.1)
  have hy2G' := (pG.not_mem_iff hy2K).mp
    (fun hh => disjoint_left.mp pF.2.2.1 (hG.1.subset hh) hy2.1)
  have hy1H' := (pH.not_mem_iff hy1K).mp
    (fun hh => disjoint_left.mp pF.2.2.1 (hH.1.subset hh) hy1.1)
  have hy2H' := (pH.not_mem_iff hy2K).mp
    (fun hh => disjoint_left.mp pF.2.2.1 (hH.1.subset hh) hy2.1)
  have hyNs := p1.symm.square hx1n.1 hx2n.1 hy1K hy2K he
  have hyMs := p2.square hx1n.2 hx2n.2 hy1K hy2K he
  obtain ⟨f1,hf1,eN1,eN1'⟩ := p1.support_dual_vertex hmed hK.1 ⟨_,hx2n.1⟩ ⟨_,hx1n.1⟩
  obtain ⟨f2,hf2,eN2,eN2'⟩ := p2.support_dual_vertex hmed hK.1 ⟨_,hx1n.2⟩ ⟨_,hx2n.2⟩
  obtain ⟨f3,hf3,eG,eG'⟩ := pG.support_dual_vertex hmed hK.1 hGn ⟨_,hx1G'⟩
  obtain ⟨f4,hf4,eH,eH'⟩ := pH.support_dual_vertex hmed hK.1 hHn ⟨_,hy1H'⟩
  obtain ⟨h,hh,h13,h13',h24,h24'⟩ := crossing_support hmed hdual hK
    ⟨_,hx1K.1⟩ hf1 hf2 hf3 hf4
    (fun x hx he => disjoint_left.mp hdis (by rw [eN1']; exact ⟨hx,he.1⟩)
      (by rw [eN2']; exact ⟨hx,he.2⟩))
    (fun x hx he => disjoint_left.mp hGH (by rw [eG]; exact ⟨hx,he.1⟩)
      (by rw [eH]; exact ⟨hx,he.2⟩))
  let T := {x ∈ K | h x=1}
  let T' := {x ∈ K | h x= -1}
  have pT : IsParallelPair K T T' := parallelPair_of_dual_vertex hmed hK.1 hh
  have hNG : N1 ∩ G ⊆ T' := fun x hx =>
    ⟨p1.1.subset hx.1,h13 x (hK.1.subset (p1.1.subset hx.1))
      (eN1 ▸ hx.1).2 (eG ▸ hx.2).2⟩
  have hNG' : N1' ∩ G' ⊆ T := fun x hx =>
    ⟨p1.2.1.subset hx.1,h13' x (hK.1.subset (p1.2.1.subset hx.1))
      (eN1' ▸ hx.1).2 (eG' ▸ hx.2).2⟩
  have hNH : N2 ∩ H ⊆ T := fun x hx =>
    ⟨p2.1.subset hx.1,h24 x (hK.1.subset (p2.1.subset hx.1))
      (eN2 ▸ hx.1).2 (eH ▸ hx.2).2⟩
  have hNH' : N2' ∩ H' ⊆ T' := fun x hx =>
    ⟨p2.2.1.subset hx.1,h24' x (hK.1.subset (p2.2.1.subset hx.1))
      (eN2' ▸ hx.1).2 (eH' ▸ hx.2).2⟩
  have hx1T := hNH ⟨hx1n.2,hx1H⟩
  have hy2T := hNG' ⟨hyNs.2,hy2G'⟩
  have hy1T' := hNH' ⟨hyMs.1,hy1H'⟩
  have hx2T' := (pT.square hy2T hy1T' hx2K hx1K
    (by simpa [add_comm] using he.symm)).1
  have hHmeet : (H ∩ N1 ∩ N2).Nonempty := by
    by_contra hn
    obtain ⟨w,hw,⟨hwF,hwN1⟩,hwN2⟩ := ((hFb.inter (hK.1.trans p1.1)).inter
      (hK.1.trans p2.1)).exists_vertex hmed hmeet
    have hwH : w ∉ H := fun hh => hn ⟨w,⟨hh,hwN1⟩,hwN2⟩
    have hwG := (pGH.symm.not_mem_iff (hFb.extreme_mem hw hwF)).mp hwH
    have hGn1 : (G ∩ N1').Nonempty := by
      by_contra hn1
      have hsub : G ⊆ F ∩ N1 := fun x hx => ⟨hG.1.subset hx,
        p1.symm.subset_of_disjoint hmed hK.1 (pF.1.trans hG.1)
          (disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hn1)) hx⟩
      have heG := hG.2.2 _ hF1.1 hsub hF1.2.1
      exact disjoint_left.mp hGH (heG ▸ ⟨hx2.1,hx2n.1⟩) hx2H
    obtain ⟨v,hv,hvG,hvN1'⟩ := ((hFb.trans hG.1).inter
      (hK.1.trans p1.2.1)).exists_vertex hmed hGn1
    have hvN2 := (p2.symm.not_mem_iff (hK.1.extreme_mem hv (pG.1.subset hvG))).mp
      (fun hh => disjoint_left.mp hdis hvN1' hh)
    obtain ⟨a,ha,b,hb,hab⟩ := hH.exchange hmed hFb pGH.symm hHn
      (hFb.extreme_mem hv (hG.1.subset hvG)) hvG
      (hFb.extreme_mem hw hwF) hwG
    have hs := p1.symm.square hvN1' hwN1
      (hK.1.extreme_mem ha.2 (pH.1.subset ha.1))
      (hK.1.extreme_mem hb.2 (pH.1.subset hb.1)) hab
    have hbN2 : b ∈ N2 := (p2.symm.not_mem_iff
      (hK.1.extreme_mem hb.2 (pH.1.subset hb.1))).mp
        (fun hh => disjoint_left.mp hdis hs.2 hh)
    have haN2 := (face_mem_of_parallelogram p2.1 hwN2 hbN2
      (pG.1.subset hvG) (pH.1.subset ha.1) hab.symm).2
    exact hn ⟨a,⟨ha.1,hs.1⟩,haN2⟩
  obtain ⟨y,hy,⟨hyH,hyN1⟩,hyN2⟩ := (((hFb.trans hH.1).inter
    (hK.1.trans p1.1)).inter (hK.1.trans p2.1)).exists_vertex hmed hHmeet
  have hyT := hNH ⟨hyN2,hyH⟩
  obtain ⟨d,hd,c,hc,hec⟩ := hG.exchange hmed hFb pGH hGn
    (hFb.extreme_mem hx2.2 hx2.1) hx2H
    (hFb.extreme_mem hy (hH.1.subset hyH)) hyH
  have hs := p2.symm.square hx2n.2 hyN2
    (hK.1.extreme_mem hd.2 (pG.1.subset hd.1))
    (hK.1.extreme_mem hc.2 (pG.1.subset hc.1)) hec
  have hcN1 : c ∈ N1 := (p1.symm.not_mem_iff
    (hK.1.extreme_mem hc.2 (pG.1.subset hc.1))).mp
      (fun hh => disjoint_left.mp hdis hh hs.2)
  have hdN1 := (face_mem_of_parallelogram p1.1 hyN1 hcN1
    hx2K.1 (pG.1.subset hd.1) hec.symm).2
  have hdT' := hNG ⟨hdN1,hd.1⟩
  have hyT' := (face_mem_of_parallelogram pT.2.1 hx2T' hdT'
    (hH.1.subset.trans pF.1.subset hyH) (pG.1.subset hc.1) hec).1
  exact disjoint_left.mp pT.2.2.1 hyT hyT'

end

section
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

def fourSum : PiLp 1 (fun _ : Fin 4 => E) →ₗ[ℝ] E :=
  ∑ i : Fin 4, (PiLp.proj (𝕜 := ℝ) 1 (fun _ : Fin 4 => E) i).toLinearMap

abbrev ZeroSumFour := LinearMap.ker (fourSum E)

namespace ZeroSumFour
variable {E}
def entry (x : ZeroSumFour E) (i : Fin 4) : E := x.val.ofLp i

@[simp] lemma entry_add (x y : ZeroSumFour E) (i : Fin 4) :
    entry (x+y) i = entry x i + entry y i := rfl
@[simp] lemma entry_sub (x y : ZeroSumFour E) (i : Fin 4) :
    entry (x-y) i = entry x i - entry y i := rfl
@[simp] lemma entry_smul (a : ℝ) (x : ZeroSumFour E) (i : Fin 4) :
    entry (a • x) i = a • entry x i := rfl
@[simp] lemma entry_zero (i : Fin 4) : entry (0 : ZeroSumFour E) i = 0 := rfl

lemma sum_entry (x : ZeroSumFour E) : ∑ i, entry x i = 0 := by
  have hx := x.property
  change (fourSum E) x.val = 0 at hx
  rw [fourSum, LinearMap.sum_apply] at hx
  exact hx

lemma norm_eq_sum (x : ZeroSumFour E) : ‖x‖ = ∑ i, ‖entry x i‖ :=
  PiLp.norm_eq_of_L1 x.val

def pair (i j : Fin 4) (z : E) : ZeroSumFour E :=
  ⟨WithLp.toLp 1 (Pi.single i z - Pi.single j z), by
    simp [fourSum, LinearMap.mem_ker, Finset.sum_sub_distrib]⟩

@[simp] lemma entry_pair (i j k : Fin 4) (z : E) :
    entry (pair i j z) k = (if k = i then z else 0) - (if k = j then z else 0) := by
  simp [entry,pair]

lemma pair_norm_add (x : ZeroSumFour E) (i j : Fin 4) (hij : i ≠ j) (m : E)
    (hi : ‖m‖+‖entry x i-m‖ = ‖entry x i‖)
    (hj : ‖m‖+‖entry x j+m‖ = ‖entry x j‖) :
    ‖pair i j m‖+‖x-pair i j m‖ = ‖x‖ := by
  rw [norm_eq_sum, norm_eq_sum, norm_eq_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hki : k = i
  · subst k
    simpa [hij] using hi
  by_cases hkj : k = j
  · subst k
    simpa [hij,Ne.symm hij,sub_neg_eq_add] using hj
  simp [hki,hkj]

lemma pair_additive_of_extreme (hmed : HasMetricMedians E)
    {x : ZeroSumFour E}
    (hx : x ∈ (closedBall (0 : ZeroSumFour E) 1).extremePoints ℝ)
    (hnx : ‖x‖ = 1) (i j : Fin 4) (hij : i ≠ j)
    (hout : ∃ k, k ≠ i ∧ k ≠ j ∧ entry x k ≠ 0) :
    ‖entry x i + entry x j‖ = ‖entry x i‖ + ‖entry x j‖ := by
  obtain ⟨m,hm⟩ := hmed ![0,entry x i,-entry x j]
  have hi : ‖m‖+‖entry x i-m‖ = ‖entry x i‖ := by
    have ht := hm 0 1 (by decide)
    simpa [dist_eq_norm,norm_sub_rev] using ht.symm
  have hj : ‖m‖+‖entry x j+m‖ = ‖entry x j‖ := by
    have ht := hm 0 2 (by decide)
    simpa [dist_eq_norm,neg_sub,norm_sub_rev,add_comm] using ht.symm
  have he := extreme_unit_norm_add hx hnx ((pair_norm_add x i j hij m hi hj).trans hnx)
  obtain ⟨k,hki,hkj,hk⟩ := hout
  have hnc : ‖pair i j m‖ = 0 := by
    have ht := congrArg (fun v : ZeroSumFour E => entry v k) he
    have he' : (0:E) = ‖pair i j m‖ • entry x k := by simpa [hki,hkj] using ht
    exact (smul_eq_zero.mp he'.symm).resolve_right hk
  have hp0 : pair i j m = 0 := norm_eq_zero.mp hnc
  have hm0 : m = 0 := by
    have ht := congrArg (fun v : ZeroSumFour E => entry v i) hp0
    simpa [hij] using ht
  have ht := hm 1 2 (by decide)
  simpa [dist_eq_norm,sub_neg_eq_add,hm0] using ht

theorem extreme_four_norms (hmed : HasMetricMedians E)
    {x : ZeroSumFour E}
    (hx : x ∈ (closedBall (0 : ZeroSumFour E) 1).extremePoints ℝ)
    (hnx : ‖x‖ = 1)
    (hout : ∀ i j : Fin 4, i ≠ j → ∃ k, k ≠ i ∧ k ≠ j ∧ entry x k ≠ 0) :
    (∀ i, ‖entry x i‖ = 1/4) ∧
      ∀ i j, i ≠ j → ‖entry x i+entry x j‖ = 1/2 := by
  have ha (i j : Fin 4) (hij : i ≠ j) :=
    pair_additive_of_extreme hmed hx hnx i j hij (hout i j hij)
  have hs := sum_entry x
  simp only [Fin.sum_univ_four] at hs
  have h01 : -(entry x 0+entry x 1) = entry x 2+entry x 3 := by
    apply neg_eq_iff_add_eq_zero.mpr
    convert hs using 1 ; abel
  have h02 : -(entry x 0+entry x 2) = entry x 1+entry x 3 := by
    apply neg_eq_iff_add_eq_zero.mpr
    convert hs using 1 ; abel
  have h03 : -(entry x 0+entry x 3) = entry x 1+entry x 2 := by
    apply neg_eq_iff_add_eq_zero.mpr
    convert hs using 1 ; abel
  have hc01 := congrArg norm h01
  have hc02 := congrArg norm h02
  have hc03 := congrArg norm h03
  simp only [norm_neg, ha 0 1 (by decide),ha 2 3 (by decide)] at hc01
  simp only [norm_neg, ha 0 2 (by decide),ha 1 3 (by decide)] at hc02
  simp only [norm_neg, ha 0 3 (by decide),ha 1 2 (by decide)] at hc03
  have hsum := (norm_eq_sum x).symm.trans hnx
  simp only [Fin.sum_univ_four] at hsum
  have hn0 : ‖entry x 0‖ = 1/4 := by linarith only [hc01,hc02,hc03,hsum]
  have hn1 : ‖entry x 1‖ = 1/4 := by linarith only [hc01,hc02,hc03,hsum]
  have hn2 : ‖entry x 2‖ = 1/4 := by linarith only [hc01,hc02,hc03,hsum]
  have hn3 : ‖entry x 3‖ = 1/4 := by linarith only [hc01,hc02,hc03,hsum]
  have hn (i : Fin 4) : ‖entry x i‖ = 1/4 := by
    fin_cases i
    · exact hn0
    · exact hn1
    · exact hn2
    · exact hn3
  exact ⟨hn,fun i j hij => by rw [ha i j hij,hn i,hn j]; norm_num⟩
end ZeroSumFour

end

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [inst526 : FiniteDimensional ℝ E]

omit inst526 in
lemma IsCompact.exists_extreme_ge [FiniteDimensional ℝ E] {K : Set E} (hc : IsCompact K)
    (f : E →L[ℝ] ℝ) {x : E} (hx : x ∈ K) :
    ∃ y ∈ K.extremePoints ℝ, f x ≤ f y := by
  let S := {y ∈ K | ∀ z ∈ K, f z ≤ f y}
  have hS : IsExposed ℝ K S := fun _ => ⟨f,rfl⟩
  obtain ⟨z,hzK,hz⟩ := hc.exists_isMaxOn ⟨x,hx⟩ f.continuous.continuousOn
  obtain ⟨y,hy⟩ := (hS.isCompact hc).extremePoints_nonempty ⟨z,hzK,hz⟩
  exact ⟨y,hS.isExtreme.extremePoints_subset_extremePoints hy,hy.1.2 x hx⟩

omit inst526 in
lemma normalized_mem_exposed [FiniteDimensional ℝ E] {f : E →L[ℝ] ℝ} {F : Set E}
    (hF : F = {x ∈ closedBall (0:E) 1 | f x = 1}) {x : E}
    (hx : x ≠ 0) (he : f x = ‖x‖) : ‖x‖⁻¹ • x ∈ F := by
  rw [hF]
  have hn := norm_pos_iff.mpr hx
  constructor
  · apply mem_closedBall_zero_iff.mpr
    simp [norm_smul,ne_of_gt hn]
  · simp [he,ne_of_gt hn]

namespace ZeroSumFour

def entryL (i : Fin 4) : ZeroSumFour E →L[ℝ] E :=
  (PiLp.proj (𝕜 := ℝ) 1 (fun _ : Fin 4 => E) i).comp
    (Submodule.subtypeL (fourSum E).ker)

omit inst526 in
@[simp] lemma entryL_apply [FiniteDimensional ℝ E] (i : Fin 4) (q : ZeroSumFour E) : entryL i q = entry q i := rfl

lemma coordinate_extreme {f : Fin 4 → E →L[ℝ] ℝ}
    (hf : ∀ i, ‖f i‖ ≤ 1) {q : ZeroSumFour E}
    (hq : ‖q‖ ≤ 1) (he : ∀ i, f i (entry q i) = ‖entry q i‖)
    (hn : ‖q‖ = 1) :
    ∃ r ∈ (closedBall (0 : ZeroSumFour E) 1).extremePoints ℝ,
      ‖r‖ = 1 ∧ (∀ i, f i (entry r i) = ‖entry r i‖) ∧
      f 2 (entry q 2) ≤ f 2 (entry r 2) := by
  let L : ZeroSumFour E →L[ℝ] ℝ := ∑ i, (f i).comp (entryL i)
  have hLi (x : ZeroSumFour E) (i : Fin 4) : f i (entry x i) ≤ ‖entry x i‖ :=
    (le_abs_self _).trans ((f i).le_opNorm _ |>.trans
      (mul_le_of_le_one_left (norm_nonneg _) (hf i)))
  have hLe (x : ZeroSumFour E) : L x = ∑ i, f i (entry x i) := by simp [L]
  have hLb : ∀ x ∈ closedBall (0 : ZeroSumFour E) 1, L x ≤ 1 := by
    intro x hx
    rw [hLe]
    exact (Finset.sum_le_sum (fun i _ => hLi x i)).trans
      ((norm_eq_sum x).symm.le.trans (mem_closedBall_zero_iff.mp hx))
  let S := {x ∈ closedBall (0 : ZeroSumFour E) 1 | L x = 1}
  have hS := IsFace.of_support_le (convex_closedBall (0 : ZeroSumFour E) 1) L.toLinearMap 1 hLb
  have hSc : IsCompact S := (isCompact_closedBall (0 : ZeroSumFour E) 1).inter_right
    (isClosed_eq L.continuous continuous_const)
  have hqS : q ∈ S := ⟨mem_closedBall_zero_iff.mpr hq,by
    rw [hLe]
    simp_rw [he]
    rw [← norm_eq_sum,hn]⟩
  obtain ⟨r,hr,hqr⟩ := IsCompact.exists_extreme_ge hSc ((f 2).comp (entryL 2)) hqS
  have hrB := hS.2.extremePoints_subset_extremePoints hr
  have hrr : ‖r‖ = 1 := le_antisymm (mem_closedBall_zero_iff.mp hrB.1) (by
    rw [norm_eq_sum,← hr.1.2,hLe]
    exact Finset.sum_le_sum (fun i _ => hLi r i))
  refine ⟨r,hrB,hrr,?_,hqr⟩
  intro i
  have hs : ∑ i, f i (entry r i) = ∑ i, ‖entry r i‖ := by
    rw [← hLe,hr.1.2,← norm_eq_sum,hrr]
  exact (Finset.sum_eq_sum_iff_of_le (fun i _ => hLi r i)).mp hs i (Finset.mem_univ i)
end ZeroSumFour

end

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [inst529 : FiniteDimensional ℝ E] [inst530 : Nontrivial E]

omit inst529 inst530 in
lemma faceHull_union_generators [FiniteDimensional ℝ E] [Nontrivial E] {F C : Set E} {a c : E}
    (ha : faceHull (closedBall (0:E) 1) {a} = F)
    (hc : faceHull (closedBall (0:E) 1) {c} = C)
    (haB : a ∈ closedBall (0:E) 1) (hcB : c ∈ closedBall (0:E) 1) :
    faceHull (closedBall (0:E) 1) ({a} ∪ {c}) =
      faceHull (closedBall (0:E) 1) (F ∪ C) := by
  have haF : a ∈ F := ha ▸ subset_faceHull (mem_singleton _)
  have hcC : c ∈ C := hc ▸ subset_faceHull (mem_singleton _)
  apply subset_antisymm (faceHull_mono (union_subset_union
    (singleton_subset_iff.mpr haF) (singleton_subset_iff.mpr hcC)))
  apply faceHull_min (isFace_faceHull (convex_closedBall _ _)
    (union_subset (singleton_subset_iff.mpr haB) (singleton_subset_iff.mpr hcB)))
  rw [← ha,← hc]
  exact union_subset (faceHull_mono subset_union_left) (faceHull_mono subset_union_right)

namespace ZeroSumFour

def ofFour (a b c d : E) (he : a+b+c+d = 0) : ZeroSumFour E :=
  ⟨WithLp.toLp 1 ![a,b,c,d], by
    simpa [fourSum,LinearMap.mem_ker,Fin.sum_univ_four] using he⟩

omit inst529 inst530 in
@[simp] lemma entry_ofFour [FiniteDimensional ℝ E] [Nontrivial E] (a b c d : E) (he : a+b+c+d = 0) (i : Fin 4) :
    entry (ofFour a b c d he) i = ![a,b,c,d] i := rfl
end ZeroSumFour

theorem two_face_exchange (hmed : HasMetricMedians E)
    (hdual : HasMetricMedians (E →L[ℝ] ℝ)) {K F C : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (hp : K ≠ closedBall (0:E) 1)
    (hF : IsFace K F) (hC : IsFace K C) (hFn : F.Nonempty) (hCn : C.Nonempty)
    {y : E} (hy : y ∈ (closedBall (0:E) 1).extremePoints ℝ)
    (hyJ : y ∈ faceHull (closedBall (0:E) 1) (F ∪ C))
    (hyF : y ∉ F) (hyC : y ∉ C) :
    ∃ a ∈ F, ∃ c ∈ C, ∃ z ∈ K, a+c=y+z := by
  classical
  have hFb := hK.trans hF
  have hCb := hK.trans hC
  obtain ⟨a,ha,haG⟩ := hFb.exists_generator hmed hFn
  obtain ⟨c,hc,hcG⟩ := hCb.exists_generator hmed hCn
  let w := (1/2:ℝ) • a+(1/2:ℝ) • c
  have hwK : w ∈ K := hK.1 (hF.subset ha) (hC.subset hc)
    (by norm_num) (by norm_num) (by norm_num)
  have hwG : faceHull (closedBall (0:E) 1) {w} =
      faceHull (closedBall (0:E) 1) (F ∪ C) :=
    (faceHull_midpoint_eq (convex_closedBall _ _) (hFb.subset ha) (hCb.subset hc)).trans
      (faceHull_union_generators haG hcG (hFb.subset ha) (hCb.subset hc))
  have hyK := faceHull_min hK (union_subset hF.subset hC.subset) hyJ
  obtain ⟨t,ht,ht1,z,hzB,hw⟩ := faceHull_radial hdual (hK.subset hwK) (hwG.symm ▸ hyJ)
  have hzK : z ∈ K := hK.2.right_mem_of_mem_openSegment hy.1 hzB hwK
    ⟨t,1-t,ht,sub_pos.mpr ht1,by ring,hw.symm⟩
  have hnorm (x : E) (hx : x ∈ K) : ‖x‖ = 1 := norm_eq_one_of_mem_proper_face hK.2 hp hx
  obtain ⟨f,hfn,hf⟩ := hFb.exposed_generator hmed hFn
    (proper_unit_face_subface_ne hK hp hF.subset)
  obtain ⟨g,hgn,hg⟩ := hCb.exposed_generator hmed hCn
    (proper_unit_face_subface_ne hK hp hC.subset)
  have hY : IsFace (closedBall (0:E) 1) {y} := ⟨convex_singleton y,isExtreme_singleton.mpr hy⟩
  obtain ⟨s,hsn,hs⟩ := hY.exposed_generator hmed (singleton_nonempty y)
    (proper_unit_face_subface_ne hK hp (singleton_subset_iff.mpr hyK))
  obtain ⟨k,hkv,hk⟩ := proper_face_support hmed hK ⟨y,hyK⟩ hp
  have hkn := mem_closedBall_zero_iff.mp hkv.1
  have hfa := (hf ▸ ha).2
  have hgc := (hg ▸ hc).2
  have hsy := (hs ▸ mem_singleton y).2
  have heq : (1/4:ℝ) • a+(1/4:ℝ) • c+(-(t/2)) • y+(-((1-t)/2)) • z = 0 := by
    calc
      _ = (1/2:ℝ) • (w - (t • y+(1-t) • z)) := by dsimp [w]; module
      _ = 0 := by rw [hw,sub_self,smul_zero]
  let q := ZeroSumFour.ofFour ((1/4:ℝ) • a) ((1/4:ℝ) • c)
    ((-(t/2)) • y) ((-((1-t)/2)) • z) heq
  let fs : Fin 4 → E →L[ℝ] ℝ := ![f,g,-s,-k]
  have hfs : ∀ i, ‖fs i‖ ≤ 1 := by
    intro i
    fin_cases i <;> simp [fs,hfn,hgn,hsn,hkn]
  have hqn : ‖q‖ = 1 := by
    rw [ZeroSumFour.norm_eq_sum]
    simp only [Fin.sum_univ_four]
    simp [q,ZeroSumFour.entry_ofFour,norm_smul,hnorm a (hF.subset ha),
      hnorm c (hC.subset hc),hnorm y hyK,hnorm z hzK,
      abs_of_nonneg ht.le,abs_of_nonneg (sub_nonneg.mpr ht1.le)]
    ring
  have hqe : ∀ i, fs i (ZeroSumFour.entry q i) = ‖ZeroSumFour.entry q i‖ := by
    intro i
    fin_cases i <;> simp [fs,q,ZeroSumFour.entry_ofFour,norm_smul,hfa,hgc,hsy,hk z hzK,
      hnorm a (hF.subset ha),hnorm c (hC.subset hc),hnorm y hyK,hnorm z hzK,
      abs_of_nonneg ht.le,abs_of_nonneg (sub_nonneg.mpr ht1.le)]
  obtain ⟨r,hr,hrn,hre,hqr⟩ := ZeroSumFour.coordinate_extreme hfs hqn.le hqe hqn
  let v := ZeroSumFour.entry r
  have hv0 : f (v 0) = ‖v 0‖ := hre 0
  have hv1 : g (v 1) = ‖v 1‖ := hre 1
  have hv2 : s (-v 2) = ‖v 2‖ := by simpa [fs,v] using hre 2
  have hv3 : k (-v 3) = ‖v 3‖ := by simpa [fs,v] using hre 3
  have hv2pos : 0 < ‖v 2‖ := by
    have hq2 : fs 2 (ZeroSumFour.entry q 2) = t/2 := by simp [fs,q,hsy]
    rw [hq2,hre 2] at hqr
    dsimp [v]
    linarith
  have hv2ne : -v 2 ≠ 0 := neg_ne_zero.mpr (norm_pos_iff.mp hv2pos)
  have hv2y : ‖v 2‖⁻¹ • (-v 2) = y := by
    have hh := normalized_mem_exposed hs hv2ne (by simpa using hv2)
    simpa using hh
  have hv2e : -v 2 = ‖v 2‖ • y := by
    rw [← hv2y,smul_smul,mul_inv_cancel₀ (ne_of_gt hv2pos),one_smul]
  have hvs : v 0+v 1 = -v 2 + -v 3 := by
    have hh := ZeroSumFour.sum_entry r
    simp only [Fin.sum_univ_four] at hh
    change v 0+v 1+v 2+v 3=0 at hh
    calc
      _ = (v 0+v 1+v 2+v 3)-v 2-v 3 := by abel
      _ = _ := by rw [hh]; abel
  have hkv0 : k (v 0) = ‖v 0‖ := by
    by_cases hh : v 0 = 0
    · simp [hh]
    have hn := norm_pos_iff.mpr hh
    have hmem := normalized_mem_exposed hf hh hv0
    have he := hk _ (hF.subset hmem)
    simp only [map_smul,smul_eq_mul] at he
    have hh := congrArg (fun t : ℝ => ‖v 0‖*t) he
    simpa [← mul_assoc,ne_of_gt hn] using hh
  have hkv1 : k (v 1) = ‖v 1‖ := by
    by_cases hh : v 1 = 0
    · simp [hh]
    have hn := norm_pos_iff.mpr hh
    have he := hk _ (hC.subset (normalized_mem_exposed hg hh hv1))
    simp only [map_smul,smul_eq_mul] at he
    have hh := congrArg (fun t : ℝ => ‖v 1‖*t) he
    simpa [← mul_assoc,ne_of_gt hn] using hh
  have hks : ‖v 0‖+‖v 1‖ = ‖v 2‖+‖v 3‖ := by
    have hh := congrArg k hvs
    simpa [hkv0,hkv1,hv3,hv2e,hk y hyK] using hh
  have hv0ne : v 0 ≠ 0 := by
    intro hzero
    have hh := congrArg g hvs
    simp only [map_add,hzero,zero_add,hv1,hv2e,map_smul,smul_eq_mul] at hh
    have hgb : g (-v 3) ≤ ‖v 3‖ := by
      simpa using (le_abs_self (g (-v 3))).trans
        ((g.le_opNorm (-v 3)).trans (mul_le_of_le_one_left (norm_nonneg _) hgn))
    have hgy := (dual_eval_bounds hgn hy.1).2
    have hks' : ‖v 1‖ = ‖v 2‖+‖v 3‖ := by simpa [hzero] using hks
    have hge : g y = 1 := by nlinarith
    exact hyC (hg.symm ▸ ⟨hy.1,hge⟩)
  have hv1ne : v 1 ≠ 0 := by
    intro hzero
    have hh := congrArg f hvs
    simp only [map_add,hzero,add_zero,hv0,hv2e,map_smul,smul_eq_mul] at hh
    have hfb : f (-v 3) ≤ ‖v 3‖ := by
      simpa using (le_abs_self (f (-v 3))).trans
        ((f.le_opNorm (-v 3)).trans (mul_le_of_le_one_left (norm_nonneg _) hfn))
    have hfy := (dual_eval_bounds hfn hy.1).2
    have hks' : ‖v 0‖ = ‖v 2‖+‖v 3‖ := by simpa [hzero] using hks
    have hfe : f y = 1 := by nlinarith
    exact hyF (hf.symm ▸ ⟨hy.1,hfe⟩)
  have hout : ∀ i j : Fin 4, i ≠ j → ∃ l, l ≠ i ∧ l ≠ j ∧ ZeroSumFour.entry r l ≠ 0 := by
    intro i j hij
    by_cases h0 : (0:Fin 4) ≠ i ∧ 0 ≠ j
    · exact ⟨0,h0.1,h0.2,hv0ne⟩
    by_cases h1 : (1:Fin 4) ≠ i ∧ 1 ≠ j
    · exact ⟨1,h1.1,h1.2,hv1ne⟩
    exact ⟨2,by omega,by omega,norm_pos_iff.mp hv2pos⟩
  have hnorms := (ZeroSumFour.extreme_four_norms hmed hr hrn hout).1
  have hn0 : ‖v 0‖ = 1/4 := hnorms 0
  have hn1 : ‖v 1‖ = 1/4 := hnorms 1
  have hn2 : ‖v 2‖ = 1/4 := hnorms 2
  have hn3 : ‖v 3‖ = 1/4 := hnorms 3
  have h0F : (4:ℝ) • v 0 ∈ F := by
    simpa [hn0] using normalized_mem_exposed hf hv0ne hv0
  have h1C : (4:ℝ) • v 1 ∈ C := by
    simpa [hn1] using normalized_mem_exposed hg hv1ne hv1
  have h3B : (4:ℝ) • (-v 3) ∈ closedBall (0:E) 1 := by
    apply mem_closedBall_zero_iff.mpr
    simp [norm_smul,hn3]
  have h2y : (4:ℝ) • (-v 2) = y := by simpa [hn2] using hv2y
  have he : (4:ℝ) • v 0+(4:ℝ) • v 1 = y+(4:ℝ) • (-v 3) := by
    simpa [smul_add,h2y] using congrArg (fun x : E => (4:ℝ) • x) hvs
  have h3K := (face_mem_of_parallelogram hK (hF.subset h0F) (hC.subset h1C) hy.1 h3B he).2
  exact ⟨_,h0F,_,h1C,_,h3K,he⟩

end

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [inst533 : FiniteDimensional ℝ E] [inst534 : Nontrivial E]

lemma proper_unit_face_not_neg (hmed : HasMetricMedians E) {K : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (hp : K ≠ closedBall (0:E) 1)
    {x : E} (hx : x ∈ K) : -x ∉ K := by
  obtain ⟨f,hf,hfK⟩ := proper_face_support hmed hK ⟨x,hx⟩ hp
  intro hn
  have h1 := hfK x hx
  have h2 := hfK (-x) hn
  simp only [map_neg] at h2
  linarith

omit inst533 inst534 in
lemma IsParallelPair.restrict_support [FiniteDimensional ℝ E] [Nontrivial E] {K F N : Set E} {f : E →L[ℝ] ℝ}
    (hFK : F ⊆ K) (eN : N = {x ∈ K | f x=1}) :
    F ∩ N = {x ∈ F | f x=1} := by
  rw [eN]
  ext x
  exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,hFK h.1,h.2⟩⟩

theorem mface_split_precore (hmed : HasMetricMedians E)
    (hdual : HasMetricMedians (E →L[ℝ] ℝ))
    {K F F' N1 N1' N2 N2' : Set E}
    (hK : IsMaximalProperFace (closedBall (0:E) 1) K)
    (pF : IsParallelPair K F F') (hmF : HasMFaceStructure F)
    (hmax : HasMaximalMRank F)
    (p1 : IsParallelPair K N1 N1') (p2 : IsParallelPair K N2 N2')
    (hF1 : IsMaximalProperFace F (F ∩ N1))
    (hF2 : IsMaximalProperFace F (F ∩ N2))
    (hmeet : (F ∩ N1 ∩ N2).Nonempty)
    (hdisF : Disjoint (F ∩ N1') (F ∩ N2'))
    {x1 x2 y1 y2 : E}
    (hx1 : x1 ∈ F ∩ (closedBall (0:E) 1).extremePoints ℝ)
    (hx2 : x2 ∈ F ∩ (closedBall (0:E) 1).extremePoints ℝ)
    (hy1 : y1 ∈ F' ∩ (closedBall (0:E) 1).extremePoints ℝ)
    (hy2 : y2 ∈ F' ∩ (closedBall (0:E) 1).extremePoints ℝ)
    (hx1n : x1 ∈ N1' ∩ N2) (hx2n : x2 ∈ N1 ∩ N2')
    (he : x1+y1=x2+y2) : False := by
  by_cases hd : Disjoint N1' N2'
  · exact mface_split_core hmed hdual hK pF hmF hmax p1 p2 hF1 hF2 hmeet hd
      hx1 hx2 hy1 hy2 hx1n hx2n he
  have hFb := hK.1.trans pF.1
  have hFn : F.Nonempty := ⟨_,hx1.1⟩
  let D := N1' ∩ N2'
  let C := N1 ∩ N2 ∩ F'
  let J := faceHull (closedBall (0:E) 1) (F ∪ C)
  have hD : IsFace (closedBall (0:E) 1) D :=
    (hK.1.trans p1.2.1).inter (hK.1.trans p2.2.1)
  have hDn : D.Nonempty := not_disjoint_iff.mp hd
  have hC : IsFace K C := (p1.1.inter p2.1).inter pF.2.1
  have hbase : F ∪ C ⊆ K := union_subset pF.1.subset hC.subset
  have hJ : IsFace (closedBall (0:E) 1) J :=
    isFace_faceHull (convex_closedBall _ _) (hbase.trans hK.1.subset)
  have hJK : J ⊆ K := faceHull_min hK.1 hbase
  have hFJ : F ⊆ J := fun _ hz => subset_faceHull (Or.inl hz)
  have hCJ : C ⊆ J := fun _ hz => subset_faceHull (Or.inr hz)
  have hJD : Disjoint J D := by
    by_contra hn
    obtain ⟨y,hy,hyJ,hyD⟩ := (hJ.inter hD).exists_vertex hmed (not_disjoint_iff.mp hn)
    have hyF : y ∉ F := fun hh => disjoint_left.mp hdisF ⟨hh,hyD.1⟩ ⟨hh,hyD.2⟩
    have hyC : y ∉ C := fun hh => disjoint_left.mp p1.2.2.1 hh.1.1 hyD.1
    have hCn : C.Nonempty := by
      by_contra hnC
      apply hyF
      apply faceHull_min hFb _ hyJ
      rw [not_nonempty_iff_eq_empty.mp hnC,union_empty]
    obtain ⟨a,ha,c,hc,z,hz,he⟩ := two_face_exchange hmed hdual hK.1 hK.2.1
      pF.1 hC hFn hCn hy hyJ hyF hyC
    have h1 := p1.square_points hmed hK.1 hc.1.1 hyD.1 (pF.1.subset ha) hz
      (by simpa [add_comm] using he)
    have h2 := p2.square_points hmed hK.1 hc.1.2 hyD.2 (pF.1.subset ha) hz
      (by simpa [add_comm] using he)
    exact disjoint_left.mp hdisF ⟨ha,h1.1⟩ ⟨ha,h2.1⟩
  obtain ⟨t,ht,htJ,htD⟩ := disjoint_faces_dual_vertex hmed hJ hD
    (hFn.mono hFJ) hDn hJD
  let L := {x ∈ closedBall (0:E) 1 | t x=1}
  have hL : IsMaximalProperFace (closedBall (0:E) 1) L :=
    dual_vertex_maximal_support hmed ht
  have hFL : F ⊆ L := fun x hx => ⟨hFb.subset hx,htJ x (hFJ hx)⟩
  obtain ⟨A,pA⟩ := maximal_mface_parallel hmed hL.1 hL.2.1
    (hFb.mono hL.1.subset hFL) hmF hmax
  obtain ⟨f1,hf1,eN1,eN1'⟩ := p1.support_dual_vertex hmed hK.1 ⟨_,hx2n.1⟩ ⟨_,hx1n.1⟩
  obtain ⟨f2,hf2,eN2,eN2'⟩ := p2.support_dual_vertex hmed hK.1 ⟨_,hx1n.2⟩ ⟨_,hx2n.2⟩
  let M1 := {x ∈ L | f1 x=1}
  let M1' := {x ∈ L | f1 x= -1}
  let M2 := {x ∈ L | f2 x=1}
  let M2' := {x ∈ L | f2 x= -1}
  have q1 : IsParallelPair L M1 M1' := parallelPair_of_dual_vertex hmed hL.1 hf1
  have q2 : IsParallelPair L M2 M2' := parallelPair_of_dual_vertex hmed hL.1 hf2
  have eF1 : F ∩ M1 = F ∩ N1 := by
    rw [IsParallelPair.restrict_support hFL (show M1={x ∈ L | f1 x=1} from rfl),
      IsParallelPair.restrict_support pF.1.subset eN1]
  have eF2 : F ∩ M2 = F ∩ N2 := by
    rw [IsParallelPair.restrict_support hFL (show M2={x ∈ L | f2 x=1} from rfl),
      IsParallelPair.restrict_support pF.1.subset eN2]
  have hmeetL : (F ∩ M1 ∩ M2).Nonempty := by
    obtain ⟨z,⟨hzF,hzN1⟩,hzN2⟩ := hmeet
    exact ⟨z,⟨hzF,(show z ∈ F ∩ M1 by rw [eF1]; exact ⟨hzF,hzN1⟩).2⟩,(show z ∈ F ∩ M2 by rw [eF2]; exact ⟨hzF,hzN2⟩).2⟩
  have hdisL : Disjoint M1' M2' := by
    by_contra hn
    obtain ⟨z,hz,hz1,hz2⟩ := ((hL.1.trans q1.2.1).inter
      (hL.1.trans q2.2.1)).exists_vertex hmed (not_disjoint_iff.mp hn)
    have hzL : z ∈ L := hz1.1
    rcases maximal_unit_face_vertex_sign hmed hK (hFn.mono pF.1.subset) hz with hzK | hzK
    · have hzD : z ∈ D := ⟨by rw [eN1']; exact ⟨hzK,hz1.2⟩,
          by rw [eN2']; exact ⟨hzK,hz2.2⟩⟩
      have hh := htD z hzD
      linarith [hzL.2]
    · have hzN1 : -z ∈ N1 := by rw [eN1]; exact ⟨hzK,by simp [hz1.2]⟩
      have hzN2 : -z ∈ N2 := by rw [eN2]; exact ⟨hzK,by simp [hz2.2]⟩
      have hzF' : -z ∈ F' := (pF.not_mem_iff
        (hK.1.extreme_mem (extreme_unit_neg hz) hzK)).mp (by
          intro hh
          have hh' := (hFL hh).2
          simp only [map_neg] at hh'
          linarith [hzL.2])
      have hh := htJ (-z) (hCJ ⟨⟨hzN1,hzN2⟩,hzF'⟩)
      simp only [map_neg] at hh
      linarith [hzL.2]
  have htx1 := htJ x1 (hFJ hx1.1)
  have htx2 := htJ x2 (hFJ hx2.1)
  have hty : t y1=t y2 := by
    have hh := congrArg t he
    simp only [map_add,htx1,htx2] at hh
    linarith
  obtain ⟨u1,hu1,u2,hu2,heu⟩ :
      ∃ u1 ∈ A ∩ (closedBall (0:E) 1).extremePoints ℝ,
        ∃ u2 ∈ A ∩ (closedBall (0:E) 1).extremePoints ℝ, x1+u1=x2+u2 := by
    rcases extreme_dual_eval_eq_one_or_neg_one hmed hy1.2 ht with hty1 | hty1
    · have hy1L : y1 ∈ L := ⟨hy1.2.1,hty1⟩
      have hy2L : y2 ∈ L := ⟨hy2.2.1,hty ▸ hty1⟩
      exact ⟨y1,⟨(pA.not_mem_iff (hL.1.extreme_mem hy1.2 hy1L)).mp
          (fun hh => disjoint_left.mp pF.2.2.1 hh hy1.1),hy1.2⟩,
        y2,⟨(pA.not_mem_iff (hL.1.extreme_mem hy2.2 hy2L)).mp
          (fun hh => disjoint_left.mp pF.2.2.1 hh hy2.1),hy2.2⟩,he⟩
    · have hy1L : -y1 ∈ L := ⟨(extreme_unit_neg hy1.2).1,by simp [hty1]⟩
      have hy2L : -y2 ∈ L := ⟨(extreme_unit_neg hy2.2).1,by simp [← hty,hty1]⟩
      refine ⟨-y2,⟨(pA.not_mem_iff (hL.1.extreme_mem (extreme_unit_neg hy2.2) hy2L)).mp
          (fun hh => proper_unit_face_not_neg hmed hK.1 hK.2.1
            (pF.2.1.subset hy2.1) (pF.1.subset hh)),extreme_unit_neg hy2.2⟩,
        -y1,⟨(pA.not_mem_iff (hL.1.extreme_mem (extreme_unit_neg hy1.2) hy1L)).mp
          (fun hh => proper_unit_face_not_neg hmed hK.1 hK.2.1
            (pF.2.1.subset hy1.1) (pF.1.subset hh)),extreme_unit_neg hy1.2⟩,?_⟩
      linear_combination (norm := module) he
  apply mface_split_core hmed hdual hL pA hmF hmax q1 q2
    (eF1.symm ▸ hF1) (eF2.symm ▸ hF2) hmeetL hdisL hx1 hx2 hu1 hu2 _ _ heu
  · exact ⟨⟨hFL hx1.1,(eN1' ▸ hx1n.1).2⟩,hFL hx1.1,(eN2 ▸ hx1n.2).2⟩
  · exact ⟨⟨hFL hx2.1,(eN1 ▸ hx2n.1).2⟩,hFL hx2.1,(eN2' ▸ hx2n.2).2⟩

end

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [Nontrivial E]

theorem maximal_mface_split (hmed : HasMetricMedians E)
    (hdual : HasMetricMedians (E →L[ℝ] ℝ)) {K F : Set E}
    (hK : IsMaximalProperFace (closedBall (0:E) 1) K)
    (hF : IsFace K F) (hmF : HasMFaceStructure F) (hmax : HasMaximalMRank F) :
    IsSplitFace K F := by
  by_contra hn
  obtain ⟨F',pF⟩ := maximal_mface_parallel hmed hK.1 hK.2.1 hF hmF hmax
  obtain ⟨x1,hx1,x2,hx2,y1,hy1,y2,hy2,hne,he⟩ :=
    nonsplit_vertex_parallelogram hmed hK.1 hK.2.1 pF hn
  have hFb := hK.1.trans hF
  have hFp := proper_unit_face_subface_ne hK.1 hK.2.1 hF.subset
  have hx1F := hFb.extreme_mem hx1.2 hx1.1
  have hx2F := hFb.extreme_mem hx2.2 hx2.1
  have hx1K := hK.1.extreme_mem hx1.2 (hF.subset hx1.1)
  have hx2K := hK.1.extreme_mem hx2.2 (hF.subset hx2.1)
  have hy1K := hK.1.extreme_mem hy1.2 (pF.2.1.subset hy1.1)
  have hy2K := hK.1.extreme_mem hy2.2 (pF.2.1.subset hy2.1)
  obtain ⟨F1,hF1,hx2F1,hx1F1⟩ := extend_face_avoiding_vertex hmed hFb hFp
    (IsFace.singleton hx2F) (singleton_nonempty x2) hx1F (by simpa using hne)
  have hx2F1 : x2 ∈ F1 := hx2F1 (mem_singleton _)
  obtain ⟨F1',pF1⟩ := maximal_proper_parallel hmed hFb hF1 ⟨_,hx2F1⟩
  have hx1F1' := (pF1.not_mem_iff hx1F).mp hx1F1
  have hx2F1' : x2 ∉ F1' := fun hh => disjoint_left.mp pF1.2.2.1 hx2F1 hh
  obtain ⟨F2,hF2,hF1'F2,hx2F2⟩ := extend_face_avoiding_vertex hmed hFb hFp
    pF1.2.1 ⟨_,hx1F1'⟩ hx2F hx2F1'
  have hx1F2 := hF1'F2 hx1F1'
  obtain ⟨F2',pF2⟩ := maximal_proper_parallel hmed hFb hF2 ⟨_,hx1F2⟩
  have hx2F2' := (pF2.not_mem_iff hx2F).mp hx2F2
  have hdis : Disjoint F1' F2' := disjoint_left.mpr
    (fun z hz hz' => disjoint_left.mp pF2.2.2.1 (hF1'F2 hz) hz')
  have hmeet : (F1 ∩ F2).Nonempty := by
    by_contra hn
    have hd : Disjoint F1 F2 := disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hn)
    obtain ⟨G,pG⟩ := (maximal_mface_children_parallel hmed hK.1 hK.2.1 pF hmax
      hF1 hF2 ⟨_,hx2F1⟩ ⟨_,hx1F2⟩ hd).1
    have hy1G := (pG.not_mem_iff hy1K).mp
      (fun hh => disjoint_left.mp pF.2.2.1 (hF1.1.subset hh) hy1.1)
    have hx1G := (pG.not_mem_iff hx1K).mp hx1F1
    have hx2G := (face_mem_of_parallelogram pG.2.1 hx1G hy1G hx2K.1 hy2K.1 he).1
    exact disjoint_left.mp pG.2.2.1 hx2F1 hx2G
  obtain ⟨f1,hf1,eF1,eF1'⟩ := pF1.support_dual_vertex hmed hFb ⟨_,hx2F1⟩ ⟨_,hx1F1'⟩
  obtain ⟨f2,hf2,eF2,eF2'⟩ := pF2.support_dual_vertex hmed hFb ⟨_,hx1F2⟩ ⟨_,hx2F2'⟩
  let N1 := {x ∈ K | f1 x=1}
  let N1' := {x ∈ K | f1 x= -1}
  let N2 := {x ∈ K | f2 x=1}
  let N2' := {x ∈ K | f2 x= -1}
  have p1 : IsParallelPair K N1 N1' := parallelPair_of_dual_vertex hmed hK.1 hf1
  have p2 : IsParallelPair K N2 N2' := parallelPair_of_dual_vertex hmed hK.1 hf2
  have e1 : F ∩ N1 = F1 := (IsParallelPair.restrict_support hF.subset rfl).trans eF1.symm
  have e2 : F ∩ N2 = F2 := (IsParallelPair.restrict_support hF.subset rfl).trans eF2.symm
  have e1' : F ∩ N1' = F1' := by
    rw [eF1']; ext x
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,hF.subset h.1,h.2⟩⟩
  have e2' : F ∩ N2' = F2' := by
    rw [eF2']; ext x
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,hF.subset h.1,h.2⟩⟩
  have hmeetK : (F ∩ N1 ∩ N2).Nonempty := by
    obtain ⟨z,hz1,hz2⟩ := hmeet
    have hzN1 : z ∈ F ∩ N1 := e1.symm ▸ hz1
    have hzN2 : z ∈ F ∩ N2 := e2.symm ▸ hz2
    exact ⟨z,hzN1,hzN2.2⟩
  exact mface_split_precore hmed hdual hK pF hmF hmax p1 p2
    (e1.symm ▸ hF1) (e2.symm ▸ hF2) hmeetK (by rwa [e1',e2']) hx1 hx2 hy1 hy2
    ⟨⟨hx1K.1,(eF1' ▸ hx1F1').2⟩,hx1K.1,(eF2 ▸ hx1F2).2⟩
    ⟨⟨hx2K.1,(eF1 ▸ hx2F1).2⟩,hx2K.1,(eF2' ▸ hx2F2').2⟩ he

end
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [inst541 : FiniteDimensional ℝ E] [inst542 : Nontrivial E]

omit inst541 inst542 in
lemma faceRank_singleton_le [FiniteDimensional ℝ E] [Nontrivial E] (a : E) : faceRank ({a} : Set E) ≤ 1 := by
  simpa [faceRank] using (finrank_span_le_card ({a} : Set E) (R := ℝ))

lemma mface_pair_obstruction (hmed : HasMetricMedians E) {L : Set E}
    (hL : IsFace (closedBall (0:E) 1) L) (hp : L ≠ closedBall (0:E) 1)
    (hr : 2 < faceRank L) (hm : HasMFaceStructure L)
    {a b : E} (ha : a ∈ L.extremePoints ℝ) (hb : b ∈ L.extremePoints ℝ)
    (hne : a ≠ b)
    (hn1 : ∀ g ∈ L ∩ (closedBall (0:E) 1).extremePoints ℝ,
      g ≠ a → g ≠ b → ∀ h ∈ closedBall (0:E) 1, a+g ≠ b+h)
    (hn2 : ∀ g ∈ L ∩ (closedBall (0:E) 1).extremePoints ℝ,
      g ≠ a → g ≠ b → ∀ h ∈ closedBall (0:E) 1, a+b ≠ g+h) : False := by
  have hav : a ∈ (closedBall (0:E) 1).extremePoints ℝ := hL.2.extremePoints_subset_extremePoints ha
  have hbv : b ∈ (closedBall (0:E) 1).extremePoints ℝ := hL.2.extremePoints_subset_extremePoints hb
  obtain ⟨H,H',hH,hH',hHn,hH'n,hHH',haH,hbH'⟩ :
      ∃ H H', IsMaximalProperFace L H ∧ IsMaximalProperFace L H' ∧
        H.Nonempty ∧ H'.Nonempty ∧ Disjoint H H' ∧ a ∈ H ∧ b ∈ H' := by
    obtain ⟨H,H',hH,hH',hHn,hH'n,hHH'⟩ := hm
    have p := maximal_pair_of_disjoint hmed hL hH hH' hHn hH'n hHH'
    have hnH : ¬ (a ∈ H ∧ b ∈ H) := by
      rintro ⟨haH,hbH⟩
      obtain ⟨g,hg,h,hh,he⟩ := hH'.exchange hmed hL p.symm hH'n ha haH hb hbH
      exact hn1 g ⟨hH'.1.subset hg.1,hg.2⟩
        (fun e => disjoint_left.mp hHH' haH (e ▸ hg.1))
        (fun e => disjoint_left.mp hHH' hbH (e ▸ hg.1)) h hh.2.1 he
    have hnH' : ¬ (a ∈ H' ∧ b ∈ H') := by
      rintro ⟨haH,hbH⟩
      obtain ⟨g,hg,h,hh,he⟩ := hH.exchange hmed hL p hHn ha haH hb hbH
      exact hn1 g ⟨hH.1.subset hg.1,hg.2⟩
        (fun e => disjoint_left.mp hHH' (e ▸ hg.1) haH)
        (fun e => disjoint_left.mp hHH' (e ▸ hg.1) hbH) h hh.2.1 he
    rcases p.vertex_mem ha with haH | haH
    · exact ⟨H,H',hH,hH',hHn,hH'n,hHH',haH,
        (p.not_mem_iff hb).mp (fun hbH => hnH ⟨haH,hbH⟩)⟩
    · exact ⟨H',H,hH',hH,hH'n,hHn,hHH'.symm,haH,
        (p.symm.not_mem_iff hb).mp (fun hbH => hnH' ⟨haH,hbH⟩)⟩
  have pH := maximal_pair_of_disjoint hmed hL hH hH' hHn hH'n hHH'
  let J := faceHull (closedBall (0:E) 1) ({a} ∪ {b})
  have hbase : {a} ∪ {b} ⊆ L := union_subset (singleton_subset_iff.mpr ha.1)
    (singleton_subset_iff.mpr hb.1)
  have hJ : IsFace (closedBall (0:E) 1) J :=
    isFace_faceHull (convex_closedBall _ _) (hbase.trans hL.subset)
  have hJL : J ⊆ L := faceHull_min hL hbase
  have haJ : a ∈ J := subset_faceHull (Or.inl (mem_singleton _))
  have hbJ : b ∈ J := subset_faceHull (Or.inr (mem_singleton _))
  have hJv : ∀ g ∈ (closedBall (0:E) 1).extremePoints ℝ ∩ J, g=a ∨ g=b := by
    intro g hg
    by_contra hn
    obtain ⟨h,hh,he⟩ := vertex_in_two_vertex_face hmed hav hbv hg.1 hg.2
    exact hn2 g ⟨hJL hg.2,hg.1⟩ (fun e => hn (Or.inl e))
      (fun e => hn (Or.inr e)) h hh.1 he
  have hHr := maximal_proper_rank hmed hL hp hH hHn
  have hHball := hL.trans hH.1
  have hHproper := proper_unit_face_subface_ne hL hp hH.1.subset
  have hHn1 : ¬ H ⊆ {a} := by
    intro hh
    have hle := (faceRank_mono hh).trans (faceRank_singleton_le a)
    omega
  obtain ⟨w,hw,hwH,hwa⟩ := hHball.exists_vertex_outside hmed (convex_singleton a) hHn1
  obtain ⟨N,hN,hwN,haN⟩ := extend_face_avoiding_vertex hmed hHball hHproper
    (IsFace.singleton (hHball.extreme_mem hw hwH)) (singleton_nonempty w)
    (hHball.extreme_mem hav haH) (by simpa [eq_comm] using hwa)
  have hwN : w ∈ N := hwN (mem_singleton _)
  have hNball := hHball.trans hN.1
  have hNJ : Disjoint N J := by
    by_contra hd
    obtain ⟨z,hz,hzN,hzJ⟩ := (hNball.inter hJ).exists_vertex hmed (not_disjoint_iff.mp hd)
    rcases hJv z ⟨hz,hzJ⟩ with rfl | rfl
    · exact haN hzN
    · exact disjoint_left.mp hHH' (hN.1.subset hzN) hbH'
  obtain ⟨f,hf,hfN,hfJ⟩ := disjoint_faces_dual_vertex hmed hNball hJ
    ⟨_,hwN⟩ ⟨_,haJ⟩ hNJ
  let M := {x ∈ L | f x=1}
  let M' := {x ∈ L | f x= -1}
  have pM : IsParallelPair L M M' := parallelPair_of_dual_vertex hmed hL hf
  have hNM : N ⊆ M := fun x hx => ⟨hH.1.subset (hN.1.subset hx),hfN x hx⟩
  have haM' : a ∈ M' := ⟨ha.1,hfJ a haJ⟩
  have hbM' : b ∈ M' := ⟨hb.1,hfJ b hbJ⟩
  have hMn : M.Nonempty := ⟨_,hNM hwN⟩
  have hMp : M ≠ L := pM.left_ne ⟨_,haM'⟩
  have hM'p : M' ≠ L := pM.symm.left_ne hMn
  have hMH' : (M ∩ H').Nonempty := by
    by_contra hn
    have hd : Disjoint H' M := (disjoint_iff_inter_eq_empty.mpr
      (not_nonempty_iff_eq_empty.mp hn)).symm
    have hsub := pM.subset_of_disjoint hmed hL hH'.1 hd
    have he := hH'.2.2 M' pM.2.1 hsub hM'p
    exact disjoint_left.mp hHH' haH (he ▸ haM')
  have hNm : N ≠ M := by
    intro he
    obtain ⟨x,hxM,hxH'⟩ := hMH'
    exact disjoint_left.mp hHH' (hN.1.subset (he.symm ▸ hxM)) hxH'
  have hNr := maximal_proper_rank hmed hHball hHproper hN ⟨_,hwN⟩
  have hNMrank := faceRank_lt hmed (hL.trans pM.1)
    (proper_unit_face_subface_ne hL hp pM.1.subset)
    (hNball.mono (hL.trans pM.1).subset hNM) hNm
  have hMrank := faceRank_lt hmed hL hp pM.1 hMp
  have hMm := rank_succ_maximal hmed hL hp pM.1 hMp (by omega)
  obtain ⟨g,hg,h,hh,he⟩ := hMm.exchange hmed hL pM hMn ha haM' hb hbM'
  exact hn1 g ⟨pM.1.subset hg.1,hg.2⟩
    (fun e => disjoint_left.mp pM.2.2.1 (e ▸ hg.1) haM')
    (fun e => disjoint_left.mp pM.2.2.1 (e ▸ hg.1) hbM') h hh.2.1 he

end

open Set Metric
open scoped Pointwise
section
variable {E : Type*} [NormedAddCommGroup E] [inst544 : NormedSpace ℝ E]

lemma IsFace.neg {K F : Set E} (h : IsFace K F) : IsFace (-K) (-F) := by
  refine ⟨h.1.neg,⟨fun x hx => h.subset hx,?_⟩⟩
  intro x hx y hy z hz hs
  apply h.2.left_mem_of_mem_openSegment hx hy hz
  obtain ⟨a,b,ha,hb,hab,he⟩ := hs
  refine ⟨a,b,ha,hb,hab,?_⟩
  rw [← he]
  module

lemma IsMaximalProperFace.neg {K F : Set E} (h : IsMaximalProperFace K F) :
    IsMaximalProperFace (-K) (-F) := by
  refine ⟨h.1.neg,fun he => h.2.1 (by simpa using congrArg Neg.neg he),?_⟩
  intro G hG hFG hp
  have hG' : IsFace K (-G) := by simpa using hG.neg
  have hFG' : F ⊆ -G := by
    intro x hx
    have hh := hFG (show -x ∈ -F by simpa using hx)
    simpa using hh
  have hp' : -G ≠ K := fun he => hp (by simpa using congrArg Neg.neg he)
  have he := h.2.2 (-G) hG' hFG' hp'
  simpa using congrArg Neg.neg he

lemma HasMFaceStructure.neg {F : Set E} (h : HasMFaceStructure F) : HasMFaceStructure (-F) := by
  obtain ⟨G,H,hG,hH,hGn,hHn,hd⟩ := h
  refine ⟨-G,-H,hG.neg,hH.neg,?_,?_,?_⟩
  · obtain ⟨g,hg⟩ := hGn
    exact ⟨-g,by simpa using hg⟩
  · obtain ⟨g,hg⟩ := hHn
    exact ⟨-g,by simpa using hg⟩
  · exact disjoint_left.mpr (fun x hx hy => disjoint_left.mp hd hx hy)

omit inst544 in
lemma neg_unitBall [NormedSpace ℝ E] : -(closedBall (0:E) 1) = closedBall (0:E) 1 := by
  ext x
  simp

lemma IsMaximalProperFace.neg_unit {K : Set E}
    (h : IsMaximalProperFace (closedBall (0:E) 1) K) :
    IsMaximalProperFace (closedBall (0:E) 1) (-K) := by
  simpa only [neg_unitBall] using h.neg

end

section
open Set Metric
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [Nontrivial E]

lemma maximal_unit_face_span (hmed : HasMetricMedians E) {K : Set E}
    (hK : IsMaximalProperFace (closedBall (0:E) 1) K) (hn : K.Nonempty) :
    Submodule.span ℝ K = ⊤ := by
  obtain ⟨f,hf,he⟩ := maximal_unit_face_support hmed hK hn
  rw [he]
  exact span_support_dual_vertex hmed hf

lemma dual_eq_on_maximal_face (hmed : HasMetricMedians E) {K : Set E}
    (hK : IsMaximalProperFace (closedBall (0:E) 1) K) (hn : K.Nonempty)
    {f g : E →L[ℝ] ℝ} (he : ∀ x ∈ K, f x=g x) : f=g := by
  ext x
  apply LinearMap.eqOn_span (f:=f.toLinearMap) (g:=g.toLinearMap) he
  rw [maximal_unit_face_span hmed hK hn]
  trivial

lemma dual_vertex_eq_of_supports (hmed : HasMetricMedians E) {K : Set E}
    (hK : IsMaximalProperFace (closedBall (0:E) 1) K) (hn : K.Nonempty)
    {f g : E →L[ℝ] ℝ}
    (hf : f ∈ (closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints ℝ)
    (hg : g ∈ (closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints ℝ)
    (he : {x ∈ K | f x=1} = {x ∈ K | g x=1}) : f=g := by
  have hsub : K ⊆ (f-g).ker := by
    apply hK.1.subset_of_vertices hmed (Submodule.convex _)
    intro x hx
    change f x-g x=0
    rcases extreme_dual_eval_eq_one_or_neg_one hmed hx.1 hf with hfx | hfx
    · have hgx : g x=1 := (show x ∈ {x ∈ K | g x=1} from he ▸ ⟨hx.2,hfx⟩).2
      linarith
    · rcases extreme_dual_eval_eq_one_or_neg_one hmed hx.1 hg with hgx | hgx
      · have hfx' : f x=1 := (show x ∈ {x ∈ K | f x=1} from he.symm ▸ ⟨hx.2,hgx⟩).2
        linarith
      · linarith
  exact dual_eq_on_maximal_face hmed hK hn (fun x hx => sub_eq_zero.mp (hsub hx))

lemma dual_mface_obstruction_at_vertex (hmed : HasMetricMedians E)
    (hdual : HasMetricMedians (E →L[ℝ] ℝ)) (hdim : 2 < Module.finrank ℝ E)
    {K : Set E} (hK : IsMaximalProperFace (closedBall (0:E) 1) K)
    (hmK : HasMFaceStructure K) {x0 : E}
    (hx0 : x0 ∈ (closedBall (0:E) 1).extremePoints ℝ) (hx0K : x0 ∈ K)
    {L : Set (E →L[ℝ] ℝ)}
    (hL : IsMaximalProperFace (closedBall (0 : E →L[ℝ] ℝ) 1) L)
    (eL : L = {f ∈ closedBall (0 : E →L[ℝ] ℝ) 1 | f x0=1})
    (hmL : HasMFaceStructure L) : False := by
  have hKn : K.Nonempty := ⟨_,hx0K⟩
  obtain ⟨a,ha,eK⟩ := maximal_unit_face_support hmed hK hKn
  obtain ⟨F,F',hF,hF',hFn,hF'n,hFF',hx0F⟩ :
      ∃ F F', IsMaximalProperFace K F ∧ IsMaximalProperFace K F' ∧
        F.Nonempty ∧ F'.Nonempty ∧ Disjoint F F' ∧ x0 ∈ F := by
    obtain ⟨F,F',hF,hF',hFn,hF'n,hFF'⟩ := hmK
    have p := maximal_pair_of_disjoint hmed hK.1 hF hF' hFn hF'n hFF'
    rcases p.vertex_mem (hK.1.extreme_mem hx0 hx0K) with hh | hh
    · exact ⟨F,F',hF,hF',hFn,hF'n,hFF',hh⟩
    · exact ⟨F',F,hF',hF,hF'n,hFn,hFF'.symm,hh⟩
  have pF := maximal_pair_of_disjoint hmed hK.1 hF hF' hFn hF'n hFF'
  obtain ⟨b,hb,eF,eF'⟩ := pF.support_dual_vertex hmed hK.1 hFn hF'n
  have haL : a ∈ L := by rw [eL]; exact ⟨ha.1,(eK ▸ hx0K).2⟩
  have hbL : b ∈ L := by rw [eL]; exact ⟨hb.1,(eF ▸ hx0F).2⟩
  have hab : a ≠ b := by
    intro he
    obtain ⟨x,hx⟩ := hF'n
    have h1 := (eK ▸ hF'.1.subset hx).2
    have h2 := (eF' ▸ hx).2
    rw [he] at h1
    linarith
  have hrd : 2 < faceRank L := by
    rw [maximal_unit_face_rank hdual hL ⟨_,haL⟩,finrank_strongDual]
    exact hdim
  apply mface_pair_obstruction hdual hL.1 hL.2.1 hrd hmL
    (hL.1.extreme_mem ha haL) (hL.1.extreme_mem hb hbL) hab
  · intro g hg hga hgb h hh he
    let G := {x ∈ K | g x=1}
    let G' := {x ∈ K | g x= -1}
    have pG : IsParallelPair K G G' := parallelPair_of_dual_vertex hmed hK.1 hg.2
    have hx0G : x0 ∈ G := ⟨hx0K,(eL ▸ hg.1).2⟩
    have hcross : (F' ∩ G).Nonempty := by
      by_contra hn
      have hd : Disjoint F' G := disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hn)
      have hsub := pG.subset_of_disjoint hmed hK.1 hF'.1 hd
      have heG' : G'=F' := hF'.2.2 G' pG.2.1 hsub (pG.symm.left_ne ⟨_,hx0G⟩)
      have heG : G=F := by
        rw [heG'] at pG
        exact pG.symm.complement_unique hmed hK.1 pF.symm
      apply hgb
      exact dual_vertex_eq_of_supports hmed hK hKn hg.2 hb (heG.trans eF)
    obtain ⟨x,hxF',hxG⟩ := hcross
    have hax := (eK ▸ hF'.1.subset hxF').2
    have hbx := (eF' ▸ hxF').2
    have hhx := dual_eval_bounds (mem_closedBall_zero_iff.mp hh) (hK.1.subset hxG.1)
    have hhe := congrArg (fun f : E →L[ℝ] ℝ => f x) he
    change a x+g x=b x+h x at hhe
    linarith [hxG.2]
  · intro g hg hga hgb h hh he
    let G := {x ∈ K | g x=1}
    let G' := {x ∈ K | g x= -1}
    have pG : IsParallelPair K G G' := parallelPair_of_dual_vertex hmed hK.1 hg.2
    have hGp : G ≠ K := by
      intro heG
      apply hga
      apply dual_eq_on_maximal_face hmed hK hKn
      intro x hx
      exact (heG.symm ▸ hx).2.trans (eK ▸ hx).2.symm
    have hcross : (F ∩ G').Nonempty := by
      by_contra hn
      have hd : Disjoint F G' := disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hn)
      have hsub := pG.symm.subset_of_disjoint hmed hK.1 hF.1 hd
      have heG : G=F := hF.2.2 G pG.1 hsub hGp
      exact hgb (dual_vertex_eq_of_supports hmed hK hKn hg.2 hb (heG.trans eF))
    obtain ⟨x,hxF,hxG'⟩ := hcross
    have hax := (eK ▸ hF.1.subset hxF).2
    have hbx := (eF ▸ hxF).2
    have hhx := dual_eval_bounds (mem_closedBall_zero_iff.mp hh) (hK.1.subset hxG'.1)
    have hhe := congrArg (fun f : E →L[ℝ] ℝ => f x) he
    change a x+b x=g x+h x at hhe
    linarith [hxG'.2]

theorem not_primal_dual_maximal_mfaces (hmed : HasMetricMedians E)
    (hdual : HasMetricMedians (E →L[ℝ] ℝ)) (hdim : 2 < Module.finrank ℝ E)
    {K : Set E} (hK : IsMaximalProperFace (closedBall (0:E) 1) K)
    (hmK : HasMFaceStructure K)
    {L : Set (E →L[ℝ] ℝ)}
    (hL : IsMaximalProperFace (closedBall (0 : E →L[ℝ] ℝ) 1) L)
    (hmL : HasMFaceStructure L) : False := by
  obtain ⟨A,B,hA,hB,hAn,hBn,hAB⟩ := hmL
  have hLn : L.Nonempty := hAn.mono hA.1.subset
  obtain ⟨u,hu,he⟩ := maximal_unit_face_support hdual hL hLn
  rw [← LinearIsometryEquiv.image_extreme_unit (finiteBidual (E:=E))] at hu
  obtain ⟨x0,hx0,rfl⟩ := hu
  change L = {f ∈ closedBall (0 : E →L[ℝ] ℝ) 1 | f x0=1} at he
  have hKn : K.Nonempty := by
    obtain ⟨A,B,hA,hB,hAn,hBn,hAB⟩ := hmK
    exact hAn.mono hA.1.subset
  rcases maximal_unit_face_vertex_sign hmed hK hKn hx0 with hxK | hxK
  · exact dual_mface_obstruction_at_vertex hmed hdual hdim hK hmK hx0 hxK hL he
      ⟨A,B,hA,hB,hAn,hBn,hAB⟩
  · exact dual_mface_obstruction_at_vertex hmed hdual hdim hK.neg_unit hmK.neg hx0 hxK
      hL he ⟨A,B,hA,hB,hAn,hBn,hAB⟩

end

open Set Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [Nontrivial E]

lemma face_rank_gt_one_vertices (hmed : HasMetricMedians E) {K : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (hr : 1 < faceRank K) :
    ∃ x ∈ K.extremePoints ℝ, ∃ y ∈ K.extremePoints ℝ, x ≠ y := by
  have hn : K.Nonempty := by
    by_contra hh
    rw [not_nonempty_iff_eq_empty.mp hh,faceRank,Submodule.span_empty,finrank_bot] at hr
    omega
  obtain ⟨x,hx,hxK⟩ := hK.exists_vertex hmed hn
  have hnot : ¬ K ⊆ {x} := by
    intro hh
    have := (faceRank_mono hh).trans (faceRank_singleton_le x)
    omega
  obtain ⟨y,hy,hyK,hyn⟩ := hK.exists_vertex_outside hmed (convex_singleton x) hnot
  exact ⟨x,hK.extreme_mem hx hxK,y,hK.extreme_mem hy hyK,by simpa [eq_comm] using hyn⟩

lemma face_rank_two_pair (hmed : HasMetricMedians E) {K : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (hp : K ≠ closedBall (0:E) 1)
    (hr : faceRank K = 2) :
    ∃ F G, IsSplitPair K F G ∧ IsMaximalProperFace K F ∧
      IsMaximalProperFace K G ∧ F.Nonempty ∧ G.Nonempty := by
  obtain ⟨x,hx,y,hy,hxy⟩ := face_rank_gt_one_vertices hmed hK (by omega)
  obtain ⟨F,hF,hxF,hyF⟩ := extend_face_avoiding_vertex hmed hK hp
    (IsFace.singleton hx) (singleton_nonempty x) hy (by simpa [eq_comm] using hxy)
  have hxF' := hxF (mem_singleton x)
  have hFn : F.Nonempty := ⟨_,hxF'⟩
  have hrF := maximal_proper_rank hmed hK hp hF hFn
  have eF : F = {x} := by
    by_contra hn
    have hs := (IsFace.singleton hx).mono hF.1.subset hxF
    have := faceRank_lt hmed (hK.trans hF.1)
      (proper_unit_face_subface_ne hK hp hF.1.subset) hs (Ne.symm hn)
    have hpos : 0 < faceRank ({x} : Set E) := by
      have hn0 : x ≠ 0 := by
        intro hh
        have := norm_eq_one_of_mem_proper_face hK.2 hp hx.1
        simp [hh] at this
      simp [faceRank,finrank_span_singleton hn0]
    omega
  obtain ⟨G,p⟩ := maximal_proper_parallel hmed hK hF hFn
  have hyG := (p.not_mem_iff hy).mp hyF
  have hGn : G.Nonempty := ⟨_,hyG⟩
  have hGp := p.symm.left_ne hFn
  have hGr := faceRank_lt hmed hK hp p.2.1 hGp
  have hGpos : 0 < faceRank G := by
    have hs := faceRank_mono (singleton_subset_iff.mpr hyG)
    have hy0 : y ≠ 0 := by
      intro hh
      have := norm_eq_one_of_mem_proper_face hK.2 hp hy.1
      simp [hh] at this
    have : faceRank ({y} : Set E) = 1 := by simp [faceRank,finrank_span_singleton hy0]
    omega
  have hmG := rank_succ_maximal hmed hK hp p.2.1 hGp (by omega)
  refine ⟨F,G,⟨p,split_of_no_vertex_parallelogram hmed hK hp p ?_⟩,hF,hmG,hFn,hGn⟩
  intro a ha b hb c hc d hd he
  rw [eF] at ha hb
  exact (mem_singleton_iff.mp ha.1).trans (mem_singleton_iff.mp hb.1).symm

lemma exists_rank_two_face (hmed : HasMetricMedians E) {K : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (hp : K ≠ closedBall (0:E) 1)
    (hr : 2 ≤ faceRank K) :
    ∃ F, IsFace K F ∧ faceRank F = 2 := by
  generalize he : faceRank K = r
  induction r using Nat.strong_induction_on generalizing K with
  | h r ih =>
    by_cases he2 : faceRank K = 2
    · exact ⟨K,IsFace.refl hK.1,he2⟩
    obtain ⟨x,hx,y,hy,hxy⟩ := face_rank_gt_one_vertices hmed hK (by omega)
    obtain ⟨F,hF,hxF,hyF⟩ := extend_face_avoiding_vertex hmed hK hp
      (IsFace.singleton hx) (singleton_nonempty x) hy (by simpa [eq_comm] using hxy)
    have hFr := maximal_proper_rank hmed hK hp hF ⟨_,hxF (mem_singleton x)⟩
    obtain ⟨G,hG,hrG⟩ := ih (faceRank F) (by omega) (hK.trans hF.1)
      (proper_unit_face_subface_ne hK hp hF.1.subset) (by omega) rfl
    exact ⟨G,hF.1.trans hG,hrG⟩

lemma exists_maximal_unit_face (hmed : HasMetricMedians E) :
    ∃ K, IsMaximalProperFace (closedBall (0:E) 1) K ∧ K.Nonempty := by
  obtain ⟨f,hf⟩ := (isCompact_closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints_nonempty
    ⟨0,by simp⟩
  refine ⟨_,dual_vertex_maximal_support hmed hf,?_⟩
  by_contra hn
  have hs := span_support_dual_vertex hmed hf
  rw [not_nonempty_iff_eq_empty.mp hn,Submodule.span_empty] at hs
  exact bot_ne_top hs

lemma exists_maximal_mface (hmed : HasMetricMedians E) (hdim : 2 ≤ Module.finrank ℝ E) :
    ∃ F, IsFace (closedBall (0:E) 1) F ∧ F ≠ closedBall (0:E) 1 ∧
      HasMFaceStructure F ∧ HasMaximalMRank F ∧ 2 ≤ faceRank F := by
  classical
  obtain ⟨K,hK,hKn⟩ := exists_maximal_unit_face hmed
  have hKr := maximal_unit_face_rank hmed hK hKn
  obtain ⟨F,hFK,hFr⟩ := exists_rank_two_face hmed hK.1 hK.2.1 (by omega)
  have hF := hK.1.trans hFK
  have hp := proper_unit_face_subface_ne hK.1 hK.2.1 hFK.subset
  obtain ⟨A,B,p,hA,hB,hAn,hBn⟩ := face_rank_two_pair hmed hF hp hFr
  have hmF : HasMFaceStructure F := ⟨A,B,hA,hB,hAn,hBn,p.1.2.2.1⟩
  let D := {F : Set E | IsFace (closedBall (0:E) 1) F ∧
    F ≠ closedBall (0:E) 1 ∧ HasMFaceStructure F}
  have hDf : D.Finite := (finite_unit_faces_of_medians hmed).subset (fun F hF => hF.1)
  obtain ⟨G,hG,hmax⟩ := Set.exists_max_image D faceRank hDf ⟨F,hF,hp,hmF⟩
  exact ⟨G,hG.1,hG.2.1,hG.2.2,fun L hL hpL hmL => hmax L ⟨hL,hpL,hmL⟩,
    by have := hmax F ⟨hF,hp,hmF⟩; omega⟩

lemma proper_split_of_no_maximal_mface (hmed : HasMetricMedians E)
    (hdual : HasMetricMedians (E →L[ℝ] ℝ)) (hdim : 2 ≤ Module.finrank ℝ E)
    (hn : ∀ K, IsMaximalProperFace (closedBall (0:E) 1) K → ¬ HasMFaceStructure K) :
    ∃ K F G, IsMaximalProperFace (closedBall (0:E) 1) K ∧
      IsSplitPair K F G ∧ F.Nonempty ∧ G.Nonempty := by
  obtain ⟨F,hF,hp,hm,hmax,hr⟩ := exists_maximal_mface hmed hdim
  obtain ⟨A,B,hA,hB,hAn,hBn,hAB⟩ := hm
  have hFn := hAn.mono hA.1.subset
  obtain ⟨f,hf,hfF⟩ := proper_face_support hmed hF hFn hp
  let K := {x ∈ closedBall (0:E) 1 | f x=1}
  have hK : IsMaximalProperFace (closedBall (0:E) 1) K := dual_vertex_maximal_support hmed hf
  have hFK : F ⊆ K := fun x hx => ⟨hF.subset hx,hfF x hx⟩
  have hne : F ≠ K := by
    intro he
    exact hn K hK (he ▸ ⟨A,B,hA,hB,hAn,hBn,hAB⟩)
  obtain ⟨G,p⟩ := maximal_mface_split hmed hdual hK (hF.mono hK.1.subset hFK)
    ⟨A,B,hA,hB,hAn,hBn,hAB⟩ hmax
  refine ⟨K,F,G,hK,p,hFn,?_⟩
  by_contra hg
  have heG := not_nonempty_iff_eq_empty.mp hg
  have he := p.1.2.2.2
  rw [heG,union_empty,hF.1.convexHull_eq] at he
  exact hne he.symm

end SymmetricMahler

end

end OAI
