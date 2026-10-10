import OAI.Analysis.Mahler.Faces
import Mathlib.Analysis.Normed.Module.DoubleDual

namespace OAI

noncomputable section

open Set Metric
namespace SymmetricMahler

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [Nontrivial E]

lemma IsParallelPair.square {K F G : Set E} (h : IsParallelPair K F G)
    {x y a b : E} (hx : x ∈ F) (hy : y ∈ G)
    (ha : a ∈ K.extremePoints ℝ) (hb : b ∈ K.extremePoints ℝ)
    (he : x+a=y+b) : a ∈ G ∧ b ∈ F := by
  constructor
  · apply (h.not_mem_iff ha).mp
    intro hh
    have hyF := (face_mem_of_parallelogram h.1 hx hh (h.2.1.subset hy) hb.1 he).1
    exact disjoint_left.mp h.2.2.1 hyF hy
  · apply (h.symm.not_mem_iff hb).mp
    intro hh
    have hxG := (face_mem_of_parallelogram h.2.1 hy hh (h.1.subset hx) ha.1 he.symm).1
    exact disjoint_left.mp h.2.2.1 hx hxG

lemma facial_diamond (hmed : HasMetricMedians E)
    {M H N N' P P' R R' Q Q' : Set E}
    (hM : IsFace (closedBall (0:E) 1) M) (hp : M ≠ closedBall (0:E) 1)
    (hN : IsMaximalProperFace M N) (hP : IsMaximalProperFace M P)
    (hR : IsMaximalProperFace M R)
    (pN : IsParallelPair M N N') (pP : IsParallelPair M P P')
    (pR : IsParallelPair M R R') (pQ : IsParallelPair M Q Q')
    (hH : H = N ∩ R') (hHP : H ⊆ P) (hHQ : H ⊆ Q)
    (hPRQ : P ∩ R ⊆ Q)
    {x y u v : E}
    (hx : x ∈ M.extremePoints ℝ) (hy : y ∈ M.extremePoints ℝ)
    (_ : u ∈ M.extremePoints ℝ) (hv : v ∈ M.extremePoints ℝ)
    (hxH : x ∈ H)
    (hyD : y ∈ R ∩ N' ∩ P' ∩ Q')
    (huD : u ∈ N ∩ P' ∩ Q)
    (hvD : v ∈ N' ∩ P ∩ Q')
    (he : x+y=u+v) :
    HasMFaceStructure (faceHull (closedBall (0:E) 1) ({y} ∪ H)) := by
  let T := faceHull (closedBall (0:E) 1) ({y} ∪ H)
  have hHb : IsFace (closedBall (0:E) 1) H := hH ▸ hM.trans (pN.1.inter pR.2.1)
  have hHM : H ⊆ M := fun z hz => pN.1.subset ((hH ▸ hz).1)
  have hbase : {y} ∪ H ⊆ M := union_subset (singleton_subset_iff.mpr hy.1) hHM
  have hT : IsFace (closedBall (0:E) 1) T :=
    isFace_faceHull (convex_closedBall _ _) (hbase.trans hM.subset)
  have hTM : T ⊆ M := faceHull_min hM hbase
  have hTc : IsFace M T := hT.mono hM.subset hTM
  have hTp := proper_unit_face_subface_ne hM hp hTM
  have hHT : H ⊆ T := fun _ hz => subset_faceHull (Or.inr hz)
  have hyT : y ∈ T := subset_faceHull (Or.inl (mem_singleton _))
  have hxT := hHT hxH
  have hxNR := hH ▸ hxH
  have hNn : N.Nonempty := ⟨x,hxNR.1⟩
  have hPn : P.Nonempty := ⟨x,hHP hxH⟩
  have hRn : R.Nonempty := ⟨y,hyD.1.1.1⟩
  let A := N ∩ P' ∩ Q
  let B := N' ∩ P ∩ Q'
  have hA : IsFace M A := (pN.1.inter pP.2.1).inter pQ.1
  have hB : IsFace M B := (pN.2.1.inter pP.1).inter pQ.2.1
  have hBR : B ⊆ R' := by
    apply pR.subset_of_disjoint hmed hM hB
    exact disjoint_left.mpr (fun z hz hzR =>
      disjoint_left.mp pQ.2.2.1 (hPRQ ⟨hz.1.2,hzR⟩) hz.2)
  have hRP : R ∩ N' ∩ Q' ⊆ P' := by
    apply pP.subset_of_disjoint hmed hM ((pR.1.inter pN.2.1).inter pQ.2.1)
    exact disjoint_left.mpr (fun z hz hzP =>
      disjoint_left.mp pQ.2.2.1 (hPRQ ⟨hzP,hz.1.1⟩) hz.2)
  have hvR : v ∈ R' := hBR hvD
  have hAs : A ⊆ T ∩ R := by
    apply (hM.trans hA).subset_of_vertices hmed (hT.1.inter pR.1.1)
    intro t ht
    have htM := hM.extreme_mem ht.1 (hA.subset ht.2)
    obtain ⟨a,ha,b,hb,hab⟩ := hP.exchange hmed hM pP hPn htM ht.2.1.2 hy hyD.1.2
    have haM := hM.extreme_mem ha.2 (pP.1.subset ha.1)
    have hbM := hM.extreme_mem hb.2 (pP.1.subset hb.1)
    have hNa := pN.square ht.2.1.1 hyD.1.1.2 haM hbM hab
    have hQa := pQ.square ht.2.2 hyD.2 haM hbM hab
    have haR := hBR ⟨⟨hNa.1,ha.1⟩,hQa.1⟩
    have hRb := pR.square hyD.1.1.1 haR hbM htM
      (by simpa [add_comm] using hab.symm)
    have hbH : b ∈ H := hH.symm ▸ ⟨hNa.2,hRb.1⟩
    have htT := (face_mem_of_parallelogram hT hyT (hHT hbH)
      ht.1.1 ha.2.1 hab.symm).1
    exact ⟨htT,hRb.2⟩
  have hBs : B ⊆ T := by
    apply (hM.trans hB).subset_of_vertices hmed hT.1
    intro t ht
    have htM := hM.extreme_mem ht.1 (hB.subset ht.2)
    obtain ⟨a,ha,b,hb,hab⟩ := hN.exchange hmed hM pN hNn htM ht.2.1.1 hy hyD.1.1.2
    have haM := hM.extreme_mem ha.2 (pN.1.subset ha.1)
    have hbM := hM.extreme_mem hb.2 (pN.1.subset hb.1)
    have hRb := pR.symm.square (hBR ht.2) hyD.1.1.1 haM hbM hab
    have hbH : b ∈ H := hH.symm ▸ ⟨hb.1,hRb.2⟩
    exact (face_mem_of_parallelogram hT hyT (hHT hbH) ht.1.1 ha.2.1 hab.symm).1
  let U := faceHull (closedBall (0:E) 1) (A ∪ B)
  have hU : IsFace (closedBall (0:E) 1) U := isFace_faceHull (convex_closedBall _ _)
    ((union_subset hA.subset hB.subset).trans hM.subset)
  have hAU : A ⊆ U := fun _ hz => subset_faceHull (Or.inl hz)
  have hBU : B ⊆ U := fun _ hz => subset_faceHull (Or.inr hz)
  have hHU : H ⊆ U := by
    apply hHb.subset_of_vertices hmed hU.1
    intro t ht
    have htM := hM.extreme_mem ht.1 (hHM ht.2)
    have htNR := hH ▸ ht.2
    obtain ⟨a,ha,b,hb,hab⟩ := hR.exchange hmed hM pR hRn htM htNR.2 hv hvR
    have haM := hM.extreme_mem ha.2 (pR.1.subset ha.1)
    have hbM := hM.extreme_mem hb.2 (pR.1.subset hb.1)
    have hNa := pN.square htNR.1 hvD.1.1 haM hbM hab
    have hQa := pQ.square (hHQ ht.2) hvD.2 haM hbM hab
    have haP := hRP ⟨⟨ha.1,hNa.1⟩,hQa.1⟩
    have hbP := (pP.symm.square haP hvD.1.2 htM hbM
      (by simpa [add_comm] using hab)).2
    have hbA : b ∈ A := ⟨⟨hNa.2,hbP⟩,hQa.2⟩
    exact (face_mem_of_parallelogram hU (hBU hvD) (hAU hbA) ht.1.1 ha.2.1 hab.symm).1
  have hyU : y ∈ U := (face_mem_of_parallelogram hU (hAU huD) (hBU hvD)
    (hM.subset hx.1) (hM.subset hy.1) he.symm).2
  have hTU : T ⊆ U := faceHull_min hU
    (union_subset (singleton_subset_iff.mpr hyU) hHU)
  let V := faceHull (closedBall (0:E) 1) ({x} ∪ (T ∩ R))
  have hV : IsFace (closedBall (0:E) 1) V := isFace_faceHull (convex_closedBall _ _)
    ((union_subset (singleton_subset_iff.mpr hxT) inter_subset_left).trans hT.subset)
  have hxV : x ∈ V := subset_faceHull (Or.inl (mem_singleton _))
  have hTRV : T ∩ R ⊆ V := fun _ hz => subset_faceHull (Or.inr hz)
  have hAV : A ⊆ V := hAs.trans hTRV
  have hBV : B ⊆ V := by
    apply (hM.trans hB).subset_of_vertices hmed hV.1
    intro t ht
    have htM := hM.extreme_mem ht.1 (hB.subset ht.2)
    obtain ⟨a,ha,b,hb,hab⟩ := hR.exchange hmed hM pR hRn htM (hBR ht.2) hx hxNR.2
    have haM := hM.extreme_mem ha.2 (pR.1.subset ha.1)
    have hbM := hM.extreme_mem hb.2 (pR.1.subset hb.1)
    have hNa := pN.symm.square ht.2.1.1 hxNR.1 haM hbM hab
    have hQa := pQ.symm.square ht.2.2 (hHQ hxH) haM hbM hab
    have hbP := hRP ⟨⟨hb.1,hNa.2⟩,hQa.2⟩
    have haP := (pP.symm.square hbP ht.2.1.2 hx haM
      (by simpa [add_comm] using hab.symm)).2
    have haA : a ∈ A := ⟨⟨hNa.1,haP⟩,hQa.1⟩
    have hbT := (face_mem_of_parallelogram hT (hBs ht.2) (hAs haA).1
      (hM.subset hx.1) hb.2.1 hab).2
    exact (face_mem_of_parallelogram hV hxV (hTRV ⟨hbT,hb.1⟩)
      ht.1.1 ha.2.1 hab.symm).1
  have hUV : U ⊆ V := faceHull_min hV (union_subset hAV hBV)
  have hVT : V ⊆ T := faceHull_min hT
    (union_subset (singleton_subset_iff.mpr hxT) inter_subset_left)
  have hTV : T = V := subset_antisymm (hTU.trans hUV) hVT
  let W := faceHull (closedBall (0:E) 1) ({y} ∪ (T ∩ R'))
  have hTW : T = W := by
    apply subset_antisymm
    · exact faceHull_mono (union_subset_union Subset.rfl
        (fun z hz => ⟨hHT hz,(hH ▸ hz).2⟩))
    · exact faceHull_min hT
        (union_subset (singleton_subset_iff.mpr hyT) inter_subset_left)
  have pT := pR.restrict hmed hM hTc
  have hAn : (T ∩ R).Nonempty := ⟨y,hyT,hyD.1.1.1⟩
  have hBn : (T ∩ R').Nonempty := ⟨x,hxT,hxNR.2⟩
  have hrA := parallel_faceHull_rank hmed hT hTp pT hAn
    (hT.extreme_mem (hM.2.extremePoints_subset_extremePoints hx) hxT) ⟨hxT,hxNR.2⟩
  have hrB := parallel_faceHull_rank hmed hT hTp pT.symm hBn
    (hT.extreme_mem (hM.2.extremePoints_subset_extremePoints hy) hyT) ⟨hyT,hyD.1.1.1⟩
  change faceRank V = faceRank (T ∩ R) + 1 at hrA
  change faceRank W = faceRank (T ∩ R') + 1 at hrB
  rw [← hTV] at hrA
  rw [← hTW] at hrB
  exact ⟨T ∩ R,T ∩ R',rank_succ_maximal hmed hT hTp pT.1 (pT.left_ne hBn) hrA,
    rank_succ_maximal hmed hT hTp pT.2.1 (pT.symm.left_ne hAn) hrB,
    hAn,hBn,pT.2.2.1⟩

def HasMaximalMRank (F : Set E) : Prop :=
  ∀ L, IsFace (closedBall (0:E) 1) L → L ≠ closedBall (0:E) 1 →
    HasMFaceStructure L → faceRank L ≤ faceRank F

lemma maximal_mface_child_parallel (hmed : HasMetricMedians E) {M F F' G H : Set E}
    (hM : IsFace (closedBall (0:E) 1) M) (hp : M ≠ closedBall (0:E) 1)
    (hpair : IsParallelPair M F F') (hmax : HasMaximalMRank F)
    (hG : IsMaximalProperFace F G) (hH : IsMaximalProperFace F H)
    (hGn : G.Nonempty) (hHn : H.Nonempty) (hGH : Disjoint G H) :
    IsParallelFace M H := by
  have hFball := hM.trans hpair.1
  have hFp := proper_unit_face_subface_ne hM hp hpair.1.subset
  have hGp := proper_unit_face_subface_ne hM hp (hG.1.subset.trans hpair.1.subset)
  have hHp := proper_unit_face_subface_ne hM hp (hH.1.subset.trans hpair.1.subset)
  have hFnh : F.Nonempty := hGn.mono hG.1.subset
  have hpairGH := maximal_pair_of_disjoint hmed hFball hG hH hGn hHn hGH
  obtain ⟨x,hx,hxH⟩ := (hFball.trans hH.1).exists_vertex hmed hHn
  have hxF := hH.1.subset hxH
  have hxM := hpair.1.subset hxF
  have hxG : x ∉ G := fun hh => disjoint_left.mp hGH hh hxH
  obtain ⟨S,hS,hGS,hxS⟩ := extend_face_avoiding_vertex hmed hM hp
    (hpair.1.trans hG.1) hGn (hM.extreme_mem hx hxM) hxG
  obtain ⟨S',hSS⟩ := maximal_proper_parallel hmed hM hS (hGn.mono hGS)
  have hxS' := (hSS.not_mem_iff (hM.extreme_mem hx hxM)).mp hxS
  have hFS : F ∩ S = G := by
    apply hG.2.2 _
    · exact (hpair.1.inter hS.1).mono hpair.1.subset inter_subset_left
    · exact fun _ hz => ⟨hG.1.subset hz,hGS hz⟩
    · intro he
      exact hxS ((he.symm ▸ hxF).2)
  have hFS' : F ∩ S' = H := by
    have hh := hSS.restrict hmed hM hpair.1
    rw [hFS] at hh
    exact hh.complement_unique hmed hFball hpairGH
  have hsub : S' ⊆ F := by
    by_contra hn
    obtain ⟨z,hz,hzS',hzF⟩ := (hM.trans hSS.2.1).exists_vertex_outside hmed hFball.1 hn
    have hzM := hSS.2.1.subset hzS'
    have hzF' := (hpair.not_mem_iff (hM.extreme_mem hz hzM)).mp hzF
    obtain ⟨a,ha,b,hb,he⟩ := hS.exchange hmed hM hSS (hGn.mono hGS)
      (hM.extreme_mem hx hxM) hxS' (hM.extreme_mem hz hzM) hzS'
    have haM := hS.1.subset ha.1
    have hbM := hS.1.subset hb.1
    have hbF : b ∈ F := by
      rcases hpair.vertex_mem (hM.extreme_mem hb.2 hbM) with hh | hh
      · exact hh
      · have hxF' := (face_mem_of_parallelogram hpair.2.1 hzF' hh hxM haM he.symm).1
        exact False.elim (disjoint_left.mp hpair.2.2.1 hxF hxF')
    have hbG : b ∈ G := hFS ▸ ⟨hbF,hb.1⟩
    have haF : a ∉ F := by
      intro hh
      have hzF' := (face_mem_of_parallelogram hpair.1 hxF hh hzM hbM he).1
      exact hzF hzF'
    let L := faceHull (closedBall (0:E) 1) ({z} ∪ F)
    have hbase : {z} ∪ F ⊆ M := union_subset (singleton_subset_iff.mpr hzM) hpair.1.subset
    have hL : IsFace (closedBall (0:E) 1) L :=
      isFace_faceHull (convex_closedBall _ _) (hbase.trans hM.subset)
    have hLM : L ⊆ M := faceHull_min hM hbase
    have hFL : F ⊆ L := fun _ hu => subset_faceHull (Or.inr hu)
    have hzL : z ∈ L := subset_faceHull (Or.inl (mem_singleton z))
    have hLp := proper_unit_face_subface_ne hM hp hLM
    have haL : a ∈ L := (face_mem_of_parallelogram hL hzL (hFL hbF)
      (hM.subset hxM) ha.2.1 he.symm).2
    have hLc : IsFace M L := hL.mono hM.subset hLM
    have hpL := hSS.restrict hmed hM hLc
    have hGA : G ⊆ L ∩ S := fun _ hu => ⟨hFL (hG.1.subset hu),hGS hu⟩
    have hHB : H ⊆ L ∩ S' := fun _ hu =>
      ⟨hFL (hH.1.subset hu),(hFS'.symm ▸ hu).2⟩
    have haA : a ∈ L ∩ S := ⟨haL,ha.1⟩
    have hzB : z ∈ L ∩ S' := ⟨hzL,hzS'⟩
    have hAn : (L ∩ S).Nonempty := hGn.mono hGA
    have hBn : (L ∩ S').Nonempty := hHn.mono hHB
    have hAp : L ∩ S ≠ L := hpL.left_ne hBn
    have hBp : L ∩ S' ≠ L := hpL.symm.left_ne hAn
    have hGAr := faceRank_lt hmed (hL.trans hpL.1)
      (proper_unit_face_subface_ne hL hLp hpL.1.subset)
      ((hFball.trans hG.1).mono (fun _ hz => hL.subset (hpL.1.subset hz)) hGA)
      (by intro hh; exact haF (hG.1.subset (hh.symm ▸ haA)))
    have hHBr := faceRank_lt hmed (hL.trans hpL.2.1)
      (proper_unit_face_subface_ne hL hLp hpL.2.1.subset)
      ((hFball.trans hH.1).mono (fun _ hz => hL.subset (hpL.2.1.subset hz)) hHB)
      (by intro hh; exact hzF (hH.1.subset (hh.symm ▸ hzB)))
    have hAr := faceRank_lt hmed hL hLp hpL.1 hAp
    have hBr := faceRank_lt hmed hL hLp hpL.2.1 hBp
    have hrG := maximal_proper_rank hmed hFball hFp hG hGn
    have hrH := maximal_proper_rank hmed hFball hFp hH hHn
    have hrL := parallel_faceHull_rank hmed hM hp hpair hFnh
      (hM.extreme_mem hz hzM) hzF'
    change faceRank L = faceRank F + 1 at hrL
    have hAm := rank_succ_maximal hmed hL hLp hpL.1 hAp (by omega)
    have hBm := rank_succ_maximal hmed hL hLp hpL.2.1 hBp (by omega)
    have hmL : HasMFaceStructure L :=
      ⟨L ∩ S,L ∩ S',hAm,hBm,hAn,hBn,hpL.2.2.1⟩
    have hbound := hmax L hL hLp hmL
    omega
  have he : S' = H := (inter_eq_right.mpr hsub).symm.trans hFS'
  exact ⟨S,he ▸ hSS.symm⟩

theorem maximal_mface_children_parallel (hmed : HasMetricMedians E) {M F F' G H : Set E}
    (hM : IsFace (closedBall (0:E) 1) M) (hp : M ≠ closedBall (0:E) 1)
    (hpair : IsParallelPair M F F') (hmax : HasMaximalMRank F)
    (hG : IsMaximalProperFace F G) (hH : IsMaximalProperFace F H)
    (hGn : G.Nonempty) (hHn : H.Nonempty) (hGH : Disjoint G H) :
    IsParallelFace M G ∧ IsParallelFace M H :=
  ⟨maximal_mface_child_parallel hmed hM hp hpair hmax hH hG hHn hGn hGH.symm,
    maximal_mface_child_parallel hmed hM hp hpair hmax hG hH hGn hHn hGH⟩

end

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [inst504 : FiniteDimensional ℝ E] [inst505 : Nontrivial E]

omit inst504 inst505 in
lemma IsParallelFace.refl [FiniteDimensional ℝ E] [Nontrivial E] {K : Set E} (hK : Convex ℝ K) : IsParallelFace K K :=
  ⟨∅,IsFace.refl hK,IsFace.empty K,by simp,by simp [hK.convexHull_eq]⟩

lemma IsParallelPair.square_sides {K F G : Set E} (h : IsParallelPair K F G)
    {x y u v : E} (hx : x ∈ F) (hy : y ∈ G)
    (hu : u ∈ K.extremePoints ℝ) (hv : v ∈ K.extremePoints ℝ)
    (he : x+y=u+v) : (u ∈ F ∧ v ∈ G) ∨ (v ∈ F ∧ u ∈ G) := by
  rcases h.vertex_mem hu with hh | hh
  · left
    refine ⟨hh,(h.not_mem_iff hv).mp ?_⟩
    intro hvF
    exact disjoint_left.mp h.2.2.1
      (face_mem_of_parallelogram h.1 hh hvF (h.1.subset hx) (h.2.1.subset hy) he.symm).2 hy
  · right
    refine ⟨(h.symm.not_mem_iff hv).mp ?_,hh⟩
    intro hvG
    exact disjoint_left.mp h.2.2.1 hx
      (face_mem_of_parallelogram h.2.1 hh hvG (h.1.subset hx) (h.2.1.subset hy) he.symm).1

theorem maximal_mface_parallel (hmed : HasMetricMedians E) {K F : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (hp : K ≠ closedBall (0:E) 1)
    (hF : IsFace K F) (hmF : HasMFaceStructure F) (hmax : HasMaximalMRank F) :
    IsParallelFace K F := by
  classical
  by_contra hn
  have hFb := hK.trans hF
  have hFp := proper_unit_face_subface_ne hK hp hF.subset
  have hFn : F.Nonempty := by
    obtain ⟨G,H,hG,-,hGn,-⟩ := hmF
    exact hGn.mono hG.1.subset
  let D : Set (Set E) := {M | IsFace (closedBall (0:E) 1) M ∧ M ⊆ K ∧ F ⊆ M ∧
    ¬ IsParallelFace M F}
  have hDf : D.Finite := (finite_unit_faces_of_medians hmed).subset (fun _ h => h.1)
  obtain ⟨M,hmin⟩ := hDf.exists_minimal ⟨K,hK,Subset.rfl,hF.subset,hn⟩
  obtain ⟨hM,hMK,hFM,hnM⟩ := hmin.1
  have hMp := proper_unit_face_subface_ne hK hp hMK
  have hFc : IsFace M F := hFb.mono hM.subset hFM
  have hFMne : F ≠ M := by
    intro hh
    rw [hh] at hnM
    exact hnM (IsParallelFace.refl hM.1)
  have hsmall : ∀ N, IsFace M N → F ⊆ N → N ≠ M → IsParallelFace N F := by
    intro N hN hFN hnp
    by_contra hnN
    have hND : N ∈ D := ⟨hM.trans hN,hN.subset.trans hMK,hFN,hnN⟩
    exact hnp (subset_antisymm hN.subset (hmin.2 hND hN.subset))
  obtain ⟨x,hx,y,hy,u0,hu0,v0,hv0,he0⟩ := nonparallel_vertex_parallelogram hmed hM hFc hFn hFMne hnM
  have hxM := hM.extreme_mem hx.2 (hFM hx.1)
  have hyM := hM.extreme_mem hy.2 hy.1.1
  have hu0M := hM.extreme_mem hu0.2 hu0.1.1
  have hv0M := hM.extreme_mem hv0.2 hv0.1.1
  have hjoin : faceHull (closedBall (0:E) 1) ({y} ∪ F) = M := by
    let J := faceHull (closedBall (0:E) 1) ({y} ∪ F)
    have hbase : {y} ∪ F ⊆ M := union_subset (singleton_subset_iff.mpr hy.1.1) hFM
    have hJ : IsFace (closedBall (0:E) 1) J :=
      isFace_faceHull (convex_closedBall _ _) (hbase.trans hM.subset)
    have hJM : J ⊆ M := faceHull_min hM hbase
    have hFJ : F ⊆ J := fun _ hz => subset_faceHull (Or.inr hz)
    have hyJ : y ∈ J := subset_faceHull (Or.inl (mem_singleton _))
    have huv := face_mem_of_parallelogram hJ (hFJ hx.1) hyJ hu0.2.1 hv0.2.1 he0
    have hnJ := parallelogram_not_parallel hx.1 (hFJ hx.1) hyJ
      (hJ.extreme_mem hu0.2 huv.1) (hJ.extreme_mem hv0.2 huv.2) hu0.1.2 hv0.1.2 he0
    exact subset_antisymm hJM (hmin.2 ⟨hJ,hJM.trans hMK,hFJ,hnJ⟩ hJM)
  obtain ⟨N,hN,hFN,hyN⟩ := extend_face_avoiding_vertex hmed hM hMp hFc hFn hyM hy.1.2
  obtain ⟨N',pN⟩ := maximal_proper_parallel hmed hM hN (hFn.mono hFN)
  have hyN' := (pN.not_mem_iff hyM).mp hyN
  obtain ⟨u,hu,v,hv,he,huN,hvN'⟩ :
      ∃ u ∈ (M \ F) ∩ (closedBall (0:E) 1).extremePoints ℝ,
        ∃ v ∈ (M \ F) ∩ (closedBall (0:E) 1).extremePoints ℝ,
          x+y=u+v ∧ u ∈ N ∧ v ∈ N' := by
    rcases pN.square_sides (hFN hx.1) hyN' hu0M hv0M he0 with hh | hh
    · exact ⟨u0,hu0,v0,hv0,he0,hh.1,hh.2⟩
    · exact ⟨v0,hv0,u0,hu0,by simpa [add_comm] using he0,hh.1,hh.2⟩
  have huM := hM.extreme_mem hu.2 hu.1.1
  have hvM := hM.extreme_mem hv.2 hv.1.1
  obtain ⟨P,hP,hFP,huP⟩ := extend_face_avoiding_vertex hmed hM hMp hFc hFn huM hu.1.2
  obtain ⟨P',pP⟩ := maximal_proper_parallel hmed hM hP (hFn.mono hFP)
  have huP' := (pP.not_mem_iff huM).mp huP
  have hpys := pP.square (hFP hx.1) huP' hyM hvM he
  have hyP' : y ∈ P' := hpys.1
  have hvP : v ∈ P := hpys.2
  obtain ⟨G,H,hG,hH,hGn,hHn,hGH,hxH⟩ :
      ∃ G H, IsMaximalProperFace F G ∧ IsMaximalProperFace F H ∧
        G.Nonempty ∧ H.Nonempty ∧ Disjoint G H ∧ x ∈ H := by
    obtain ⟨G,H,hG,hH,hGn,hHn,hGH⟩ := hmF
    have pGH := maximal_pair_of_disjoint hmed hFb hG hH hGn hHn hGH
    rcases pGH.vertex_mem (hFb.extreme_mem hx.2 hx.1) with hh | hh
    · exact ⟨H,G,hH,hG,hHn,hGn,hGH.symm,hh⟩
    · exact ⟨G,H,hG,hH,hGn,hHn,hGH,hh⟩
  have pGH := maximal_pair_of_disjoint hmed hFb hG hH hGn hHn hGH
  obtain ⟨O,pFO⟩ := hsmall P hP.1 hFP hP.2.1
  obtain ⟨C,pFC⟩ := hsmall N hN.1 hFN hN.2.1
  obtain ⟨S,pHS⟩ := (maximal_mface_children_parallel hmed (hM.trans hN.1)
    (proper_unit_face_subface_ne hM hMp hN.1.subset) pFC hmax hG hH hGn hHn hGH).2
  obtain ⟨I,pHI⟩ := (maximal_mface_children_parallel hmed (hM.trans hP.1)
    (proper_unit_face_subface_ne hM hMp hP.1.subset) pFO hmax hG hH hGn hHn hGH).2
  have hGS : G ⊆ S := pHS.subset_of_disjoint hmed (hM.trans hN.1)
    ((hFb.trans hG.1).mono (hM.trans hN.1).subset (hG.1.subset.trans hFN)) hGH
  have hxS : x ∉ S := fun hh => disjoint_left.mp pHS.2.2.1 hxH hh
  obtain ⟨R,hR,hSR,hxR⟩ := extend_face_avoiding_vertex hmed hM hMp
    (hN.1.trans pHS.2.1) (hGn.mono hGS) hxM hxS
  obtain ⟨R',pR⟩ := maximal_proper_parallel hmed hM hR (hGn.mono (hGS.trans hSR))
  have hxR' := (pR.not_mem_iff hxM).mp hxR
  have hFR : F ∩ R = G := hG.2.2 _
    ((hFc.inter hR.1).mono hFM inter_subset_left)
    (fun _ hz => ⟨hG.1.subset hz,hSR (hGS hz)⟩)
    (by intro hh; exact hxR ((hh.symm ▸ hx.1).2))
  have hNR : N ∩ R = S := by
    apply subset_antisymm
    · apply pHS.subset_of_disjoint hmed (hM.trans hN.1)
        ((hN.1.inter hR.1).mono hN.1.subset inter_subset_left)
      apply disjoint_left.mpr
      intro z hz hzH
      exact disjoint_left.mp hGH (hFR ▸ ⟨hH.1.subset hzH,hz.2⟩) hzH
    · exact fun z hz => ⟨pHS.2.1.subset hz,hSR hz⟩
  have hNR' : N ∩ R' = H := by
    have hh := pR.restrict hmed hM hN.1
    rw [hNR] at hh
    exact hh.complement_unique hmed (hM.trans hN.1) pHS.symm
  have huS : u ∈ S := (pHS.not_mem_iff ((hM.trans hN.1).extreme_mem hu.2 huN)).mp
    (fun hh => hu.1.2 (hH.1.subset hh))
  have huR := hSR huS
  have hrys := pR.symm.square hxR' huR hyM hvM he
  have hyR := hrys.1
  have hvR' := hrys.2
  have hHdis : Disjoint H (P ∩ R) := disjoint_left.mpr (fun z hz hzPR =>
    disjoint_left.mp pR.2.2.1 hzPR.2 ((hNR'.symm ▸ hz).2))
  have pPR := pR.restrict hmed hM hP.1
  have hPRn : (P ∩ R).Nonempty := hGn.mono
    (fun z hz => ⟨hFP (hG.1.subset hz),hSR (hGS hz)⟩)
  let J := convexHull ℝ (H ∪ (P ∩ R))
  have hJc : IsFace P J := parallel_disjoint_union_face hmed (hM.trans hP.1)
    pHI pPR hHn hPRn hHdis
  have hJ := (hM.trans hP.1).trans hJc
  have hFJ : F ⊆ J := by
    rw [pGH.2.2.2]
    exact convexHull_mono (union_subset
      (fun z hz => Or.inr ⟨hFP (hG.1.subset hz),hSR (hGS hz)⟩)
      (fun _ hz => Or.inl hz))
  let Z := O ∩ R'
  have hZ : IsFace (closedBall (0:E) 1) Z :=
    ((hM.trans hP.1).trans pFO.2.1).inter (hM.trans pR.2.1)
  have hvO := (pFO.not_mem_iff ((hM.trans hP.1).extreme_mem hv.2 hvP)).mp hv.1.2
  have hvZ : v ∈ Z := ⟨hvO,hvR'⟩
  have hJZ : Disjoint J Z := by
    by_contra hd
    have hn : (J ∩ Z).Nonempty := not_disjoint_iff.mp hd
    obtain ⟨z,hz,hzJ,hzZ⟩ := (hJ.inter hZ).exists_vertex hmed hn
    have hzV := hJ.extreme_mem hz hzJ
    change z ∈ (convexHull ℝ (H ∪ (P ∩ R))).extremePoints ℝ at hzV
    rcases extremePoints_convexHull_subset hzV with hh | hh
    · exact disjoint_left.mp pFO.2.2.1 (hH.1.subset hh) hzZ.1
    · exact disjoint_left.mp pR.2.2.1 hh.2 hzZ.2
  obtain ⟨q,hq,hqJ,hqZ⟩ := disjoint_faces_dual_vertex hmed hJ hZ
    (hFn.mono hFJ) ⟨v,hvZ⟩ hJZ
  let Q := {z ∈ M | q z = 1}
  let Q' := {z ∈ M | q z = -1}
  have pQ : IsParallelPair M Q Q' := parallelPair_of_dual_vertex hmed hM hq
  have hFQ : F ⊆ Q := fun z hz => ⟨hFM hz,hqJ z (hFJ hz)⟩
  have hPRQ : P ∩ R ⊆ Q := fun z hz =>
    ⟨hP.1.subset hz.1,hqJ z (subset_convexHull ℝ _ (Or.inr hz))⟩
  have hvQ' : v ∈ Q' := ⟨hv.1.1,hqZ v hvZ⟩
  have hqys := pQ.square (hFQ hx.1) hvQ' hyM huM (by simpa [add_comm] using he)
  have hyQ' := hqys.1
  have huQ := hqys.2
  let T := faceHull (closedBall (0:E) 1) ({y} ∪ H)
  have hmT : HasMFaceStructure T := facial_diamond hmed hM hMp hN hP hR pN pP pR pQ
    hNR'.symm (hH.1.subset.trans hFP) (hH.1.subset.trans hFQ) hPRQ
    hxM hyM huM hvM hxH ⟨⟨⟨hyR,hyN'⟩,hyP'⟩,hyQ'⟩
    ⟨⟨huN,huP'⟩,huQ⟩ ⟨⟨hvN',hvP⟩,hvQ'⟩ he
  have hbaseT : {y} ∪ H ⊆ M := union_subset (singleton_subset_iff.mpr hy.1.1)
    (hH.1.subset.trans hFM)
  have hT : IsFace (closedBall (0:E) 1) T :=
    isFace_faceHull (convex_closedBall _ _) (hbaseT.trans hM.subset)
  have hTM : T ⊆ M := faceHull_min hM hbaseT
  have hTp := proper_unit_face_subface_ne hM hMp hTM
  have hHT : H ⊆ T := fun _ hz => subset_faceHull (Or.inr hz)
  have hyT : y ∈ T := subset_faceHull (Or.inl (mem_singleton _))
  have huT := (face_mem_of_parallelogram hT (hHT hxH) hyT hu.2.1 hv.2.1 he).1
  have hTN : IsFace (closedBall (0:E) 1) (T ∩ N) := hT.inter (hM.trans hN.1)
  have hHTN : H ⊆ T ∩ N := fun z hz => ⟨hHT hz,hFN (hH.1.subset hz)⟩
  have hr1 := faceRank_lt hmed hTN
    (proper_unit_face_subface_ne hT hTp inter_subset_left)
    ((hFb.trans hH.1).mono hTN.subset hHTN)
    (by intro hh; exact hu.1.2 (hH.1.subset (hh.symm ▸ ⟨huT,huN⟩)))
  have hr2 := faceRank_lt hmed hT hTp (hTN.mono hT.subset inter_subset_left)
    (by intro hh; exact hyN ((hh.symm ▸ hyT).2))
  have hrH := maximal_proper_rank hmed hFb hFp hH hHn
  have hrT := hmax T hT hTp hmT
  omega

end

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [inst508 : FiniteDimensional ℝ E] [inst509 : Nontrivial E]

lemma IsFace.exists_generator (hmed : HasMetricMedians E) {F : Set E}
    (hF : IsFace (closedBall (0:E) 1) F) (hn : F.Nonempty) :
    ∃ x ∈ F, faceHull (closedBall (0:E) 1) {x} = F := by
  classical
  let D : Set (Set E) := {G | ∃ x ∈ F, G = faceHull (closedBall (0:E) 1) {x}}
  have hf : D.Finite := (finite_unit_faces_of_medians hmed).subset (by
    rintro G ⟨x,hx,rfl⟩
    exact isFace_faceHull (convex_closedBall _ _) (singleton_subset_iff.mpr (hF.subset hx)))
  obtain ⟨x0,hx0⟩ := hn
  obtain ⟨G,hmax⟩ := hf.exists_maximal ⟨_,x0,hx0,rfl⟩
  obtain ⟨x,hx,rfl⟩ := hmax.1
  refine ⟨x,hx,subset_antisymm (faceHull_min hF (singleton_subset_iff.mpr hx)) ?_⟩
  intro y hy
  let z := (1/2:ℝ) • x+(1/2:ℝ) • y
  have hz : z ∈ F := hF.1 hx hy (by norm_num) (by norm_num) (by norm_num)
  have hZ := isFace_faceHull (convex_closedBall (0:E) 1)
    (singleton_subset_iff.mpr (hF.subset hz))
  have hseg : z ∈ openSegment ℝ x y := ⟨1/2,1/2,by norm_num,by norm_num,by norm_num,rfl⟩
  have hzZ : z ∈ faceHull (closedBall (0:E) 1) {z} := subset_faceHull (mem_singleton z)
  have hxZ := hZ.2.left_mem_of_mem_openSegment (hF.subset hx) (hF.subset hy) hzZ hseg
  have hyZ := hZ.2.right_mem_of_mem_openSegment (hF.subset hx) (hF.subset hy) hzZ hseg
  exact hmax.2 ⟨z,hz,rfl⟩ (faceHull_min hZ (singleton_subset_iff.mpr hxZ)) hyZ

omit inst508 inst509 in
lemma faceHull_midpoint_eq [FiniteDimensional ℝ E] [Nontrivial E] {K : Set E} (hK : Convex ℝ K) {x y : E}
    (hx : x ∈ K) (hy : y ∈ K) :
    faceHull K {(1/2:ℝ) • x+(1/2:ℝ) • y} = faceHull K ({x} ∪ {y}) := by
  have hJ := isFace_faceHull hK (union_subset (singleton_subset_iff.mpr hx) (singleton_subset_iff.mpr hy))
  have hm := hK hx hy (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num) (by norm_num)
  have hL := isFace_faceHull hK (singleton_subset_iff.mpr hm)
  have hxJ : x ∈ faceHull K ({x} ∪ {y}) := subset_faceHull (Or.inl (mem_singleton x))
  have hyJ : y ∈ faceHull K ({x} ∪ {y}) := subset_faceHull (Or.inr (mem_singleton y))
  have hmL : (1/2:ℝ) • x+(1/2:ℝ) • y ∈ faceHull K {(1/2:ℝ) • x+(1/2:ℝ) • y} :=
    subset_faceHull (mem_singleton _)
  have hs : (1/2:ℝ) • x+(1/2:ℝ) • y ∈ openSegment ℝ x y :=
    ⟨1/2,1/2,by norm_num,by norm_num,by norm_num,rfl⟩
  exact subset_antisymm (faceHull_min hJ (singleton_subset_iff.mpr
    (hJ.1 hxJ hyJ (by norm_num) (by norm_num) (by norm_num))))
    (faceHull_min hL (union_subset
      (singleton_subset_iff.mpr (hL.2.left_mem_of_mem_openSegment hx hy hmL hs))
      (singleton_subset_iff.mpr (hL.2.right_mem_of_mem_openSegment hx hy hmL hs))))

lemma IsFace.exposed_generator (hmed : HasMetricMedians E) {F : Set E}
    (hF : IsFace (closedBall (0:E) 1) F) (hn : F.Nonempty)
    (hp : F ≠ closedBall (0:E) 1) :
    ∃ f : E →L[ℝ] ℝ, ‖f‖ ≤ 1 ∧ F = {x ∈ closedBall (0:E) 1 | f x = 1} := by
  classical
  let V := (closedBall (0:E) 1).extremePoints ℝ \ F
  have hVf : V.Finite := (finite_extreme_unit_of_medians hmed).subset sdiff_subset
  have hVn : V.Nonempty := by
    obtain ⟨x,hx,hxb,hxf⟩ := (IsFace.refl (convex_closedBall (0:E) 1)).exists_vertex_outside hmed hF.1
      (by intro hs; exact hp (subset_antisymm hF.subset hs))
    exact ⟨x,hx,hxf⟩
  have hsep : ∀ x : V, ∃ f ∈ (closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints ℝ,
      (∀ y ∈ F, f y = 1) ∧ f x = -1 := fun x => face_vertex_dual_separation hmed hF hn x.2.1 x.2.2
  choose f hf hfF hfx using hsep
  let : Fintype V := hVf.fintype
  let : Nonempty V := hVn.to_subtype
  let c : ℝ := Fintype.card V
  have hc : 0 < c := by
    change 0 < (Fintype.card V : ℝ)
    exact_mod_cast (Fintype.card_pos (α := V))
  let g : E →L[ℝ] ℝ := c⁻¹ • ∑ x : V, f x
  have hg : ‖g‖ ≤ 1 := by
    calc
      ‖g‖ = c⁻¹ * ‖∑ x : V, f x‖ := by simp [g,norm_smul,abs_of_pos hc]
      _ ≤ c⁻¹ * ∑ x : V, ‖f x‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hc.le)
      _ ≤ c⁻¹ * ∑ _x : V, (1:ℝ) := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun x _ => mem_closedBall_zero_iff.mp (hf x).1)) (inv_nonneg.mpr hc.le)
      _ = 1 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
        exact inv_mul_cancel₀ (ne_of_gt hc)
  have hge : ∀ x ∈ closedBall (0:E) 1, g x = 1 ↔ ∀ v : V, f v x = 1 := by
    intro x hx
    have he : g x = c⁻¹ * ∑ v : V, f v x := by simp [g]
    rw [he]
    constructor
    · intro hgx v
      have hsum : ∑ v : V, f v x = c := by
        have ht := congrArg (fun a : ℝ => c*a) hgx
        simpa [← mul_assoc,ne_of_gt hc] using ht
      have heq : ∑ v : V, f v x = ∑ _v : V, (1:ℝ) := by simpa [c] using hsum
      exact (Finset.sum_eq_sum_iff_of_le (fun v _ =>
        (dual_eval_bounds (mem_closedBall_zero_iff.mp (hf v).1) hx).2)).mp heq v (Finset.mem_univ v)
    · intro hh
      simp only [hh, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      exact inv_mul_cancel₀ (ne_of_gt hc)
  refine ⟨g,hg,subset_antisymm (fun x hx => ⟨hF.subset hx,(hge x (hF.subset hx)).mpr
    (fun v => hfF v x hx)⟩) ?_⟩
  apply (isFace_support hg).subset_of_vertices hmed hF.1
  intro x hx
  by_contra hxn
  have hh := (hge x hx.2.1).mp hx.2.2 ⟨x,hx.1,hxn⟩
  have hm := hfx ⟨x,hx.1,hxn⟩
  linarith

lemma faceHull_radial (hdual : HasMetricMedians (E →L[ℝ] ℝ))
    {w y : E} (hw : w ∈ closedBall (0:E) 1)
    (hy : y ∈ faceHull (closedBall (0:E) 1) {w}) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧ ∃ z ∈ closedBall (0:E) 1,
      w = a • y+(1-a) • z := by
  classical
  have hyB := faceHull_min (IsFace.refl (convex_closedBall (0:E) 1))
    (singleton_subset_iff.mpr hw) hy
  let D := (closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints ℝ
  have hDf : D.Finite := finite_extreme_unit_of_medians hdual
  let S : Set ℝ := {1} ∪ ((fun f : E →L[ℝ] ℝ => (1-f w)/2) '' {f ∈ D | f w < 1})
  have hSf : S.Finite := (finite_singleton 1).union
    ((hDf.subset (fun _ h => h.1)).image _)
  have hSn : S.Nonempty := ⟨1,Or.inl (mem_singleton _)⟩
  obtain ⟨r,hr⟩ := hSf.exists_minimal hSn
  have hrmin : ∀ s ∈ S, r ≤ s := fun s hs => le_of_not_gt (fun hh => not_lt_of_ge (hr.2 hs hh.le) hh)
  have hrS := hr.1
  have hrpos : 0 < r := by
    rcases hrS with hr | ⟨f,⟨hf,hfw⟩,rfl⟩
    · simp only [mem_singleton_iff] at hr
      linarith
    · linarith
  let a := r/2
  have ha : 0 < a := by dsimp [a]; linarith
  have ha1 : a < 1 := by have hh := hrmin 1 (Or.inl (mem_singleton _)); dsimp [a]; linarith
  let z : E := (1-a)⁻¹ • (w-a • y)
  have hz : z ∈ closedBall (0:E) 1 := by
    apply mem_closedBall_zero_iff.mpr
    apply norm_le_of_dual_extreme_le
    intro f hf
    have hfw := (dual_eval_bounds (mem_closedBall_zero_iff.mp hf.1) hw).2
    have hfy := dual_eval_bounds (mem_closedBall_zero_iff.mp hf.1) hyB
    have hm : f w-a*f y ≤ 1-a := by
      by_cases he : f w = 1
      · have hyf := faceHull_min (isFace_support (mem_closedBall_zero_iff.mp hf.1))
          (singleton_subset_iff.mpr ⟨hw,he⟩) hy
        rw [he,hyf.2]
        ring_nf
        exact le_rfl
      · have hh := hrmin ((1-f w)/2) (Or.inr ⟨f,⟨hf,lt_of_le_of_ne hfw he⟩,rfl⟩)
        have hn := mul_nonneg ha.le (show 0 ≤ f y+1 by linarith)
        dsimp [a] at *
        nlinarith
    change f ((1-a)⁻¹ • (w-a • y)) ≤ 1
    simp only [map_smul,map_sub,smul_eq_mul]
    exact (inv_mul_le_iff₀ (sub_pos.mpr ha1)).mpr (by simpa using hm)
  refine ⟨a,ha,ha1,z,hz,?_⟩
  dsimp [z]
  rw [smul_smul,mul_inv_cancel₀ (ne_of_gt (sub_pos.mpr ha1)),one_smul]
  abel

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [inst512 : FiniteDimensional ℝ E]

lemma finrank_strongDual : Module.finrank ℝ (E →L[ℝ] ℝ) = Module.finrank ℝ E := by
  rw [← (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).finrank_eq]
  simp

def finiteBidual : E ≃ₗᵢ[ℝ] ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  (NormedSpace.inclusionInDoubleDualLi ℝ).toLinearIsometryEquiv
    (by rw [finrank_strongDual,finrank_strongDual])

@[simp] lemma finiteBidual_apply (x : E) (f : E →L[ℝ] ℝ) : finiteBidual x f = f x := rfl

omit inst512 in
lemma LinearIsometryEquiv.image_extreme_unit [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (e : E ≃ₗᵢ[ℝ] F) :
    e '' (closedBall (0:E) 1).extremePoints ℝ = (closedBall (0:F) 1).extremePoints ℝ := by
  rw [image_extremePoints,LinearIsometryEquiv.image_closedBall,map_zero]

lemma extreme_unit_neg {x : E} (hx : x ∈ (closedBall (0:E) 1).extremePoints ℝ) :
    -x ∈ (closedBall (0:E) 1).extremePoints ℝ := by
  have he := LinearIsometryEquiv.image_extreme_unit (LinearIsometryEquiv.neg ℝ (E:=E))
  rw [← he]
  exact ⟨x,hx,rfl⟩

variable [Nontrivial E]

lemma dual_disjoint_faces_primal_vertex (hdual : HasMetricMedians (E →L[ℝ] ℝ))
    {F G : Set (E →L[ℝ] ℝ)}
    (hF : IsFace (closedBall (0 : E →L[ℝ] ℝ) 1) F)
    (hG : IsFace (closedBall (0 : E →L[ℝ] ℝ) 1) G)
    (hFn : F.Nonempty) (hGn : G.Nonempty) (hd : Disjoint F G) :
    ∃ x ∈ (closedBall (0:E) 1).extremePoints ℝ,
      (∀ f ∈ F, f x = 1) ∧ ∀ g ∈ G, g x = -1 := by
  obtain ⟨u,hu,huF,huG⟩ := disjoint_faces_dual_vertex hdual hF hG hFn hGn hd
  rw [← LinearIsometryEquiv.image_extreme_unit (finiteBidual (E:=E))] at hu
  obtain ⟨x,hx,rfl⟩ := hu
  exact ⟨x,hx,huF,huG⟩

lemma IsParallelPair.square_points (hmed : HasMetricMedians E) {K F G : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (h : IsParallelPair K F G)
    {x y a b : E} (hx : x ∈ F) (hy : y ∈ G) (ha : a ∈ K) (hb : b ∈ K)
    (he : x+a=y+b) : a ∈ G ∧ b ∈ F := by
  obtain ⟨f,hf,heF,heG⟩ := h.support_dual_vertex hmed hK ⟨x,hx⟩ ⟨y,hy⟩
  have hfx := (heF ▸ hx).2
  have hfy := (heG ▸ hy).2
  have hfa := dual_eval_bounds (mem_closedBall_zero_iff.mp hf.1) (hK.subset ha)
  have hfb := dual_eval_bounds (mem_closedBall_zero_iff.mp hf.1) (hK.subset hb)
  have hh := congrArg f he
  simp only [map_add,hfx,hfy] at hh
  exact ⟨heG.symm ▸ ⟨ha,by linarith⟩,heF.symm ▸ ⟨hb,by linarith⟩⟩

lemma maximal_unit_face_support (hmed : HasMetricMedians E) {K : Set E}
    (hK : IsMaximalProperFace (closedBall (0:E) 1) K) (hn : K.Nonempty) :
    ∃ f ∈ (closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints ℝ,
      K = {x ∈ closedBall (0:E) 1 | f x = 1} := by
  obtain ⟨f,hf,hfK⟩ := proper_face_support hmed hK.1 hn hK.2.1
  refine ⟨f,hf,?_⟩
  apply Eq.symm
  apply hK.2.2 _ (isFace_support (mem_closedBall_zero_iff.mp hf.1))
    (fun x hx => ⟨hK.1.subset hx,hfK x hx⟩)
  intro hh
  have h0 : (0:E) ∈ {x ∈ closedBall (0:E) 1 | f x = 1} := hh.symm ▸ (by simp)
  simpa using h0.2

lemma dual_vertex_maximal_support (hmed : HasMetricMedians E) {f : E →L[ℝ] ℝ}
    (hf : f ∈ (closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints ℝ) :
    IsMaximalProperFace (closedBall (0:E) 1) {x ∈ closedBall (0:E) 1 | f x = 1} := by
  apply full_rank_maximal_proper hmed (isFace_support (mem_closedBall_zero_iff.mp hf.1))
  · intro hh
    have h0 : (0:E) ∈ {x ∈ closedBall (0:E) 1 | f x = 1} := hh.symm ▸ (by simp)
    simpa using h0.2
  · unfold faceRank
    rw [span_support_dual_vertex hmed hf,finrank_top]

lemma vertex_in_two_vertex_face (hmed : HasMetricMedians E) {a b c : E}
    (ha : a ∈ (closedBall (0:E) 1).extremePoints ℝ)
    (hb : b ∈ (closedBall (0:E) 1).extremePoints ℝ)
    (hc : c ∈ (closedBall (0:E) 1).extremePoints ℝ)
    (hcJ : c ∈ faceHull (closedBall (0:E) 1) ({a} ∪ {b})) :
    ∃ d ∈ (closedBall (0:E) 1).extremePoints ℝ, a+b=c+d := by
  obtain ⟨u,hu,d,hd,he⟩ := face_vertex_exchange hmed ha hc
    ⟨convex_singleton b,isExtreme_singleton.mpr hb⟩ (singleton_nonempty b) hcJ
  have huB : u=b := hu.1
  exact ⟨d,hd,huB ▸ he⟩

end SymmetricMahler

open Set Metric
namespace SymmetricMahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [inst516 : FiniteDimensional ℝ E] [inst517 : Nontrivial E]

def IsSplitPair (K F G : Set E) : Prop :=
  IsParallelPair K F G ∧ Disjoint (Submodule.span ℝ F) (Submodule.span ℝ G)

def IsSplitFace (K F : Set E) : Prop := ∃ G, IsSplitPair K F G

omit inst516 inst517 in
lemma disjoint_span_insert [FiniteDimensional ℝ E] [Nontrivial E] (A S V : Submodule ℝ E) {y : E}
    (hAS : Disjoint A S) (hAV : A ≤ V) (hSV : S ≤ V) (hy : y ∉ V) :
    Disjoint A (Submodule.span ℝ ({y} : Set E) ⊔ S) := by
  rw [Submodule.disjoint_def]
  intro z hzA hz
  obtain ⟨t,ht,s,hs,rfl⟩ := Submodule.mem_sup.mp hz
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp ht
  have hay : a • y ∈ V := by
    convert V.sub_mem (hAV hzA) (hSV hs) using 1 ; abel
  have ha : a = 0 := by
    by_contra hn
    exact hy ((Submodule.smul_mem_iff V hn).mp hay)
  simp only [ha,zero_smul,zero_add] at hzA ⊢
  exact Submodule.disjoint_def.mp hAS s hzA hs

theorem split_of_no_vertex_parallelogram (hmed : HasMetricMedians E) {K F G : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (hp : K ≠ closedBall (0:E) 1)
    (hpair : IsParallelPair K F G)
    (hn : ∀ x ∈ F ∩ (closedBall (0:E) 1).extremePoints ℝ,
      ∀ z ∈ F ∩ (closedBall (0:E) 1).extremePoints ℝ,
      ∀ y ∈ G ∩ (closedBall (0:E) 1).extremePoints ℝ,
      ∀ w ∈ G ∩ (closedBall (0:E) 1).extremePoints ℝ, x+y=z+w → x=z) :
    Disjoint (Submodule.span ℝ F) (Submodule.span ℝ G) := by
  classical
  generalize hr : faceRank K = r
  induction r using Nat.strong_induction_on generalizing K F G with
  | h r ih =>
    by_cases hFn : F.Nonempty
    · by_cases hGn : G.Nonempty
      · obtain ⟨y,hy,hyG⟩ := (hK.trans hpair.2.1).exists_vertex hmed hGn
        have hyK := hK.extreme_mem hy (hpair.2.1.subset hyG)
        have hyF := (hpair.not_mem_iff hyK).mpr hyG
        obtain ⟨H,hH,hFH,hyH⟩ := extend_face_avoiding_vertex hmed hK hp hpair.1 hFn hyK hyF
        obtain ⟨H',hHH⟩ := maximal_proper_parallel hmed hK hH (hFn.mono hFH)
        have hHr := faceRank_lt hmed hK hp hH.1 hH.2.1
        have hHball := hK.trans hH.1
        have hHp := proper_unit_face_subface_ne hK hp hH.1.subset
        have hFGH : IsParallelPair H F (H ∩ G) := by
          have hh := hpair.restrict hmed hK hH.1
          have he : H ∩ F = F := inter_eq_right.mpr hFH
          rwa [he] at hh
        have hdis : Disjoint (Submodule.span ℝ F) (Submodule.span ℝ (H ∩ G)) := by
          apply ih (faceRank H) (by omega) hHball hHp hFGH
          · intro x hx z hz a ha b hb he
            exact hn x hx z hz a ⟨ha.1.2,ha.2⟩ b ⟨hb.1.2,hb.2⟩ he
          · rfl
        have hspanG : Submodule.span ℝ G ≤
            Submodule.span ℝ ({y} : Set E) ⊔ Submodule.span ℝ (H ∩ G) := by
          apply Submodule.span_le.mpr
          apply (hK.trans hpair.2.1).subset_of_vertices hmed (Submodule.convex _)
          intro z hz
          by_cases hzH : z ∈ H
          · exact Submodule.mem_sup_right (Submodule.subset_span ⟨hzH,hz.2⟩)
          by_cases hzy : z = y
          · subst z
            exact Submodule.mem_sup_left (Submodule.subset_span (mem_singleton y))
          have hzK := hK.extreme_mem hz.1 (hpair.2.1.subset hz.2)
          obtain ⟨u,hu,v,hv,he⟩ := hH.exchange hmed hK hHH (hFn.mono hFH)
            hyK ((hHH.not_mem_iff hyK).mp hyH) hzK ((hHH.not_mem_iff hzK).mp hzH)
          have huK := hK.extreme_mem hu.2 (hH.1.subset hu.1)
          have hvK := hK.extreme_mem hv.2 (hH.1.subset hv.1)
          have huG : u ∈ G := by
            rcases hpair.vertex_mem huK with huF | huG
            · have hvF : v ∈ F := by
                rcases hpair.vertex_mem hvK with hvF | hvG
                · exact hvF
                · have huG := (face_mem_of_parallelogram hpair.2.1 hz.2 hvG
                    hyK.1 huK.1 he.symm).2
                  exact False.elim (disjoint_left.mp hpair.2.2.1 huF huG)
              have huv := hn u ⟨huF,hu.2⟩ v ⟨hvF,hv.2⟩
                y ⟨hyG,hy⟩ z ⟨hz.2,hz.1⟩ (by simpa [add_comm] using he)
              have hyz : y = z := by simpa [huv] using he
              exact False.elim (hzy hyz.symm)
            · exact huG
          have hvG : v ∈ G :=
            (face_mem_of_parallelogram hpair.2.1 hyG huG hzK.1 hvK.1 he).2
          have hzEq : z = y+u-v := by rw [he]; abel
          rw [hzEq]
          exact (Submodule.span ℝ ({y}:Set E) ⊔ Submodule.span ℝ (H ∩ G)).sub_mem
            ((Submodule.span ℝ ({y}:Set E) ⊔ Submodule.span ℝ (H ∩ G)).add_mem
              (Submodule.mem_sup_left (Submodule.subset_span (mem_singleton y)))
              (Submodule.mem_sup_right (Submodule.subset_span ⟨hu.1,huG⟩)))
            (Submodule.mem_sup_right (Submodule.subset_span ⟨hv.1,hvG⟩))
        exact (disjoint_span_insert _ _ (Submodule.span ℝ H) hdis
          (Submodule.span_mono hFH) (Submodule.span_mono inter_subset_left)
          (vertex_not_mem_span_face hmed hK hp hH.1 hyK hyH)).mono_right hspanG
      · simp [not_nonempty_iff_eq_empty.mp hGn]
    · simp [not_nonempty_iff_eq_empty.mp hFn]

theorem nonsplit_vertex_parallelogram (hmed : HasMetricMedians E) {K F G : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (hp : K ≠ closedBall (0:E) 1)
    (hpair : IsParallelPair K F G) (hns : ¬ IsSplitFace K F) :
    ∃ x ∈ F ∩ (closedBall (0:E) 1).extremePoints ℝ,
      ∃ z ∈ F ∩ (closedBall (0:E) 1).extremePoints ℝ,
      ∃ y ∈ G ∩ (closedBall (0:E) 1).extremePoints ℝ,
      ∃ w ∈ G ∩ (closedBall (0:E) 1).extremePoints ℝ, x ≠ z ∧ x+y=z+w := by
  classical
  by_contra! hn
  apply hns
  refine ⟨G,hpair,split_of_no_vertex_parallelogram hmed hK hp hpair ?_⟩
  intro x hx z hz y hy w hw he
  by_contra hne
  exact hn x hx z hz y hy w hw hne he

end SymmetricMahler

end

end OAI
