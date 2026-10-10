import OAI.Probability.GammaPassage.SpatialCrossingGeometry

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP Set

/-- Positive-longitudinal case of wi:chunk-witness. The outer pieces are
checked first; otherwise the actual middle subcrossing witnesses E(s,L). -/
theorem positive_longitudinal_chunk_witness (w : Edge → ℝ) (b m₀ am ap K η : ℝ)
    (hb : |b| ≤ 1) (ha : am ≤ ap) (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k)
    (hscale : 3*η*(2 : ℝ)^k+2*|((am+ap)/2)| *((2 : ℝ)^k+1) < K*(2 : ℝ)^k)
    (p : Vertex) (ds : List Step) (hfull : FullSpatialChunk b k m ds)
    (hx : (displacement ds).1=2*(2 : ℤ)^m)
    (hcheap : defect w b m₀ ((am+ap)/2) p ds < η*(2 : ℝ)^k) :
    ∃ q ∈ spatialWitnessFamily b m₀ am ap K η k m (spatialChunkIndex b k m p),
      q.Good w ∧ q.edges ⊆ pathEdges p ds := by
  let ih := spatialChunkIndex b k m p
  let L : ℤ := (2 : ℤ)^m
  let A := (ih.1+1)*L
  let B := (ih.1+2)*L
  have hL : 0 < L := by dsimp [L]; positivity
  have hi := meshFloor_bounds p.1 L hL
  have hidx : ih.1=p.1/L := rfl
  have hpA : p.1 ≤ A := by dsimp [A]; rw [hidx]; dsimp [meshFloor] at hi; nlinarith [hi.2]
  have hAB : A ≤ B := by dsimp [A,B]; nlinarith
  have hend : B ≤ (p+displacement ds).1 := by
    dsimp [B]
    rw [hidx]
    simp only [hx]
    dsimp [meshFloor] at hi
    change p.1/L*L ≤ p.1 ∧ _ at hi
    dsimp [L] at *
    nlinarith [hi.1]
  obtain ⟨pre,mid,post,heq,hpre,hmid,hincols⟩ := path_column_subcrossing p ds A B hpA hAB hend
  let box : Set Vertex := {z | z-spatialTranslate b k m ih ∈ endpointBox b 4 4 k m}
  have hin : PathIn p (pre++mid++post) box := by
    rw [← heq]
    exact fullSpatialChunk_in_box b hb k m hs p ds hfull
  have hprebox : PathIn p pre box :=
    pathIn_append_left p pre mid box (pathIn_append_left p (pre++mid) post box hin)
  have hpostbox := pathIn_append_right p (pre++mid) post box hin
  by_cases hnegPre : defect w b m₀ ((am+ap)/2) p pre < -η*(2 : ℝ)^k
  · obtain ⟨q,hq,hqs,hqd,hgood⟩ := negative_midpoint_spatial_witness w b m₀ am ap K η ha k m ih p pre hprebox hnegPre
    refine ⟨q,hq,hgood,?_⟩
    change pathEdges q.start q.steps ⊆ pathEdges p ds
    rw [hqs,hqd,heq,pathEdges_append,pathEdges_append]
    exact Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left
  · by_cases hnegPost : defect w b m₀ ((am+ap)/2) (p+displacement (pre++mid)) post < -η*(2 : ℝ)^k
    · obtain ⟨q,hq,hqs,hqd,hgood⟩ := negative_midpoint_spatial_witness w b m₀ am ap K η ha k m ih
        (p+displacement (pre++mid)) post hpostbox hnegPost
      refine ⟨q,hq,hgood,?_⟩
      change pathEdges q.start q.steps ⊆ pathEdges p ds
      rw [hqs,hqd,heq,pathEdges_append]
      exact Finset.subset_union_right
    · have hprelo := le_of_not_gt hnegPre
      have hpostlo := le_of_not_gt hnegPost
      have hsum := hcheap
      rw [heq,defect_append,defect_append] at hsum
      have hmidcheap : defect w b m₀ ((am+ap)/2) (p+displacement pre) mid < 3*η*(2 : ℝ)^k := by linarith
      have hrloc : PathIn p (pre++mid++post) {z | |transverse b z-transverse b p| ≤ (2 : ℝ)^k+1} := by
        rw [← heq]
        intro i hi'
        simpa only [mem_ofPred_eq,transverse_add,add_sub_cancel_left] using
          (proper_chunk_localization b hb k m ds hfull.1 i hi').2
      have hrmid := pathIn_middle p pre mid post _ hrloc
      have hrstart : |transverse b (p+displacement pre)-transverse b p| ≤ (2 : ℝ)^k+1 := by
        simpa using hrmid 0 (by omega)
      have hrend := pathIn_endpoint _ _ _ hrmid
      change |transverse b (p+displacement pre+displacement mid)-transverse b p| ≤ (2 : ℝ)^k+1 at hrend
      have hrd : |transverse b (displacement mid)| ≤ 2*((2 : ℝ)^k+1) := by
        have hh := abs_sub (transverse b (p+displacement pre+displacement mid)-transverse b p)
          (transverse b (p+displacement pre)-transverse b p)
        simp only [transverse_add] at hh hrend
        have he : transverse b p+transverse b (displacement pre)+transverse b (displacement mid)-transverse b p-
            (transverse b p+transverse b (displacement pre)-transverse b p)=transverse b (displacement mid) := by ring
        rw [he] at hh
        simp only [transverse_add] at hrstart
        linarith
      have hdx : (displacement mid).1=L := by
        simp only [Prod.fst_add] at hmid
        dsimp [A,B] at hpre hmid
        nlinarith
      have hac := mul_le_mul_of_nonneg_left hrd (abs_nonneg ((am+ap)/2))
      have haa := le_abs_self (((am+ap)/2)*transverse b (displacement mid))
      rw [abs_mul] at haa
      have hcost : pathCost w (p+displacement pre) mid < m₀*(L : ℝ)+K*(2 : ℝ)^k := by
        unfold defect support at hmidcheap
        rw [hdx] at hmidcheap
        nlinarith
      let q : GammaFPP.BK.StrictPathWitness := ⟨p+displacement pre,mid,m₀*(L : ℝ)+K*(2 : ℝ)^k⟩
      refine ⟨q,Or.inr ⟨?_,?_,?_,?_⟩,hcost,?_⟩
      · change (p+displacement pre).1=(spatialTranslate b k m (ih+(1,0))).1
        simpa [A,spatialTranslate,L] using hpre
      · change (p+displacement pre+displacement mid).1=(spatialTranslate b k m (ih+(1,0))).1+(2 : ℤ)^m
        rw [hmid]
        dsimp [B,spatialTranslate,L]
        ring
      · intro i hi'
        exact chunk_subcrossing_region b k m hs p _ (hincols i hi') (hrmid i hi')
      · change m₀*(L : ℝ)+K*(2 : ℝ)^k=m₀*(2 : ℤ)^m+K*(2 : ℝ)^k
        simp [L]
      · change pathEdges (p+displacement pre) mid ⊆ pathEdges p ds
        rw [heq]
        exact pathEdges_middle_subset p pre mid post

/-- Complete source wi:chunk-witness for actual full chunks. -/
theorem cheap_full_spatial_chunk_witness (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (b m₀ am ap K η : ℝ) (hb : |b| ≤ 1) (ha : am ≤ ap) (hη : 0 < η)
    (hgap : 4*η ≤ (ap-am)/2) (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k)
    (hscale₁ : η*(2 : ℝ)^k < 2*m₀*(2 : ℝ)^m-|((am+ap)/2)| *((2 : ℝ)^k+1))
    (hscale₂ : 3*η*(2 : ℝ)^k+2*|((am+ap)/2)| *((2 : ℝ)^k+1) < K*(2 : ℝ)^k)
    (p : Vertex) (ds : List Step) (hfull : FullSpatialChunk b k m ds)
    (hcheap : defect w b m₀ ((am+ap)/2) p ds < η*(2 : ℝ)^k) :
    ∃ q ∈ spatialWitnessFamily b m₀ am ap K η k m (spatialChunkIndex b k m p),
      q.Good w ∧ q.edges ⊆ pathEdges p ds := by
  by_cases hr : (2 : ℝ)^k ≤ |transverse b (displacement ds)|
  · obtain ⟨q,hq,hs',hd',hg⟩ := full_chunk_transverse_witness w b m₀ am ap K η hb ha hη hgap k m hs p ds hfull hr hcheap
    refine ⟨q,hq,hg,?_⟩
    change pathEdges q.start q.steps ⊆ pathEdges p ds
    rw [hs',hd']
  · have hl := (proper_chunk_endpoint_localization b hb k m ds hfull.1).1
    have hx : 2*(2 : ℤ)^m ≤ |(displacement ds).1| := by
      by_contra hh
      exact hfull.2 ⟨lt_of_not_ge hh,lt_of_not_ge hr⟩
    have heq : |(displacement ds).1|=2*(2 : ℤ)^m := le_antisymm hl hx
    rcases eq_or_eq_neg_of_abs_eq heq with hx | hx
    · exact positive_longitudinal_chunk_witness w b m₀ am ap K η hb ha k m hs hscale₂ p ds hfull hx hcheap
    · have hh := negative_longitudinal_chunk_not_cheap w hw b m₀ ((am+ap)/2) η hb k m p ds hfull
        (by simpa using hx) hscale₁
      linarith

end GammaFPP.CrossingBridge

end OAI
