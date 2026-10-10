import OAI.Probability.GammaPassage.ContiguousWitnesses

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP
open Set

/-- A constructive form of wi:full-defect. If the greedy family is empty,
a cheap full chunk supplies a single witness. No maximum is assumed. -/
theorem spatial_full_chunk_witnesses (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (b m₀ am ap K η : ℝ) (hb : |b| ≤ 1) (ha : am ≤ ap) (hη : 0 < η)
    (hgap : 4*η ≤ (ap-am)/2) (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k)
    (hstep : max |m₀-((am+ap)/2)*b| |(am+ap)/2| ≤ η*(2 : ℝ)^k)
    (hscale₁ : η*(2 : ℝ)^k < 2*m₀*(2 : ℝ)^m-|((am+ap)/2)| *((2 : ℝ)^k+1))
    (hscale₂ : 3*η*(2 : ℝ)^k+2*|((am+ap)/2)| *((2 : ℝ)^k+1) < K*(2 : ℝ)^k)
    (p : Vertex) (ds : List Step) (hfull : FullSpatialChunk b k m ds)
    (hsimple : ((trace p ds).map traversalEdge).Nodup) :
    ∃ ws : List GammaFPP.BK.StrictPathWitness,
      ws.Pairwise (fun q r => Disjoint q.edges r.edges) ∧
      (∀ q ∈ ws, q ∈ spatialWitnessFamily b m₀ am ap K η k m (spatialChunkIndex b k m p) ∧
        q.Good w ∧ q.edges ⊆ pathEdges p ds) ∧
      η*(2 : ℝ)^k-4*η*(2 : ℝ)^k*ws.length ≤ defect w b m₀ ((am+ap)/2) p ds := by
  have hηs : 0 ≤ η*(2 : ℝ)^k := by positivity
  obtain ⟨ws,hpair,hws,hbasic⟩ := spatial_negative_prefix_witnesses w hw b m₀ am ap K η ha hη.le k m
    (spatialChunkIndex b k m p) hstep p ds (fullSpatialChunk_in_box b hb k m hs p ds hfull) hsimple
  by_cases hempty : ws=[]
  · subst ws
    simp only [List.length_nil,Nat.cast_zero,mul_zero,sub_zero] at hbasic
    by_cases hcheap : defect w b m₀ ((am+ap)/2) p ds < η*(2 : ℝ)^k
    · obtain ⟨q,hq,hg,he⟩ := cheap_full_spatial_chunk_witness w hw b m₀ am ap K η hb ha hη hgap
        k m hs hscale₁ hscale₂ p ds hfull hcheap
      refine ⟨[q],by simp,?_,?_⟩
      · intro r hr
        have heq : r=q := List.mem_singleton.mp hr
        subst r
        exact ⟨hq,hg,he⟩
      · simp only [List.length_singleton,Nat.cast_one,mul_one]
        linarith
    · exact ⟨[],by simp,by simp,by simpa using le_of_not_gt hcheap⟩
  · have hlen : (1 : ℝ) ≤ ws.length := by exact_mod_cast List.length_pos_iff.mpr hempty
    refine ⟨ws,hpair,hws,?_⟩
    nlinarith [mul_le_mul_of_nonneg_left hlen hηs]

/-- Source wi:total-defect, including all physical-edge disjointness and the
actual ordered chunk indices. Witness families are constructed, not supplied. -/
theorem spatial_total_witnesses (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (b m₀ am ap K η : ℝ) (hb : |b| ≤ 1) (ha : am ≤ ap) (hη : 0 < η)
    (hgap : 4*η ≤ (ap-am)/2) (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k)
    (hstep : max |m₀-((am+ap)/2)*b| |(am+ap)/2| ≤ η*(2 : ℝ)^k)
    (hscale₁ : η*(2 : ℝ)^k < 2*m₀*(2 : ℝ)^m-|((am+ap)/2)| *((2 : ℝ)^k+1))
    (hscale₂ : 3*η*(2 : ℝ)^k+2*|((am+ap)/2)| *((2 : ℝ)^k+1) < K*(2 : ℝ)^k)
    (p : Vertex) (blocks : List (List Step)) (rest : List Step)
    (hfull : ∀ q ∈ blocks, FullSpatialChunk b k m q)
    (hrest : ∀ i ≤ rest.length, chunkInterior b k m (displacement (rest.take i)))
    (hsimple : ((trace p (blocks.flatten++rest)).map traversalEdge).Nodup) :
    ∃ packs : List (List GammaFPP.BK.StrictPathWitness),
      packs.length=blocks.length+1 ∧
      List.Forall₂ (fun ws ih => ∀ q ∈ ws,
        q ∈ spatialWitnessFamily b m₀ am ap K η k m ih ∧ q.Good w)
        packs (spatialChunkIndex b k m p :: chunkIndexTail b k m p blocks) ∧
      packs.flatten.Pairwise (fun q r => Disjoint q.edges r.edges) ∧
      (∀ q ∈ packs.flatten, q.edges ⊆ pathEdges p (blocks.flatten++rest)) ∧
      ((blocks.length : ℝ)-1)*η*(2 : ℝ)^k-4*η*(2 : ℝ)^k*packs.flatten.length ≤
        defect w b m₀ ((am+ap)/2) p (blocks.flatten++rest) := by
  have hηs : 0 ≤ η*(2 : ℝ)^k := by positivity
  induction blocks generalizing p with
  | nil =>
    have hin := spatial_chunk_in_box b k m hs p rest
      (proper_chunk_localization b hb k m rest (fun i hi => hrest i hi.le))
    obtain ⟨ws,hpair,hws,hbound⟩ := spatial_negative_prefix_witnesses w hw b m₀ am ap K η ha hη.le k m
      (spatialChunkIndex b k m p) hstep p rest hin (by simpa using hsimple)
    refine ⟨[ws],rfl,?_,by simpa using hpair,?_,?_⟩
    · exact List.Forall₂.cons (fun q hq => ⟨(hws q hq).1,(hws q hq).2.1⟩) List.Forall₂.nil
    · simpa using (fun q hq => (hws q hq).2.2)
    · simp only [List.length_nil,Nat.cast_zero,zero_sub,neg_mul,one_mul,List.flatten_singleton,List.flatten_nil,List.nil_append]
      nlinarith [mul_nonneg hηs (show (0 : ℝ) ≤ ws.length by positivity)]
  | cons ds blocks rec =>
    have hsim : ((trace p (ds++(blocks.flatten++rest))).map traversalEdge).Nodup := by
      simpa only [List.flatten_cons,List.append_assoc] using hsimple
    have hsplit := simple_append_edges p ds (blocks.flatten++rest) hsim
    obtain ⟨ws,hpair,hws,hbound⟩ := spatial_full_chunk_witnesses w hw b m₀ am ap K η hb ha hη hgap k m hs
      hstep hscale₁ hscale₂ p ds (hfull ds (by simp)) hsplit.1
    obtain ⟨packs,hlen,hassign,hdisj,hedges,htotal⟩ := rec (p+displacement ds)
      (fun q hq => hfull q (by simp [hq])) hsplit.2.1
    refine ⟨ws::packs,by simp [hlen],List.Forall₂.cons ?_ hassign,?_,?_,?_⟩
    · exact fun q hq => ⟨(hws q hq).1,(hws q hq).2.1⟩
    · simp only [List.flatten_cons,List.pairwise_append]
      refine ⟨hpair,hdisj,?_⟩
      intro q hq r hr
      exact hsplit.2.2.mono (hws q hq).2.2 (hedges r hr)
    · intro q hq
      simp only [List.flatten_cons,List.mem_append] at hq
      simp only [List.flatten_cons,List.append_assoc]
      rw [pathEdges_append]
      rcases hq with hq | hq
      · exact (hws q hq).2.2.trans Finset.subset_union_left
      · exact (hedges q hq).trans Finset.subset_union_right
    · simp only [List.flatten_cons,List.append_assoc,List.length_cons,List.length_append,
        Nat.cast_add,Nat.cast_one]
      rw [defect_append]
      linarith

end GammaFPP.CrossingBridge

end OAI
