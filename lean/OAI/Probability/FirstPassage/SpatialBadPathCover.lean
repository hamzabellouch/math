import OAI.Probability.FirstPassage.WitnessEntropy

namespace OAI

namespace PlanarFPP
open Set Finset

def SpatialBadPath (w : Edge → ℝ) (b m₀ a η : ℝ) (k m N : ℕ) : Prop :=
  ∃ blocks : List (List Step), ∃ rest : List Step,
    blocks.length=N ∧ (∀ q ∈ blocks, FullSpatialChunk b k m q) ∧
    (∀ i ≤ rest.length, chunkInterior b k m (displacement (rest.take i))) ∧
    ((trace 0 (blocks.flatten++rest)).map traversalEdge).Nodup ∧
    defect w b m₀ a 0 (blocks.flatten++rest) < N*η*(2 : ℝ)^k/2

theorem spatial_bad_path_cover (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (b m₀ am ap K η : ℝ) (hb : |b| ≤ 1) (ha : am ≤ ap) (hη : 0 < η)
    (hgap : 4*η ≤ (ap-am)/2) (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k)
    (hstep : max |m₀-((am+ap)/2)*b| |(am+ap)/2| ≤ η*(2 : ℝ)^k)
    (hscale₁ : η*(2 : ℝ)^k < 2*m₀*(2 : ℝ)^m-|((am+ap)/2)| *((2 : ℝ)^k+1))
    (hscale₂ : 3*η*(2 : ℝ)^k+2*|((am+ap)/2)| *((2 : ℝ)^k+1) < K*(2 : ℝ)^k)
    (N : ℕ) (hN : 4 ≤ N) (hbad : SpatialBadPath w b m₀ ((am+ap)/2) η k m N) :
    ∃ is ∈ spatialItineraries 0 N, ∃ ns ∈ compositionCover N (N/16),
      (0::is).length=ns.length ∧
      StrictDisjointPaths (spatialListSupport b k m (witnessLabels ns (0::is)))
        ((witnessLabels ns (0::is)).map (spatialWitnessFamily b m₀ am ap K η k m)) w := by
  obtain ⟨blocks,rest,hlen,hfull,hrest,hsimple,hcheap⟩ := hbad
  obtain ⟨packs,hplen,hassign,hpair,hedges,hlower⟩ := spatial_total_witnesses w hw b m₀ am ap K η hb ha hη
    hgap k m hs hstep hscale₁ hscale₂ 0 blocks rest hfull hrest hsimple
  have hcount : N/16 ≤ packs.flatten.length :=
    long_path_witness_count (defect w b m₀ ((am+ap)/2) 0 (blocks.flatten++rest)) (η*(2 : ℝ)^k) (by positivity) N _ hN
      (by rw [hlen] at hlower; nlinarith [hlower]) (by nlinarith [hcheap])
  let selected := takeWitnessPacks (N/16) packs
  let ns := selected.map List.length
  let is := chunkIndexTail b k m 0 blocks
  have hilen : is.length=N := by dsimp [is]; rw [chunkIndexTail_length,hlen]
  have his : is ∈ spatialItineraries 0 N := by
    have hh := mem_spatialItineraries (spatialChunkIndex b k m 0) is (chunkIndexTail_bounded b hb k m hs 0 blocks hfull)
    simpa only [spatialChunkIndex_origin,hilen] using hh
  have hnlen : ns.length=N+1 := by simp [ns,selected,takeWitnessPacks_length,hplen,hlen]
  have hnflat : selected.flatten=packs.flatten.take (N/16) := takeWitnessPacks_flatten ..
  have hnsum : ns.sum=N/16 := by
    change (selected.map List.length).sum=_
    rw [← List.length_flatten,hnflat,List.length_take,Nat.min_eq_left hcount]
  have hselected := takeWitnessPacks_assign
    (fun q ih => q ∈ spatialWitnessFamily b m₀ am ap K η k m ih ∧ q.Good w) (N/16) packs _ hassign
  have hselectedPair : selected.flatten.Pairwise (fun q r => Disjoint q.edges r.edges) := by
    rw [hnflat]
    exact hpair.sublist (List.take_sublist ..)
  refine ⟨is,his,ns,(mem_compositionCover ..).mpr ⟨hnlen,hnsum⟩,by simp [hilen,hnlen],?_⟩
  have hc := witnessPacks_strictDisjoint w b m₀ am ap K η k m selected
    (spatialChunkIndex b k m 0::is) hselected hselectedPair
  simpa only [spatialChunkIndex_origin] using hc

end PlanarFPP

end OAI
