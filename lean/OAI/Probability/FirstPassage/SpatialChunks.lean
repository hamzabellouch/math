import OAI.Probability.FirstPassage.SpatialFirstExit

namespace OAI

namespace PlanarFPP
open Set

theorem spatial_chunk_decomposition (b : ℝ) (k m : ℕ) (ds : List Step) :
    ∃ blocks : List (List Step), ∃ rest : List Step,
      ds=blocks.flatten++rest ∧ (∀ q ∈ blocks, FullSpatialChunk b k m q) ∧
      (∀ i ≤ rest.length, chunkInterior b k m (displacement (rest.take i))) := by
  induction hn : ds.length using Nat.strong_induction_on generalizing ds with
  | h n ih =>
    rcases first_full_spatial_chunk b k m ds with hrest | ⟨pre,rest,heq,hpre,hfull⟩
    · exact ⟨[],ds,by simp,by simp,hrest⟩
    · have hlen : rest.length < n := by
        rw [heq,List.length_append] at hn
        have hp := List.length_pos_iff.mpr hpre
        omega
      obtain ⟨bs,tail,hbs,hbf,hbt⟩ := ih rest.length hlen rest rfl
      refine ⟨pre::bs,tail,?_,?_,hbt⟩
      · simp [heq,hbs,List.append_assoc]
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hfull
        · exact hbf q hq

lemma spatial_chunk_displacement_bound (b : ℝ) (hb : |b| ≤ 1) (k m : ℕ)
    (blocks : List (List Step)) (rest : List Step)
    (hfull : ∀ q ∈ blocks, FullSpatialChunk b k m q)
    (hrest : ∀ i ≤ rest.length, chunkInterior b k m (displacement (rest.take i))) :
    |(displacement (blocks.flatten++rest)).1| ≤ 2*(2 : ℤ)^m*((blocks.length : ℤ)+1) := by
  induction blocks with
  | nil =>
    have hh := (hrest rest.length le_rfl).1.le
    simpa using hh
  | cons q qs ih =>
    have hq := proper_chunk_endpoint_localization b hb k m q (hfull q (by simp)).1
    have htail := ih (fun v hv => hfull v (by simp [hv]))
    simp only [List.flatten_cons,List.append_assoc,displacement_append,Prod.fst_add,List.length_cons,Nat.cast_add,Nat.cast_one]
    have ht := abs_add_le (displacement q).1 (displacement (qs.flatten++rest)).1
    simp only [displacement_append,Prod.fst_add] at ht htail
    nlinarith [hq.1]

noncomputable def chunkIndexTail (b : ℝ) (k m : ℕ) : Vertex → List (List Step) → List (ℤ×ℤ)
  | _,[] => []
  | p,q::qs => spatialChunkIndex b k m (p+displacement q)::chunkIndexTail b k m (p+displacement q) qs

def BoundedIndexSteps : (ℤ×ℤ) → List (ℤ×ℤ) → Prop
  | _,[] => True
  | p,q::qs => |q.1-p.1| ≤ 3 ∧ |q.2-p.2| ≤ 3 ∧ BoundedIndexSteps q qs

lemma chunkIndexTail_length (b : ℝ) (k m : ℕ) (p : Vertex) (blocks : List (List Step)) :
    (chunkIndexTail b k m p blocks).length=blocks.length := by
  induction blocks generalizing p with
  | nil => rfl
  | cons q qs ih => simp [chunkIndexTail,ih]

lemma chunkIndexTail_bounded (b : ℝ) (hb : |b| ≤ 1) (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k)
    (p : Vertex) (blocks : List (List Step))
    (hfull : ∀ q ∈ blocks, FullSpatialChunk b k m q) :
    BoundedIndexSteps (spatialChunkIndex b k m p) (chunkIndexTail b k m p blocks) := by
  induction blocks generalizing p with
  | nil => trivial
  | cons q qs ih =>
    have hq := proper_chunk_endpoint_localization b hb k m q (hfull q (by simp)).1
    have hinc := spatialChunkIndex_increment b k m hs p (p+displacement q)
      (by simpa only [Prod.fst_add,add_sub_cancel_left] using hq.1)
      (by simpa only [transverse_add,add_sub_cancel_left] using hq.2)
    exact ⟨hinc.1,hinc.2,ih _ (fun v hv => hfull v (by simp [hv]))⟩

end PlanarFPP

end OAI
