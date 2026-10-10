import OAI.Probability.GammaPassage.SpatialChunkGeometry

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP Set

noncomputable def chunkInterior (b : ℝ) (k m : ℕ) (v : Vertex) : Prop :=
  |v.1| < 2*(2 : ℤ)^m ∧ |transverse b v| < (2 : ℝ)^k

noncomputable def FullSpatialChunk (b : ℝ) (k m : ℕ) (ds : List Step) : Prop :=
  (∀ i < ds.length, chunkInterior b k m (displacement (ds.take i))) ∧
    ¬chunkInterior b k m (displacement ds)

lemma chunkInterior_zero (b : ℝ) (k m : ℕ) : chunkInterior b k m 0 := by
  constructor
  · change (0 : ℤ) < 2*(2 : ℤ)^m
    positivity
  · simp [transverse]

lemma fullSpatialChunk_nonempty (b : ℝ) (k m : ℕ) (ds : List Step)
    (h : FullSpatialChunk b k m ds) : ds ≠ [] := by
  intro he
  subst ds
  exact h.2 (chunkInterior_zero b k m)

/-- The first exit is selected from the actual finite path. No chunk or
subpath existence is assumed. -/
theorem first_full_spatial_chunk (b : ℝ) (k m : ℕ) (ds : List Step) :
    (∀ i ≤ ds.length, chunkInterior b k m (displacement (ds.take i))) ∨
    ∃ pre rest : List Step, ds=pre++rest ∧ pre ≠ [] ∧ FullSpatialChunk b k m pre := by
  classical
  by_cases h : ∃ i : ℕ, i ≤ ds.length ∧ ¬chunkInterior b k m (displacement (ds.take i))
  · let n := Nat.find h
    have hn := Nat.find_spec h
    have hn0 : 0 < n := by
      by_contra hh
      have he : n=0 := by omega
      have hn' : ¬chunkInterior b k m (displacement (ds.take n)) := hn.2
      simp only [he,List.take_zero,displacement_nil] at hn'
      exact hn' (chunkInterior_zero b k m)
    have hlen : (ds.take n).length=n := List.length_take_of_le hn.1
    refine Or.inr ⟨ds.take n,ds.drop n,(List.take_append_drop n ds).symm,?_,?_,?_⟩
    · intro he
      rw [he] at hlen
      simp only [List.length_nil] at hlen
      omega
    · intro i hi
      rw [hlen] at hi
      have hnot := Nat.find_min h hi
      have hip : i ≤ ds.length := by omega
      have hv : chunkInterior b k m (displacement (ds.take i)) := by tauto
      simpa only [List.take_take,Nat.min_eq_left hi.le] using hv
    · exact hn.2
  · exact Or.inl (fun i hi => by by_contra hn; exact h ⟨i,hi,hn⟩)

lemma step_transverse_abs_le (b : ℝ) (hb : |b| ≤ 1) (d : Step) : |transverse b d.delta| ≤ 1 := by
  cases d with
  | east => simpa [Step.delta,transverse] using hb
  | west => simpa [Step.delta,transverse] using hb
  | north => norm_num [Step.delta,transverse]
  | south => norm_num [Step.delta,transverse]

/-- A step out of the open chunk rectangle overshoots transversely by at
most one and cannot overshoot the integer longitudinal boundary. -/
lemma chunk_step_localization (b : ℝ) (hb : |b| ≤ 1) (k m : ℕ) (v : Vertex)
    (hv : chunkInterior b k m v) (d : Step) :
    |(v+d.delta).1| ≤ 2*(2 : ℤ)^m ∧ |transverse b (v+d.delta)| ≤ (2 : ℝ)^k+1 := by
  have hx := abs_lt.mp hv.1
  constructor
  · cases d <;> simp only [Step.delta,Prod.fst_add] <;> apply abs_le.mpr <;> omega
  · rw [transverse_add]
    exact (abs_add_le _ _).trans (by linarith [hv.2,step_transverse_abs_le b hb d])

lemma proper_chunk_endpoint_localization (b : ℝ) (hb : |b| ≤ 1) (k m : ℕ) (ds : List Step)
    (hproper : ∀ i < ds.length, chunkInterior b k m (displacement (ds.take i))) :
    |(displacement ds).1| ≤ 2*(2 : ℤ)^m ∧ |transverse b (displacement ds)| ≤ (2 : ℝ)^k+1 := by
  induction ds using List.reverseRecOn with
  | nil =>
    constructor
    · change (0 : ℤ) ≤ 2*(2 : ℤ)^m
      positivity
    · simpa [transverse] using (show (0 : ℝ) ≤ (2 : ℝ)^k+1 by positivity)
  | append_singleton ds d _ih =>
    have h := hproper ds.length (by simp)
    have ht : (ds++[d]).take ds.length=ds := by simp
    rw [ht] at h
    simpa [displacement_append,displacement] using chunk_step_localization b hb k m (displacement ds) h d

lemma proper_chunk_localization (b : ℝ) (hb : |b| ≤ 1) (k m : ℕ) (ds : List Step)
    (hproper : ∀ i < ds.length, chunkInterior b k m (displacement (ds.take i))) :
    ∀ i ≤ ds.length, |(displacement (ds.take i)).1| ≤ 2*(2 : ℤ)^m ∧
      |transverse b (displacement (ds.take i))| ≤ (2 : ℝ)^k+1 := by
  intro i hi
  rcases lt_or_eq_of_le hi with hi | rfl
  · exact ⟨(hproper i hi).1.le,by linarith [(hproper i hi).2]⟩
  · simpa using proper_chunk_endpoint_localization b hb k m ds hproper

/-- Every full first-exit chunk supplies the precise spatial box needed by
the actual witness family, including its terminal vertex. -/
lemma fullSpatialChunk_in_box (b : ℝ) (hb : |b| ≤ 1) (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k)
    (p : Vertex) (ds : List Step) (h : FullSpatialChunk b k m ds) :
    PathIn p ds {z | z-spatialTranslate b k m (spatialChunkIndex b k m p) ∈ endpointBox b 4 4 k m} :=
  spatial_chunk_in_box b k m hs p ds (proper_chunk_localization b hb k m ds h.1)

end GammaFPP.CrossingBridge

end OAI
