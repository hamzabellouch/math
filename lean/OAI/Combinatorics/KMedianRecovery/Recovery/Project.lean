import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Data

namespace OAI

namespace MetricKMedianRecovery.PhaseLeafGeometry
universe uD uX uY
variable {D : Type uD} {X : Type uX} {Y : Type uY}
variable [PseudoMetricSpace X] [DecidableEq X]

noncomputable def Data.project {loc : D → X} {F B : Finset X} {U : ℝ}
    (d : Data loc F B U) (Q : Finset X) : Finset X :=
  (Q ∩ F) ∪ (Q \ F).image d.root

lemma Data.project_subset {loc : D → X} {F B : Finset X} {U : ℝ}
    (d : Data loc F B U) (Q : Finset X) (hQ : Q ⊆ F ∪ B) : d.project Q ⊆ F := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · exact (Finset.mem_inter.mp hx).2
  · obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hx
    exact d.root_mem b ((Finset.mem_union.mp (hQ (Finset.mem_sdiff.mp hb).1)).resolve_left
      (Finset.mem_sdiff.mp hb).2)

lemma Data.project_card {loc : D → X} {F B : Finset X} {U : ℝ}
    (d : Data loc F B U) (Q : Finset X) :
    (d.project Q).card ≤ (Q ∩ F).card+(Q \ F).card := by
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left (Finset.card_image_le) _)

lemma Data.project_member {loc : D → X} {F B : Finset X} {U : ℝ}
    (d : Data loc F B U) (Q : Finset X) (hQ : Q ⊆ F ∪ B) (j : D) (b : X) (hb : b ∈ Q) :
    ∃ a ∈ d.project Q, dist (loc j) a ≤ dist (loc j) b := by
  by_cases hbF : b ∈ F
  · exact ⟨b,Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hb,hbF⟩),le_rfl⟩
  · have hbB := (Finset.mem_union.mp (hQ hb)).resolve_left hbF
    refine ⟨d.root b,Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨b,Finset.mem_sdiff.mpr ⟨hb,hbF⟩,rfl⟩),?_⟩
    rw [d.client b hbB j]
    linarith only [d.nonneg b hbB]

lemma Data.project_nonempty [Nonempty D] {loc : D → X} {F B : Finset X} {U : ℝ}
    (d : Data loc F B U) (Q : Finset X) (hQ : Q ⊆ F ∪ B) (hne : Q.Nonempty) :
    (d.project Q).Nonempty := by
  obtain ⟨b,hb⟩ := hne
  obtain ⟨a,ha,_⟩ := d.project_member Q hQ (Classical.arbitrary D) b hb
  exact ⟨a,ha⟩

lemma Data.project_distance {loc : D → X} {F B : Finset X} {U : ℝ}
    (d : Data loc F B U) (Q : Finset X) (hQ : Q ⊆ F ∪ B) (j : D) :
    nearestDistance (loc j) (d.project Q) ≤ nearestDistance (loc j) Q := by
  by_cases hne : Q.Nonempty
  · obtain ⟨b,hb,he⟩ := nearestDistance_attained (loc j) Q hne
    obtain ⟨a,ha,hd⟩ := d.project_member Q hQ j b hb
    exact (nearestDistance_le_mem _ _ a ha).trans (hd.trans_eq he.symm)
  · have he := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [he,Data.project,Finset.empty_inter,Finset.empty_sdiff,Finset.image_empty,
      Finset.union_empty,le_refl]

omit [DecidableEq X] in

theorem Data.original_projection [PseudoMetricSpace Y] [DecidableEq Y] [Nonempty D]
    {loc : D → X} {F : Finset X} {B Q : Finset Y} {U : ℝ}
    (e : X ↪ Y) (he : ∀ x y, dist (e x) (e y) = dist x y)
    (d : Data (fun j => e (loc j)) (F.image e) B U)
    (hQ : Q ⊆ F.image e ∪ B) (hne : Q.Nonempty) :
    ∃ S : Finset X, S ⊆ F ∧ S.Nonempty ∧
      S.card ≤ (Q ∩ F.image e).card+(Q \ F.image e).card ∧
      (∀ j, nearestDistance (loc j) S ≤ nearestDistance (e (loc j)) Q) := by
  classical
  let S := F.filter (fun i => e i ∈ d.project Q)
  have hS : S.image e = d.project Q := by
    ext y
    constructor
    · rintro hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      exact (Finset.mem_filter.mp hx).2
    · intro hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp (d.project_subset Q hQ hy)
      exact Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,hy⟩,rfl⟩
  have hne' : S.Nonempty := Finset.image_nonempty.mp (hS ▸ d.project_nonempty Q hQ hne)
  refine ⟨S,Finset.filter_subset _ _,hne',?_,?_⟩
  · have hc : S.card = (d.project Q).card := by rw [← hS,Finset.card_image_of_injective _ e.injective]
    rw [hc]
    exact d.project_card Q
  · intro j
    obtain ⟨y,hy,hdy⟩ := nearestDistance_attained (e (loc j)) (d.project Q) (d.project_nonempty Q hQ hne)
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp (hS.symm ▸ hy)
    have hd : nearestDistance (loc j) S ≤ nearestDistance (e (loc j)) (d.project Q) := by
      rw [hdy,he]
      exact nearestDistance_le_mem _ _ _ hx
    exact hd.trans (d.project_distance Q hQ j)

end MetricKMedianRecovery.PhaseLeafGeometry

end OAI
