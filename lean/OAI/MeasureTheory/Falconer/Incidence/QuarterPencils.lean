import OAI.MeasureTheory.Falconer.Geometry.QuarterCoarseCover

namespace OAI

/-! Exact transport of a finite pencil family under the fixed contraction. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

noncomputable def quarterPencils (V : Space 2 → Finset (Space 2)) (z : Space 2) :
    Finset (Space 2) := (V ((4:ℝ) • z)).image (localCellLine 4 0 0)

theorem planarQuarter_left_inverse (p : Space 2) : (4:ℝ) • planarQuarter p = p := by
  rw [planarQuarter,smul_smul]
  norm_num

theorem quarterPencils_at (V : Space 2 → Finset (Space 2)) (p : Space 2) :
    quarterPencils V (planarQuarter p) = (V p).image (localCellLine 4 0 0) := by
  rw [quarterPencils,planarQuarter_left_inverse]

theorem quarterPencils_union (P : Finset (Space 2)) (V : Space 2 → Finset (Space 2)) :
    (P.image planarQuarter).biUnion (quarterPencils V) =
      (P.biUnion V).image (localCellLine 4 0 0) := by
  ext l
  constructor
  · intro hl
    obtain ⟨z,hz,hl⟩ := Finset.mem_biUnion.mp hl
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    rw [quarterPencils_at] at hl
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
    exact Finset.mem_image_of_mem _ (Finset.mem_biUnion.mpr ⟨p,hp,ha⟩)
  · intro hl
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨p,hp,ha⟩ := Finset.mem_biUnion.mp ha
    refine Finset.mem_biUnion.mpr ⟨planarQuarter p,Finset.mem_image_of_mem _ hp,?_⟩
    rw [quarterPencils_at]
    exact Finset.mem_image_of_mem _ ha

theorem quarterPencils_union_card (P : Finset (Space 2)) (V : Space 2 → Finset (Space 2)) :
    ((P.image planarQuarter).biUnion (quarterPencils V)).card = (P.biUnion V).card := by
  rw [quarterPencils_union,Finset.card_image_of_injective _ (localCellLine_injective (by norm_num) 0 0)]

theorem quarterPencils_data {δ s K : ℝ} (hδ : 0 < δ) (hs : 0 ≤ s) (hK : 1 ≤ K)
    (P : Finset (Space 2)) (V : Space 2 → Finset (Space 2))
    (hV : ∀ p ∈ P, (V p).Nonempty ∧ InBoundedLineChart (V p) ∧
      FiniteSeparatedAt δ (V p) ∧ NormalizedFiniteBallBound δ s K (V p) ∧
      ∀ l ∈ V p, |l 0| ≤ 1/2 ∧ TubeIncident δ p l) :
    ∀ z ∈ P.image planarQuarter,
      (quarterPencils V z).Nonempty ∧ InBoundedLineChart (quarterPencils V z) ∧
      FiniteSeparatedAt (δ/4) (quarterPencils V z) ∧
      NormalizedFiniteBallBound (δ/4) s (K*4^s) (quarterPencils V z) ∧
      ∀ l ∈ quarterPencils V z, |l 0| ≤ 1/2 ∧ TubeIncident (δ/4) z l := by
  intro z hz
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
  rw [quarterPencils_at]
  have hv := hV p hp
  refine ⟨hv.1.image _,localCellLine_four_chart _ hv.2.1,
    localCellLine_four_separated _ hv.2.2.1,
    localCellLine_four_regular hδ hs hK _ hv.2.2.2.1,?_⟩
  intro l hl
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
  exact ⟨(hv.2.2.2.2 a ha).1,planarQuarter_incident (hv.2.2.2.2 a ha).2⟩

end Falconer

end OAI
