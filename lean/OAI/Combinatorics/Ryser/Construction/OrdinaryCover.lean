import OAI.Combinatorics.Ryser.Construction.LabelAction
import OAI.Combinatorics.Ryser.Construction.CoverPencil
import Mathlib.Data.Finset.Sum

namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {k F G : Type*} [instFieldk : Field k] [instFieldF : Field F]
variable [instDecidableEqk : DecidableEq k] [DecidableEq F] [instDecidableEqG : DecidableEq G]

def ordinaryLines (data : ConfigurationData k F G)
    (C : Finset (Vertex (k := k) data.altered)) : Finset (AffineLine F) := C.toLeft

@[simp] theorem mem_ordinaryLines (data : ConfigurationData k F G)
    (C : Finset (Vertex (k := let _ := instFieldk; let _ := instFieldF; let _ := instDecidableEqk; let _ := instDecidableEqG; k) data.altered)) (ell : AffineLine F) :
    ell ∈ ordinaryLines data C ↔ ordinaryVertex data ell ∈ C :=
  Finset.mem_toLeft

theorem ordinaryVertex_injective (data : ConfigurationData k F G) :
    Function.Injective (ordinaryVertex data) := let _ := instFieldk; let _ := instFieldF; let _ := instDecidableEqk; let _ := instDecidableEqG; by
  intro l m hlm
  exact Sum.inl.inj hlm

theorem ordinaryLines_card_le (data : ConfigurationData k F G)
    (C : Finset (Vertex (k := let _ := instFieldk; let _ := instFieldF; let _ := instDecidableEqk; let _ := instDecidableEqG; k) data.altered)) :
    (ordinaryLines data C).card ≤ C.card := Finset.card_toLeft_le

variable [Fintype F]

def forcedPencilVertices (data : ConfigurationData k F G)
    (B : Finset (AffineLine F)) (p : ProjectivePoint F) :
    Finset (Vertex (k := k) data.altered) :=
  (affinePencil p \ B).image (ordinaryVertex data)

theorem card_forcedPencilVertices (data : ConfigurationData k F G)
    (B : Finset (AffineLine F)) (p : ProjectivePoint F) :
    (forcedPencilVertices data B p).card = (affinePencil p \ B).card :=
  Finset.card_image_of_injective _ (ordinaryVertex_injective data)

@[simp] theorem ordinaryVertex_mem_forcedPencilVertices_iff
    (data : ConfigurationData k F G) (B : Finset (AffineLine F))
    (p : ProjectivePoint F) (ell : AffineLine F) :
    ordinaryVertex data ell ∈ forcedPencilVertices data B p ↔
      ell ∈ affinePencil p ∧ ell ∉ B := by
  constructor
  · intro h
    obtain ⟨l, hl, heq⟩ := Finset.mem_image.mp h
    have hlell : l = ell := ordinaryVertex_injective data heq
    subst l
    exact Finset.mem_sdiff.mp hl
  · intro h
    exact Finset.mem_image_of_mem _ (Finset.mem_sdiff.mpr h)

theorem ordinaryLines_offPencil_add_onPencil_le
    (data : ConfigurationData k F G)
    (C : Finset (Vertex (k := k) data.altered)) (p : ProjectivePoint F) :
    (ordinaryLines data C \ affinePencil p).card +
      (ordinaryLines data C ∩ affinePencil p).card ≤ C.card := by
  rw [Finset.card_sdiff_add_card_inter]
  exact ordinaryLines_card_le data C

variable [Fintype G]

theorem ordinaryLines_cover_ordinaryPoints (data : ConfigurationData k F G)
    (C : Finset (Vertex (k := k) data.altered))
    (hC : IsCover (hypergraph data) C) :
    ∀ x ∈ data.ordinaryPoints, ∃ ell ∈ ordinaryLines data C, Incidence x ell := by
  intro x hx
  have he : ordinaryEdge data x ∈ hypergraph data :=
    (mem_hypergraph data _).2 (Or.inl ⟨x, hx, rfl⟩)
  obtain ⟨v, hvC, hve⟩ := hC (ordinaryEdge data x) he
  obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hve
  exact ⟨lineThrough d x, (mem_ordinaryLines data C _).2 hvC,
    incidence_lineThrough d x⟩

theorem ordinaryVertex_mem_cover_of_pencil_survivors
    (data : ConfigurationData k F G)
    (C : Finset (Vertex (k := k) data.altered))
    (hC : IsCover (hypergraph data) C)
    (p : ProjectivePoint F) (ell : AffineLine F)
    (hpell : ProjectiveIncidence p (some ell))
    (hmany : 1 + (ordinaryLines data C \ affinePencil p).card <
      (data.ordinaryPoints ∩ linePoints ell).card) :
    ordinaryVertex data ell ∈ C := by
  apply (mem_ordinaryLines data C ell).1
  exact mem_cover_of_pencil_survivors data.ordinaryPoints (ordinaryLines data C)
    p ell (ordinaryLines_cover_ordinaryPoints data C hC) hpell hmany

theorem forcedPencilVertices_subset_cover
    (data : ConfigurationData k F G)
    (C : Finset (Vertex (k := k) data.altered))
    (hC : IsCover (hypergraph data) C)
    (B : Finset (AffineLine F)) (p : ProjectivePoint F)
    (hmany : ∀ ell ∈ affinePencil p, ell ∉ B →
      1 + (ordinaryLines data C \ affinePencil p).card <
        (data.ordinaryPoints ∩ linePoints ell).card) :
    forcedPencilVertices data B p ⊆ C := by
  intro v hv
  obtain ⟨ell, hell, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨hpell, hnot⟩ := Finset.mem_sdiff.mp hell
  exact ordinaryVertex_mem_cover_of_pencil_survivors data C hC p ell
    ((mem_affinePencil _ _).1 hpell) (hmany ell hpell hnot)

end RyserCoveringCounterexample.Construction

end OAI
