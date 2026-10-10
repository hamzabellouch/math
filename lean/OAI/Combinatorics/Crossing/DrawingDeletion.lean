import OAI.Combinatorics.Crossing.DrawingRestriction

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators Classical
variable {m n : ℕ}

def deleteRightVertex (D : AdmissibleDrawing m (n+1)) (v : Fin (n+1)) : AdmissibleDrawing m n :=
  restrictDrawing D (Fin.succAboveOrderEmb v).toEmbedding

theorem crossing_survives_deletion_iff (D : AdmissibleDrawing m (n+1))
    (v : Fin (n+1)) (x : Plane) (e f : BipartiteEdge m (n+1)) (hef : e ≠ f)
    (he : x ∈ edgeInterior D.toContinuousDrawing e) (hf : x ∈ edgeInterior D.toContinuousDrawing f) :
    x ∈ crossingPoints (deleteRightVertex D v).toContinuousDrawing ↔ e.2 ≠ v ∧ f.2 ≠ v := by
  constructor
  · rintro ⟨a,b,hab,ha,hb⟩
    let emb := (Fin.succAboveOrderEmb v).toEmbedding
    have hab' : restrictEdge emb a ≠ restrictEdge emb b := (restrictEdge emb).injective.ne hab
    have hae : e = restrictEdge emb a ∨ e = restrictEdge emb b :=
      (crossing_incident_iff D x (restrictEdge emb a) (restrictEdge emb b) hab' ha hb e).mp he
    have haf : f = restrictEdge emb a ∨ f = restrictEdge emb b :=
      (crossing_incident_iff D x (restrictEdge emb a) (restrictEdge emb b) hab' ha hb f).mp hf
    constructor
    · rcases hae with rfl | rfl <;> exact Fin.succAbove_ne v _
    · rcases haf with rfl | rfl <;> exact Fin.succAbove_ne v _
  · rintro ⟨hev,hfv⟩
    obtain ⟨a,ha⟩ := Fin.exists_succAbove_eq hev
    obtain ⟨b,hb⟩ := Fin.exists_succAbove_eq hfv
    let emb := (Fin.succAboveOrderEmb v).toEmbedding
    have hea : restrictEdge emb (e.1,a) = e := Prod.ext rfl ha
    have hfb : restrictEdge emb (f.1,b) = f := Prod.ext rfl hb
    refine ⟨(e.1,a),(f.1,b),?_,?_,?_⟩
    · intro hab
      apply hef
      rw [← hea, ← hfb, hab]
    · change x ∈ edgeInterior D.toContinuousDrawing (restrictEdge emb (e.1,a))
      rwa [hea]
    · change x ∈ edgeInterior D.toContinuousDrawing (restrictEdge emb (f.1,b))
      rwa [hfb]

theorem crossing_columns_ne (D : AdmissibleDrawing m n) (hnorm : NoAdjacentCrossings D)
    (x : Plane) (e f : BipartiteEdge m n) (hef : e ≠ f)
    (he : x ∈ edgeInterior D.toContinuousDrawing e) (hf : x ∈ edgeInterior D.toContinuousDrawing f) :
    e.2 ≠ f.2 := by
  intro hcol
  have hh : x ∈ edgeInterior D.toContinuousDrawing e ∩ edgeInterior D.toContinuousDrawing f := ⟨he,hf⟩
  rw [hnorm e f hef (Or.inr hcol)] at hh
  exact hh

theorem two_excluded_indices (a b : Fin (n+1)) (hab : a ≠ b) :
    (∑ v : Fin (n+1), if a ≠ v ∧ b ≠ v then (1 : ℕ) else 0) = (n+1)-2 := by
  have he : (Finset.univ.filter (fun v : Fin (n+1) => a ≠ v ∧ b ≠ v)) =
      (Finset.univ.erase a).erase b := by
    ext v
    simp [ne_comm, and_comm]
  rw [← Finset.card_filter, he, Finset.card_erase_of_mem (by simp [hab.symm]),
    Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]
  omega

theorem crossing_deletion_multiplicity (D : AdmissibleDrawing m (n+1))
    (hnorm : NoAdjacentCrossings D) (x : Plane) (hx : x ∈ crossingPoints D.toContinuousDrawing) :
    (∑ v : Fin (n+1), if x ∈ crossingPoints (deleteRightVertex D v).toContinuousDrawing
      then (1 : ℕ) else 0) = (n+1)-2 := by
  obtain ⟨e,f,hef,he,hf⟩ := hx
  simp_rw [crossing_survives_deletion_iff D _ x e f hef he hf]
  exact two_excluded_indices e.2 f.2 (crossing_columns_ne D hnorm x e f hef he hf)

end Zarankiewicz

end

end OAI
