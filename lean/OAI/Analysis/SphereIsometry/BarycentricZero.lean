import OAI.Analysis.SphereIsometry.BarycentricFlags
import OAI.Analysis.SphereIsometry.SubdivisionData

namespace OAI

/-!
# The zero-dimensional subdivision and its empty codimension-one face

The subdivision of a zero-dimensional complex has one vertex for each old
singleton face. In particular, iterated subdivision of the point has one
top face, incident to its unique empty codimension-one face.
-/

noncomputable section

namespace Tingley.FiniteComplex

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {K : FiniteComplex V}

@[simp] theorem incidentTop_empty (K : FiniteComplex V) (m : ℕ) :
    K.incidentTop m ∅ = K.topCells m := by
  classical
  ext s
  simp [incidentTop]

theorem sd_topCells_zero_card (hK : K.CardBound 0) :
    (K.sd.topCells 0).card = (K.topCells 0).card := by
  classical
  let v : ∀ s ∈ K.topCells 0, FaceVertex K := fun s hs =>
    ⟨s, (mem_topCells.mp hs).1,
      Finset.card_pos.mp (by have h := (mem_topCells.mp hs).2; omega)⟩
  let f : ∀ s ∈ K.topCells 0, Finset (FaceVertex K) := fun s hs => {v s hs}
  have hf : ∀ s hs, f s hs ∈ K.sd.topCells 0 := by
    intro s hs
    apply mem_topCells.mpr
    constructor
    · apply mem_sd_iff.mpr
      change K.chain {v s hs}
      simp [chain]
    · change ({v s hs} : Finset (FaceVertex K)).card = 0 + 1
      simp
  have hinj : ∀ s hs t ht, f s hs = f t ht → s = t := by
    intro s hs t ht h
    have hv : v s hs = v t ht := Finset.singleton_inj.mp h
    exact congrArg Subtype.val hv
  have hsurj : ∀ c ∈ K.sd.topCells 0, ∃ s hs, f s hs = c := by
    intro c hc
    obtain ⟨hcface, hccard⟩ := mem_topCells.mp hc
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp (show c.card = 1 by omega)
    have hacard : a.val.card = 0 + 1 := by
      have hlo := Finset.card_pos.mpr a.property.2
      have hhi := hK a.val a.property.1
      omega
    have ha : a.val ∈ K.topCells 0 := mem_topCells.mpr ⟨a.property.1, hacard⟩
    refine ⟨a.val, ha, ?_⟩
    change ({v a.val ha} : Finset (FaceVertex K)) = {a}
    congr 1
  exact (Finset.card_bij f hf hinj hsurj).symm

theorem sd_pure_zero (hK : K.Pure 0) : K.sd.Pure 0 := by
  classical
  intro c hc
  rcases c.eq_empty_or_nonempty with rfl | hne
  · obtain ⟨s, hs, _⟩ := hK ∅ K.empty_mem
    let a : FaceVertex K := ⟨s, (mem_topCells.mp hs).1,
      Finset.card_pos.mp (by have h := (mem_topCells.mp hs).2; omega)⟩
    refine ⟨{a}, mem_topCells.mpr ⟨mem_sd_iff.mpr ?_, by simp⟩,
      Finset.empty_subset _⟩
    simp [chain]
  · refine ⟨c, mem_topCells.mpr ⟨hc, ?_⟩, Finset.Subset.refl _⟩
    have hlo := Finset.card_pos.mpr hne
    have hhi := sd_cardBound hK.cardBound c hc
    omega

end Tingley.FiniteComplex

namespace Tingley

theorem iter_topCells_zero_card (k : ℕ) : (topCells 0 k).card = 1 := by
  classical
  induction k with
  | zero =>
      change ((FiniteComplex.full : FiniteComplex (Fin 1)).topCells 0).card = 1
      have hfull : (FiniteComplex.full : FiniteComplex (Fin 1)).topCells 0 =
          {Finset.univ} := by
        ext s
        simp only [FiniteComplex.mem_topCells, FiniteComplex.mem_full,
          true_and, Finset.mem_singleton]
        constructor
        · intro hs
          apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
          simpa using hs.ge
        · rintro rfl
          simp
      rw [hfull]
      simp
  | succ k ih =>
      change (((iterData (Fin 1) k).complex).sd.topCells 0).card = 1
      have hK : (iterData (Fin 1) k).complex.CardBound 0 := by
        intro s hs
        exact iter_card_le (m := 0) (k := k) hs
      rw [FiniteComplex.sd_topCells_zero_card hK]
      exact ih

theorem iter_incidentTop_zero_card (k : ℕ) {c : Finset (IterVertex 0 k)}
    (hc : c ∈ codimFaces 0 k) : (incidentTop 0 k c).card = 1 := by
  have hczero : c = ∅ := Finset.card_eq_zero.mp (mem_codimFaces.mp hc).2
  subst c
  change ((iterData (Fin 1) k).complex.incidentTop 0 ∅).card = 1
  rw [FiniteComplex.incidentTop_empty]
  exact iter_topCells_zero_card k

end Tingley

end

end OAI
