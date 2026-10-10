import Mathlib.Data.Fintype.Perm
import OAI.Combinatorics.BalancedRyser.Local.Local

namespace OAI

namespace Balanced.Local
noncomputable section
attribute [local instance] Classical.propDecidable

namespace EqualityPattern

variable {b κ : ℕ}

def reindex (P : EqualityPattern b κ) (σ : Equiv.Perm (Fin b)) :
    EqualityPattern b κ where
  classOf i := P.classOf (σ i)
  everyClass := by
    intro c
    obtain ⟨⟨i, j⟩, hc⟩ := P.everyClass c
    exact ⟨(σ.symm i, j), by simpa using hc⟩
  withinTuple i := P.withinTuple (σ i)
  pairOverlap i j hij := P.pairOverlap (σ i) (σ j) (fun h => hij (σ.injective h))

end EqualityPattern

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ} (P : EqualityPattern b κ) (σ : Equiv.Perm (Fin b))

def reindexAssignment (a : DirectionAssignment F b κ) : DirectionAssignment F b κ :=
  (a.1 ∘ σ, a.2)

def reindexBits (bits : Bits b) : Bits b := bits ∘ σ

def reindexPositions : (Fin b × Fin 4) ≃ (Fin b × Fin 4) :=
  Equiv.prodCongr σ (Equiv.refl _)

omit [Field F] [Fintype F] [DecidableEq F] in
theorem eligible_reindex (a : DirectionAssignment F b κ) :
    Eligible (P.reindex σ) (reindexAssignment σ a) ↔ Eligible P a := by
  constructor
  · rintro ⟨ht, hg, he⟩
    refine ⟨?_, hg, ?_⟩
    · intro i j hij
      have h := ht (a₁ := σ.symm i) (a₂ := σ.symm j) (by simpa [reindexAssignment] using hij)
      exact σ.symm.injective h
    · intro i j
      simpa [reindexAssignment, EqualityPattern.reindex] using he (σ.symm i) j
  · rintro ⟨ht, hg, he⟩
    exact ⟨ht.comp σ.injective, hg, fun i j => he (σ i) j⟩

omit [Field F] [Fintype F] [DecidableEq F] in
theorem prescribedTuple_reindex (a : DirectionAssignment F b κ)
    (bits : Bits b) (i : Fin b) :
    prescribedTuple (P.reindex σ) (reindexAssignment σ a) (reindexBits σ bits) i =
      prescribedTuple P a bits (σ i) := rfl

omit [Fintype F] [DecidableEq F] in
theorem prescribedPoint_reindex (a : DirectionAssignment F b κ)
    (bits : Bits b) (M : MergedPairs F) (ij : Fin b × Fin 4) :
    prescribedPoint (P.reindex σ) (reindexAssignment σ a) (reindexBits σ bits) M ij =
      prescribedPoint P a bits M (reindexPositions σ ij) := rfl

omit [Fintype F] [DecidableEq F] in
theorem aligned_reindex (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (M : MergedPairs F) :
    Aligned (P.reindex σ) (reindexAssignment σ a) (reindexBits σ bits) p M ↔
      Aligned P a bits p M := by
  constructor
  · intro h ij
    have hh := h ((reindexPositions σ).symm ij)
    rw [prescribedPoint_reindex, Equiv.apply_symm_apply] at hh
    simpa [reindexPositions, reindexAssignment] using hh
  · intro h ij
    exact h (reindexPositions σ ij)

theorem admissible_reindex (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (M : MergedPairs F) :
    Admissible (P.reindex σ) (reindexAssignment σ a) (reindexBits σ bits) p M ↔
      Admissible P a bits p M := by
  constructor
  · rintro ⟨ha, hi, hp, hc, hm⟩
    refine ⟨(aligned_reindex P σ a bits p M).mp ha, ?_, ?_, ?_, hm⟩
    · intro ij kl h
      have hh := hi (a₁ := (reindexPositions σ).symm ij)
        (a₂ := (reindexPositions σ).symm kl) (by
          simpa only [prescribedPoint_reindex, Equiv.apply_symm_apply] using h)
      exact (reindexPositions σ).symm.injective hh
    · intro ij
      simpa only [prescribedPoint_reindex, Equiv.apply_symm_apply]
        using hp ((reindexPositions σ).symm ij)
    · intro i
      simpa [reindexAssignment] using hc (σ.symm i)
  · rintro ⟨ha, hi, hp, hc, hm⟩
    refine ⟨(aligned_reindex P σ a bits p M).mpr ha,
      hi.comp (reindexPositions σ).injective, ?_, ?_, hm⟩
    · intro ij
      exact hp (reindexPositions σ ij)
    · intro i
      exact hc (σ i)

omit [Fintype F] in
theorem prescribedDesignated_reindex (a : DirectionAssignment F b κ)
    (bits : Bits b) (M : MergedPairs F) :
    prescribedDesignated (P.reindex σ) (reindexAssignment σ a) (reindexBits σ bits) M =
      prescribedDesignated P a bits M := by
  unfold prescribedDesignated
  change Finset.univ.image (prescribedPoint P a bits M ∘ reindexPositions σ) = _
  rw [← Finset.image_image, Finset.image_univ_equiv]

theorem prescribedPartners_reindex (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (M : MergedPairs F) :
    prescribedPartners (P.reindex σ) (reindexAssignment σ a) (reindexBits σ bits) p M =
      prescribedPartners P a bits p M := by
  unfold prescribedPartners
  rw [prescribedDesignated_reindex]

omit P [Fintype F] in
theorem targetLines_reindex (a : DirectionAssignment F b κ) (p : Point F) :
    Finset.univ.image (fun i => lineThrough ((reindexAssignment σ a).1 i) p) =
      Finset.univ.image (fun i => lineThrough (a.1 i) p) := by
  change Finset.univ.image ((fun i => lineThrough (a.1 i) p) ∘ σ) = _
  rw [← Finset.image_image, Finset.image_univ_equiv]

omit P in
theorem allowedPiece_reindex (a : DirectionAssignment F b κ)
    (p : Point F) (M : MergedPairs F) (x : LocalPiece F) :
    AllowedPiece (reindexAssignment σ a) p M x ↔ AllowedPiece a p M x := by
  rcases x with U | l | d
  · rfl
  · change l ∉ _ ∪ constituentLines M ↔ l ∉ _ ∪ constituentLines M
    rw [targetLines_reindex]
  · rfl

theorem badCover_reindex (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (M : MergedPairs F) :
    BadCover (P.reindex σ) (reindexAssignment σ a) (reindexBits σ bits) p M ↔
      BadCover P a bits p M := by
  simp only [BadCover, prescribedDesignated_reindex, prescribedPartners_reindex,
    allowedPiece_reindex]

theorem admissibleBadCover_reindex (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (M : MergedPairs F) :
    AdmissibleBadCover (P.reindex σ) (reindexAssignment σ a) (reindexBits σ bits) p M ↔
      AdmissibleBadCover P a bits p M := by
  simp only [AdmissibleBadCover, admissible_reindex, badCover_reindex]

end
end Balanced.Local

end OAI
