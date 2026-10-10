import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.Perm.Basic
import OAI.Computability.UniqueGames.Reduction.ActualSourceLemmas

namespace OAI

section

/-! An explicit enumeration of noise indices, retaining repeated vector values.
This additional data leaves `SplitGadget` unchanged and supplies an executable
ordering for the edge list. -/

namespace UniqueGamesTheorem.Reduction.ActualSource

open scoped BigOperators

structure NoiseEnumeration {s d : Nat} (g : SplitGadget s d) where
  indices : List g.NoiseIndex
  nodup : indices.Nodup
  complete : ∀ i, i ∈ indices

namespace NoiseEnumeration

variable {s d : Nat} {g : SplitGadget s d}

noncomputable def ofFintype (g : SplitGadget s d) : NoiseEnumeration g where
  indices := Finset.univ.toList
  nodup := Finset.nodup_toList _
  complete i := by simp

theorem nonempty (e : NoiseEnumeration g) : e.indices ≠ [] := by
  intro h
  obtain ⟨i⟩ := g.noiseNonempty
  have hi := e.complete i
  simp only [h, List.not_mem_nil] at hi

theorem perm_univ (e : NoiseEnumeration g) :
    e.indices.Perm (Finset.univ : Finset g.NoiseIndex).toList := by
  apply (List.perm_ext_iff_of_nodup e.nodup (Finset.nodup_toList _)).2
  intro i
  simp [e.complete i]

theorem length_eq_card (e : NoiseEnumeration g) :
    e.indices.length = Fintype.card g.NoiseIndex := by
  simpa using e.perm_univ.length_eq

theorem sum_eq_univ (e : NoiseEnumeration g) (f : g.NoiseIndex → ℚ) :
    (e.indices.map f).sum = ∑ i, f i := by
  rw [(e.perm_univ.map f).sum_eq, Finset.sum_map_toList]

/-- A list average over index occurrences is precisely the uniform finite law. -/
theorem average_eq_expect (e : NoiseEnumeration g) (f : g.NoiseIndex → ℚ) :
    (e.indices.map f).sum / e.indices.length = Finset.univ.expect f := by
  rw [e.sum_eq_univ, e.length_eq_card, Fintype.expect_eq_sum_div_card]

end NoiseEnumeration
end UniqueGamesTheorem.Reduction.ActualSource

end

section

/-! Finite noise tables for the executable outer reduction. Positions, including
positions containing equal vectors, remain distinct sample outcomes. -/

namespace UniqueGamesTheorem.Integration.NoiseTables

open BinaryLinear UniqueGamesTheorem.Reduction.ActualSource

variable {s d : Nat}

/-- Reindexing changes the names of outcomes, retaining their uniform law. -/
def reindex (g : SplitGadget s d) {I : Type} [Fintype I] [Nonempty I]
    (e : I ≃ g.NoiseIndex) : SplitGadget s d where
  f := g.f
  equivariant := g.equivariant
  NoiseIndex := I
  noiseFintype := inferInstance
  noiseNonempty := inferInstance
  noise i := g.noise (e i)

theorem reindex_stabilityError (g : SplitGadget s d)
    {I : Type} [Fintype I] [Nonempty I] (e : I ≃ g.NoiseIndex) :
    (reindex g e).stabilityError = g.stabilityError := by
  apply Fintype.expect_equiv ((Equiv.refl (Ambient s d)).prodCongr e)
  intro x
  rfl

theorem reindex_kernelProbability (g : SplitGadget s d)
    {I : Type} [Fintype I] [Nonempty I] (e : I ≃ g.NoiseIndex)
    {P : Type} [AddCommGroup P] [Module F2 P]
    (S : Ambient s d →ₗ[F2] P) :
    SplitGadget.kernelProbability (reindex g e) S =
      SplitGadget.kernelProbability g S := by
  classical
  apply Fintype.expect_equiv e
  intro i
  rfl

/-- Only a nonempty finite list of binary vectors is required as static noise
data. The correcting function is a separate witness used in the proof. -/
structure Table (s d : Nat) where
  vectors : List (Ambient s d)
  nonempty : vectors ≠ []

namespace Table

def gadget (T : Table s d) (f : Ambient s d → Alphabet s)
    (hf : ∀ x c, f (x + (c, 0)) = f x + c) : SplitGadget s d where
  f := f
  equivariant := hf
  NoiseIndex := Fin T.vectors.length
  noiseFintype := inferInstance
  noiseNonempty := ⟨⟨0, List.length_pos_iff.mpr T.nonempty⟩⟩
  noise := T.vectors.get

def ofEnumeration (g : SplitGadget s d) (en : NoiseEnumeration g) : Table s d where
  vectors := en.indices.map g.noise
  nonempty := by simpa using en.nonempty

@[simp] theorem ofEnumeration_length (g : SplitGadget s d) (en : NoiseEnumeration g) :
    (ofEnumeration g en).vectors.length = en.indices.length := by
  simp [ofEnumeration]

/-- The inverse equivalence is used only to prove the probability identity;
the forward noise lookup is ordinary finite-list indexing. -/
noncomputable def positionEquiv (g : SplitGadget s d) (en : NoiseEnumeration g) :
    Fin (ofEnumeration g en).vectors.length ≃ g.NoiseIndex := by
  classical
  exact (finCongr (ofEnumeration_length g en)).trans
    (en.nodup.getEquivOfForallMemList en.indices en.complete)

theorem noise_positionEquiv (g : SplitGadget s d) (en : NoiseEnumeration g)
    (i : Fin (ofEnumeration g en).vectors.length) :
    ((ofEnumeration g en).gadget g.f g.equivariant).noise i =
      g.noise (positionEquiv g en i) := by
  change (en.indices.map g.noise)[i.val] = g.noise en.indices[i.val]
  exact List.getElem_map _

theorem stabilityError_ofEnumeration (g : SplitGadget s d) (en : NoiseEnumeration g) :
    ((ofEnumeration g en).gadget g.f g.equivariant).stabilityError =
      g.stabilityError := by
  apply Fintype.expect_equiv
    ((Equiv.refl (Ambient s d)).prodCongr (positionEquiv g en))
  intro x
  change (if g.f (x.1 + _) = g.f x.1 then (0 : ℚ) else 1) = _
  rw [noise_positionEquiv]
  rfl

theorem kernelProbability_ofEnumeration (g : SplitGadget s d)
    (en : NoiseEnumeration g) {P : Type} [AddCommGroup P] [Module F2 P]
    (S : Ambient s d →ₗ[F2] P) :
    SplitGadget.kernelProbability ((ofEnumeration g en).gadget g.f g.equivariant) S =
      SplitGadget.kernelProbability g S := by
  classical
  apply Fintype.expect_equiv (positionEquiv g en)
  intro i
  rw [noise_positionEquiv]

/-- Exact table conversion retains both mathematical gadget guarantees. -/
theorem guarantees_ofEnumeration (g : SplitGadget s d) (en : NoiseEnumeration g)
    {ζ ν : ℚ} {r : Nat}
    (hstable : g.stabilityError ≤ ζ)
    (hdisp : ∀ (P : Type) [AddCommGroup P] [Module F2 P]
      (S : Ambient s d →ₗ[F2] P),
      r ≤ Module.finrank F2 (S.comp (alphabetEmbedding s d)).range →
      SplitGadget.kernelProbability g S ≤ ν) :
    ((ofEnumeration g en).gadget g.f g.equivariant).stabilityError ≤ ζ ∧
      ∀ (P : Type) [AddCommGroup P] [Module F2 P]
        (S : Ambient s d →ₗ[F2] P),
        r ≤ Module.finrank F2 (S.comp (alphabetEmbedding s d)).range →
        SplitGadget.kernelProbability
          ((ofEnumeration g en).gadget g.f g.equivariant) S ≤ ν := by
  constructor
  · simpa only [stabilityError_ofEnumeration] using hstable
  · intro P _ _ S hS
    rw [kernelProbability_ofEnumeration]
    exact hdisp P S hS

end Table
end UniqueGamesTheorem.Integration.NoiseTables

end

end OAI
