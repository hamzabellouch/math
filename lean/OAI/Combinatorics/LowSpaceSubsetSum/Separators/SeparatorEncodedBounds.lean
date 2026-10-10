import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorEncodedCheck
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorWorkBound

namespace OAI

/-! # Fixed-pair coverage and scan bounds for original indexed entries -/

noncomputable section

namespace LowSpaceSubsetSum.TopCoordinates

open SeparatorExpectation RepresentationMoments

variable {n g : ℕ} (C : TopCoordinates n g)

theorem finds_fixed_pair (families : Fin 4 → Array (Finset (Fin g))) (target : ℤ)
    (xs ys : List (Entry (Fin n))) (hsize : xs.length + ys.length ≤ 2 ^ n)
    (x y : Entry (Fin n)) (hx : x ∈ xs) (hy : y ∈ ys)
    (hw : x.value + y.value = target)
    (hc : SeparatorCheck.Covered families (C.encodeEntry x) (C.encodeEntry y)) :
    (C.check families target xs ys).accepted = true :=
  SeparatorCheck.finds_fixed_pair n families target (xs.map C.encodeEntry) (ys.map C.encodeEntry)
    (by simpa using hsize) (C.encodeEntry x) (C.encodeEntry y)
    (List.mem_map.mpr ⟨x, hx, rfl⟩) (List.mem_map.mpr ⟨y, hy, rfl⟩) hw hc

theorem coverage_probability (S : RoundedParameters g) (x y : Entry (Fin n))
    (hd : Disjoint x.mask y.mask)
    (hc : ∀ i, (SeparatorCheck.localMask i (C.encodeEntry x).mask).card = S.c i)
    (hhalf : ∀ i, S.c i + (SeparatorCheck.localMask i (C.encodeEntry y).mask).card = g / 2) :
    1 - 4 * Real.exp (-10) ≤ finiteUniformProbability
      (fun draws : SeparatorCheck.Draws g S.e S.c =>
        SeparatorCheck.Covered (SeparatorCheck.sampledFamilies draws) (C.encodeEntry x) (C.encodeEntry y)) :=
  SeparatorCheck.coverage_probability S.e S.c (C.encodeEntry x) (C.encodeEntry y)
    S.even (C.encoded_disjoint hd) hc hhalf S.count_le S.size_le S.feasible

theorem mean_scans_polynomial (S : RoundedParameters g) (u : ℕ)
    (hu : 256 ≤ u) (hnu : n ≤ u) (hgu : g + 1 ≤ u)
    (target : ℤ) (xs ys : List (Entry (Fin n)))
    (hleft : ∀ x ∈ xs, ∀ i, (SeparatorCheck.localMask i (C.encodeEntry x).mask).card = S.c i)
    (hright : ∀ x ∈ ys, ∀ i,
      (SeparatorCheck.localMask i (C.encodeEntry x).mask).card = g / 2 - S.c i) :
    mean (fun draws : IndependentFamilies g S.e S.counts =>
      ((C.check (familyArrays draws) target xs ys).scans : ℝ)) ≤
        ((xs.length + ys.length : ℕ) : ℝ) * (u : ℝ) ^ 22 *
          (2 : ℝ) ^ (((4 * g : ℕ) : ℝ) * (1 - binaryEntropy (1 / 4))) := by
  have h := S.mean_scans_polynomial n u hu hnu hgu target
    (xs.map C.encodeEntry) (ys.map C.encodeEntry) (by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
      exact hleft x hx) (by
      intro z hz
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
      exact hright y hy)
  simpa only [List.length_map, check] using h

end LowSpaceSubsetSum.TopCoordinates

end

end OAI
