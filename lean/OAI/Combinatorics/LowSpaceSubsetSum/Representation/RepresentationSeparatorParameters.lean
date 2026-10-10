import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorParameters
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationTopCoordinates
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorEncodedBounds

namespace OAI

/-! # Separator parameters for the actual guessed representation layout -/

noncomputable section

namespace LowSpaceSubsetSum.RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

def separatorParameters (guesses : Guesses n) (hn : 2200 ≤ n) :
    SeparatorExpectation.RoundedParameters (2 * blockHalf n 0) :=
  SeparatorParameters.rounded (2 * blockHalf n 0) (guesses 0).val
    (by simp only [blockHalf, Matrix.cons_val_zero]; omega)
    (by simp)
    (by
      have h := (Finset.mem_Icc.mp (guesses 0).property).2
      change (guesses 0).val ≤ mixerSize n / 4 at h
      simp only [mixerSize, blockHalf, Matrix.cons_val_zero] at h ⊢
      omega)
    (by
      have h := (Finset.mem_Icc.mp (guesses 0).property).1
      change (mixerSize n + 5) / 6 ≤ (guesses 0).val at h
      simp only [mixerSize, blockHalf, Matrix.cons_val_zero] at h ⊢
      omega)

theorem collected_separator_count (z : Layout n) (guesses : Guesses n) (f : R.Partitions z)
    (background : Fin n → Fin 2 × Fin 4) (side : Fin 2) (hn : 2200 ≤ n)
    (D : RepresentationParentData n) (hleaves : D.leaves = R.rawLeaf z guesses f background side)
    (B : ℕ) (e : Entry (Fin n)) (he : e ∈ (D.entries B).toList) (i : Fin 4) :
    (SeparatorCheck.localMask i ((R.topCoordinates z f).encodeEntry e).mask).card =
      if side = 0 then (separatorParameters guesses hn).c i
      else (2 * blockHalf n 0) / 2 - (separatorParameters guesses hn).c i := by
  rw [R.collected_local_count z guesses f background side D hleaves B e he i]
  simp [separatorParameters, SeparatorParameters.rounded]

theorem collected_mean_scans (z : Layout n) (guesses : Guesses n) (f : R.Partitions z)
    (background : Fin n → Fin 2 × Fin 4) (hn : 2200 ≤ n)
    (left right : RepresentationParentData n)
    (hleft : left.leaves = R.rawLeaf z guesses f background 0)
    (hright : right.leaves = R.rawLeaf z guesses f background 1)
    (B u : ℕ) (hu : 256 ≤ u) (hnu : n ≤ u) (hgu : 2 * blockHalf n 0 + 1 ≤ u)
    (target : ℤ) :
    let S := separatorParameters guesses hn
    RepresentationMoments.mean (fun draws : SeparatorExpectation.IndependentFamilies
      (2 * blockHalf n 0) S.e S.counts =>
      (((R.topCoordinates z f).check (SeparatorExpectation.familyArrays draws) target
        (left.entries B).toList (right.entries B).toList).scans : ℝ)) ≤
      (((left.entries B).size + (right.entries B).size : ℕ) : ℝ) * (u : ℝ) ^ 22 *
        (2 : ℝ) ^ (((4 * (2 * blockHalf n 0) : ℕ) : ℝ) * (1 - binaryEntropy (1 / 4))) := by
  dsimp only
  apply (R.topCoordinates z f).mean_scans_polynomial (separatorParameters guesses hn)
    u hu hnu hgu target (left.entries B).toList (right.entries B).toList
  · intro x hx i
    exact R.collected_separator_count z guesses f background 0 hn left hleft B x hx i
  · intro x hx i
    exact R.collected_separator_count z guesses f background 1 hn right hright B x hx i

end LowSpaceSubsetSum.RepresentationSetup

end

end OAI
