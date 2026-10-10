import OAI.Analysis.MarkovType.SubdivisionSameSign
import OAI.Analysis.MarkovType.SubdivisionMergeCoordinates
import OAI.Analysis.MarkovType.SubdivisionNearIsometry
import OAI.Analysis.MarkovType.CoordinateFactorization

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

namespace SpreadingModel

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem averaged_mergeAt (S : SpreadingModel Y) (i : ℕ) (x : C00) :
    S.averagedSeminorm (C00.mergeAt i x) ≤ S.averagedSeminorm x := by
  obtain ⟨left, right, a, b, hi, hx⟩ := Subdivision.exists_context x i
  calc
    S.averagedSeminorm (C00.mergeAt i x) =
        S.averagedSeminorm
          (C00.mergeAt left.length (Subdivision.ofList (left ++ ([a, b] ++ right)))) := by
      rw [hi, hx]
    _ = S.averagedSeminorm (Subdivision.ofList (left ++ ([a + b] ++ right))) := by
      rw [Subdivision.mergeAt_context]
    _ ≤ S.averagedSeminorm (Subdivision.ofList (left ++ ([a, b] ++ right))) :=
      S.averaged_merge_context left right a b
    _ = S.averagedSeminorm x := congrArg S.averagedSeminorm hx

def orderedNorm (S : SpreadingModel Y) : OrderedNorm where
  toSeminorm := S.averagedSeminorm
  definite := S.averaged_definite
  spreading := S.averaged_spreading
  merge_le := S.averaged_mergeAt

@[simp] theorem orderedNorm_apply (S : SpreadingModel Y) (x : C00) :
    S.orderedNorm x = S.averagedSeminorm x := rfl

theorem orderedNorm_prefix_lower (S : SpreadingModel Y) (x : C00) (k : ℕ) :
    S.d * |prefixCut x k| ≤ S.orderedNorm x := S.averaged_prefix_lower x k

theorem orderedNorm_subdivide (S : SpreadingModel Y) (J : ℕ → ℕ)
    (hJ : ∀ i, 0 < J i) (x : C00) :
    S.orderedNorm (C00.subdivide J x) = S.orderedNorm x :=
  S.averaged_subdivide J hJ x

theorem orderedNorm_uniformSubdivision (S : SpreadingModel Y) (q : ℕ)
    (hq : 0 < q) (x : C00) :
    S.orderedNorm (C00.uniformSubdivision q x) = S.orderedNorm x :=
  S.orderedNorm_subdivide (fun _ => q) (fun _ => hq) x

theorem orderedNorm_scaled_uniform (S : SpreadingModel Y) (q : ℕ)
    (hq : 0 < q) (x : C00) :
    S.orderedNorm ((q : ℝ) • C00.uniformSubdivision q x) = (q : ℝ) * S.orderedNorm x := by
  rw [OrderedNorm.smul, abs_of_nonneg (Nat.cast_nonneg q),
    S.orderedNorm_uniformSubdivision q hq x]

theorem orderedNorm_representable (S : SpreadingModel Y) :
    CoordinatesRepresentable Y S.orderedNorm := by
  apply CoordinatesRepresentable.of_factorization S.orderedNorm S.p
  · intro m η hη
    obtain ⟨q, hq, hqbound⟩ := S.exists_uniform_nearIsometry m hη
    exact ⟨q * m, C00.uniformArrayMap q m, hqbound⟩
  · exact S.embeddings

end SpreadingModel

theorem exists_orderedNorm_of_spreadingModel
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (S : SpreadingModel Y) :
    ∃ N : OrderedNorm, CoordinatesRepresentable Y N :=
  ⟨S.orderedNorm, S.orderedNorm_representable⟩

end MarkovSuperreflexivity

end

end OAI
