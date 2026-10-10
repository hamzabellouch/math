import OAI.Combinatorics.Ryser.LineCover.Overlap
import OAI.Combinatorics.Ryser.Geometry.Basic
import OAI.Combinatorics.Ryser.Incidence.PruningCore

namespace OAI

open scoped BigOperators Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [instFieldF : Field F] [instFintypeF : Fintype F] [DecidableEq F]

def projectivePointsOf (X : Finset (Point F)) : Finset (ProjectivePoint F) :=
  X.image Sum.inl

def projectiveLinesOf (L : Finset (AffineLine F)) : Finset (ProjectiveLine F) :=
  L.image some

@[simp] theorem card_projectivePointsOf (X : Finset (Point F)) :
    (projectivePointsOf X).card = X.card := let _ := instFieldF; let _ := instFintypeF;
  Finset.card_image_of_injective X Sum.inl_injective

@[simp] theorem card_projectiveLinesOf (L : Finset (AffineLine F)) :
    (projectiveLinesOf L).card = L.card := let _ := instFieldF; let _ := instFintypeF;
  Finset.card_image_of_injective L (Option.some_injective _)

theorem leftDegree_projectiveLinesOf (L : Finset (AffineLine F)) (x : Point F) :
    Incidence.leftDegree ProjectiveIncidence (projectiveLinesOf L) (Sum.inl x) =
      multiplicity Incidence L x := let _ := instFintypeF; by
  unfold Incidence.leftDegree projectiveLinesOf multiplicity
  have houter :
      @Finset.filter _ (ProjectiveIncidence (Sum.inl x))
        (fun l => Classical.propDecidable (ProjectiveIncidence (Sum.inl x) l))
        (L.image some) = (L.image some).filter (ProjectiveIncidence (Sum.inl x)) :=
    Finset.filter_congr_decidable _ _ _
  have hinner :
      @Finset.filter _ (Incidence x) (fun l => Classical.propDecidable (Incidence x l)) L =
        L.filter (Incidence x) := Finset.filter_congr_decidable _ _ _
  rw [houter, hinner, Finset.filter_image, Finset.card_image_of_injective _ (Option.some_injective _)]
  congr 1

theorem incidenceCount_projective_lifts (X : Finset (Point F))
    (L : Finset (AffineLine F)) :
    Incidence.incidenceCount ProjectiveIncidence (projectivePointsOf X)
      (projectiveLinesOf L) = ∑ x ∈ X, multiplicity Incidence L x := by
  unfold Incidence.incidenceCount projectivePointsOf
  rw [Finset.sum_image]
  · exact Finset.sum_congr rfl (fun x _ => leftDegree_projectiveLinesOf L x)
  · intro x hx y hy hxy
    exact Sum.inl.inj hxy

theorem multiplicity_eq_finite_pencil (L : Finset (AffineLine F)) (x : Point F) :
    multiplicity Incidence L x =
      (L.filter fun l => ProjectiveIncidence (Sum.inl x) (some l)).card := let _ := instFintypeF; by
  unfold multiplicity
  have hfilter :
      @Finset.filter _ (Incidence x) (fun l => Classical.propDecidable (Incidence x l)) L =
        L.filter (Incidence x) := Finset.filter_congr_decidable _ _ _
  rw [hfilter]
  congr 1

end RyserCoveringCounterexample.LineCover

end

end OAI
