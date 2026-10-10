import Mathlib
import OAI.Computability.VertexCover.Reduction.PrivatePairProjectionRight

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.LabelCover
open VertexCover.Restriction
open EnergyForm.Projection
open scoped BigOperators

noncomputable def otherWeightProjection (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) : (Φ.restrictionForm d).Projection :=
  product Φ.weightProjection Φ.weightProjection_commute (J.erase j).toList

theorem privateSeed_weight_commute (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j k : Fin d) (f : Φ.RestrictionSpace d) :
    Φ.privateSeedProjection J j (Φ.weightProjection k f) =
      Φ.weightProjection k (Φ.privateSeedProjection J j f) :=
  Φ.condition_weightProjection_commute (Φ.privateSeedKey J j) k f

theorem privateSeed_otherWeight_commute (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) (f : Φ.RestrictionSpace d) :
    Φ.privateSeedProjection J j (Φ.otherWeightProjection J j f) =
      Φ.otherWeightProjection J j (Φ.privateSeedProjection J j f) :=
  (productMap_commute Φ.weightProjection (Φ.privateSeedProjection J j)
    (fun k x => (Φ.privateSeed_weight_commute J j k x).symm) (J.erase j).toList f).symm

noncomputable def privateAverageProjection (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) : (Φ.restrictionForm d).Projection :=
  (Φ.privateSeedProjection J j).comp (Φ.otherWeightProjection J j)
    (Φ.privateSeed_otherWeight_commute J j)

theorem privateAverage_weight_commute (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j k : Fin d) (f : Φ.RestrictionSpace d) :
    Φ.privateAverageProjection J j (Φ.weightProjection k f) =
      Φ.weightProjection k (Φ.privateAverageProjection J j f) := by
  change Φ.privateSeedProjection J j
      (productMap Φ.weightProjection (J.erase j).toList (Φ.weightProjection k f)) = _
  rw [productMap_commute Φ.weightProjection (Φ.weightProjection k)
    (fun l => Φ.weightProjection_commute l k), Φ.privateSeed_weight_commute]
  rfl

noncomputable def privateProjection (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) : (Φ.restrictionForm d).Projection :=
  (Φ.weightProjection j).residual.comp (Φ.privateAverageProjection J j)
    (residual_commute _ _ (fun f => (Φ.privateAverage_weight_commute J j j f).symm))

theorem privateProjection_weight_commute (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j k : Fin d) (f : Φ.RestrictionSpace d) :
    Φ.privateProjection J j (Φ.weightProjection k f) =
      Φ.weightProjection k (Φ.privateProjection J j f) := by
  change (Φ.weightProjection j).residual
    (Φ.privateAverageProjection J j (Φ.weightProjection k f)) = _
  rw [Φ.privateAverage_weight_commute, residual_commute _ _ (Φ.weightProjection_commute j k)]
  rfl

theorem privateProjection_group_le (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) (f : Φ.RestrictionSpace d) :
    (Φ.restrictionForm d).energy (Φ.privateProjection J j (Φ.weightGroup j f)) ≤
      (Φ.restrictionForm d).energy (Φ.privateProjection J j f) :=
  finDifference_retained_le Φ.weightProjection Φ.weightProjection_commute
    (Φ.privateProjection J j) (fun k x => (Φ.privateProjection_weight_commute J j k x).symm) j f

theorem privateProjection_group_eq (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) (f : Φ.RestrictionSpace d) :
    Φ.privateProjection J j (Φ.weightGroup j f) =
      Φ.privateAverageProjection J j (Φ.weightGroup j f) := by
  change (Φ.weightProjection j).residual
    (Φ.privateAverageProjection J j (Φ.weightGroup j f)) = _
  rw [residual_commute _ _ (fun x => (Φ.privateAverage_weight_commute J j j x).symm),
    Φ.weightGroup_centered]

theorem privateAverage_loss_le (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) (f : Φ.RestrictionSpace d) :
    (Φ.restrictionForm d).energy ((Φ.privateAverageProjection J j).residual f) ≤
      (∑ k ∈ J.erase j, (Φ.restrictionForm d).energy ((Φ.weightProjection k).residual f)) +
      ∑ e : PositionPair d, (Φ.restrictionForm d).energy ((Φ.privatePairProjection J j e).residual f) := by
  have hc := comp_loss_le (Φ.privateSeedProjection J j) (Φ.otherWeightProjection J j)
    (Φ.privateSeed_otherWeight_commute J j) f
  have hw := product_loss_finset Φ.weightProjection Φ.weightProjection_commute (J.erase j) f
  have hs := residual_le_of_nested (Φ.privateSeedProjection J j)
    (product (Φ.privatePairProjection J j) (Φ.privatePairProjection_commute J j) Finset.univ.toList)
    (Φ.privateSeedProjection_product J j) f
  have hsp := product_loss_finset (Φ.privatePairProjection J j)
    (Φ.privatePairProjection_commute J j) Finset.univ f
  change (Φ.restrictionForm d).energy ((Φ.privateAverageProjection J j).residual f) ≤ _ at hc
  change (Φ.restrictionForm d).energy ((Φ.otherWeightProjection J j).residual f) ≤ _ at hw
  linarith

theorem privateProjection_group_lower (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) (f : Φ.RestrictionSpace d) :
    (Φ.restrictionForm d).energy (Φ.weightGroup j f) ≤
      (Φ.restrictionForm d).energy (Φ.privateProjection J j f) +
      (∑ k ∈ J.erase j, (Φ.restrictionForm d).energy
        ((Φ.weightProjection k).residual (Φ.weightGroup j f))) +
      ∑ e : PositionPair d, (Φ.restrictionForm d).energy
        ((Φ.privatePairProjection J j e).residual (Φ.weightGroup j f)) := by
  have he := (Φ.privateAverageProjection J j).pythagoras (Φ.weightGroup j f)
  have hl := Φ.privateAverage_loss_le J j (Φ.weightGroup j f)
  have hr := Φ.privateProjection_group_le J j f
  rw [Φ.privateProjection_group_eq] at hr
  linarith

end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
