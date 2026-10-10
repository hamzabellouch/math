import OAI.GroupTheory.Thompson.RecursiveColoring
import OAI.GroupTheory.Thompson.IntervalFamily

namespace OAI

/-!
# The actual finite family of colors, including zero outside admissibility

A basic partition is admissible when it respects every chosen parent and
child. Its family color is always defined and lies in the unit ball. The
option extension also assigns zero to a non-basic image; the group-level
construction will supply the actual partial image partition.
-/

noncomputable section

universe uE

namespace ThompsonNonamenability

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {D : ℕ}

/-- One simultaneous condition for all actual parent and child intervals. -/
def PartitionAdmissible (D : ℕ) (T : BasicPartition) : Prop :=
  ∀ q : IntervalIndex D, T.Respects (familyInterval D q)

/-- The family color is zero whenever the actual partition is inadmissible. -/
def partitionFamilyColor (hD : 0 < D) (f : UnitBall E → UnitBall E)
    (T : BasicPartition) (q : IntervalIndex D) : UnitBall E := by
  classical
  exact if h : PartitionAdmissible D T then
    partitionColor (selectedInterval D) (selectedInterval_internal D) hD f
      (T.restrict (familyInterval D q) (h q))
  else unitBallZero E

theorem partitionFamilyColor_of_admissible (hD : 0 < D)
    (f : UnitBall E → UnitBall E) (T : BasicPartition)
    (h : PartitionAdmissible D T) (q : IntervalIndex D) :
    partitionFamilyColor hD f T q =
      partitionColor (selectedInterval D) (selectedInterval_internal D) hD f
        (T.restrict (familyInterval D q) (h q)) := by
  simp only [partitionFamilyColor, dite_eq_left h]

theorem partitionFamilyColor_of_not_admissible (hD : 0 < D)
    (f : UnitBall E → UnitBall E) (T : BasicPartition)
    (h : ¬PartitionAdmissible D T) (q : IntervalIndex D) :
    partitionFamilyColor hD f T q = unitBallZero E := by
  simp only [partitionFamilyColor, dite_eq_right h]

theorem partitionFamilyColor_norm_le (hD : 0 < D)
    (f : UnitBall E → UnitBall E) (T : BasicPartition) (q : IntervalIndex D) :
    ‖(partitionFamilyColor hD f T q : E)‖ ≤ 1 :=
  (partitionFamilyColor hD f T q).property

/-- A parent's color is the map applied to its actual child-color mean. -/
theorem partitionFamilyColor_parent (hD : 0 < D)
    (f : UnitBall E → UnitBall E) (T : BasicPartition)
    (h : PartitionAdmissible D T) (i : Fin D) :
    partitionFamilyColor hD f T (.inl i) =
      f (ballMean hD (fun j => partitionFamilyColor hD f T (.inr (i, j)))) := by
  simp only [partitionFamilyColor_of_admissible hD f T h, familyInterval]
  exact partitionColor_restrict (selectedInterval D) (selectedInterval_internal D)
    hD f T i (h (.inl i)) (fun j => h (.inr (i, j)))

/-- Total zero extension at a non-basic image as well as an inadmissible one. -/
def optionFamilyColor (hD : 0 < D) (f : UnitBall E → UnitBall E) :
    Option BasicPartition → IntervalIndex D → UnitBall E
  | none, _ => unitBallZero E
  | some T, q => partitionFamilyColor hD f T q

@[simp] theorem optionFamilyColor_none (hD : 0 < D)
    (f : UnitBall E → UnitBall E) (q : IntervalIndex D) :
    optionFamilyColor hD f none q = unitBallZero E := rfl

@[simp] theorem optionFamilyColor_some (hD : 0 < D)
    (f : UnitBall E → UnitBall E) (T : BasicPartition) (q : IntervalIndex D) :
    optionFamilyColor hD f (some T) q = partitionFamilyColor hD f T q := rfl

theorem optionFamilyColor_norm_le (hD : 0 < D)
    (f : UnitBall E → UnitBall E) (T : Option BasicPartition) (q : IntervalIndex D) :
    ‖(optionFamilyColor hD f T q : E)‖ ≤ 1 :=
  (optionFamilyColor hD f T q).property

end ThompsonNonamenability

end

end OAI
