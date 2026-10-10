import OAI.GroupTheory.Thompson.BasicPartition
import OAI.GroupTheory.Thompson.HilbertAverage

namespace OAI

/-!
# Recursive unit-ball colors of actual basic dyadic partitions

The recursion uses the number of actual cells. Restriction to any selected
internal interval strictly decreases that number. The mean is bundled with
its genuine unit-ball proof before it is supplied to the map.
-/

noncomputable section

universe uE

namespace ThompsonNonamenability

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {D : ℕ}

def partitionColor (I : Fin D → BasicInterval) (hI : ∀ i, (I i).Internal)
    (hD : 0 < D) (f : UnitBall E → UnitBall E) (T : BasicPartition) :
    UnitBall E := by
  classical
  exact if h : ∀ i, T.Respects (I i) then
    f (ballMean hD (fun i =>
      partitionColor I hI hD f (T.restrict (I i) (h i))))
  else unitBallZero E
termination_by T.cellCount
decreasing_by
  exact T.restrict_cellCount_lt _ _ (hI _)

/-- The recursive branch, with its actual restricted partitions. -/
theorem partitionColor_of_respects (I : Fin D → BasicInterval)
    (hI : ∀ i, (I i).Internal) (hD : 0 < D)
    (f : UnitBall E → UnitBall E) (T : BasicPartition)
    (h : ∀ i, T.Respects (I i)) :
    partitionColor I hI hD f T = f (ballMean hD (fun i =>
      partitionColor I hI hD f (T.restrict (I i) (h i)))) := by
  rw [partitionColor]
  simp only [dite_eq_left h]

/-- Partitions failing the simultaneous respect condition receive zero. -/
theorem partitionColor_of_not_respects (I : Fin D → BasicInterval)
    (hI : ∀ i, (I i).Internal) (hD : 0 < D)
    (f : UnitBall E → UnitBall E) (T : BasicPartition)
    (h : ¬∀ i, T.Respects (I i)) :
    partitionColor I hI hD f T = unitBallZero E := by
  rw [partitionColor]
  simp only [dite_eq_right h]

theorem partitionColor_norm_le (I : Fin D → BasicInterval)
    (hI : ∀ i, (I i).Internal) (hD : 0 < D)
    (f : UnitBall E → UnitBall E) (T : BasicPartition) :
    ‖(partitionColor I hI hD f T : E)‖ ≤ 1 :=
  (partitionColor I hI hD f T).property

/-- Applying the recursion to a parent restriction gives the actual child mean.
The normalized two-step restriction is replaced by the proved composite one. -/
theorem partitionColor_restrict (I : Fin D → BasicInterval)
    (hI : ∀ i, (I i).Internal) (hD : 0 < D)
    (f : UnitBall E → UnitBall E) (T : BasicPartition) (i : Fin D)
    (hparent : T.Respects (I i))
    (hchild : ∀ j, T.Respects ((I i).comp (I j))) :
    partitionColor I hI hD f (T.restrict (I i) hparent) =
      f (ballMean hD (fun j => partitionColor I hI hD f
        (T.restrict ((I i).comp (I j)) (hchild j)))) := by
  let hr : ∀ j, (T.restrict (I i) hparent).Respects (I j) :=
    fun j => T.restrict_respects (I i) (I j) hparent (hchild j)
  calc
    partitionColor I hI hD f (T.restrict (I i) hparent) =
        f (ballMean hD (fun j => partitionColor I hI hD f
          ((T.restrict (I i) hparent).restrict (I j) (hr j)))) :=
      partitionColor_of_respects I hI hD f _ hr
    _ = _ := by
      apply congrArg f
      apply congrArg (ballMean hD)
      funext j
      apply congrArg (partitionColor I hI hD f)
      exact T.restrict_restrict (I i) (I j) hparent (hchild j)

end ThompsonNonamenability

end

end OAI
