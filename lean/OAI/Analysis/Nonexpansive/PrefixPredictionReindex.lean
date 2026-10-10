import OAI.Analysis.Nonexpansive.PrefixPredictionOutputs

namespace OAI

/-!
# Reindexing a finite prediction history

Equivalent finite candidate labels give the same residual inputs, actual
nonlinear predictions, and chosen weak limits. The coefficient domain is
transported in both directions, so the full detector sets also agree. These
identities connect a recorded finite prefix to the final ledger without
changing any map or passing a weak limit through a nonlinear operation.
-/

noncomputable section

open Set Filter
open scoped BigOperators Topology

namespace ReflexiveFixedPoints.Prediction.Prefix

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {P I J : Type*} [Fintype P] [DecidableEq P] [Fintype I] [Fintype J]
variable {parentI : I → P} {parentJ : J → P}

/-- Every parent-group mass is preserved under a finite equivalence of candidate labels. -/
theorem coefficientSum_pullCoeff {P I J : Type*}
    [Fintype P] [DecidableEq P] [Fintype I] [Fintype J]
    {parentI : I → P} {parentJ : J → P} (e : I ≃ J)
    (hp : ∀ i, parentJ (e i) = parentI i) (theta : J → ℝ) (p : P) :
    Prediction.coefficientSum parentI (fun i => theta (e i)) p =
      Prediction.coefficientSum parentJ theta p := by
  unfold Prediction.coefficientSum Prediction.groupedCoefficient
  simpa only [hp] using
    (e.sum_comp (fun j => if parentJ j = p then theta j else 0))

/-- Pull back an admissible coefficient function along the candidate-label equivalence. -/
def pullCoeff (e : I ≃ J) (hp : ∀ i, parentJ (e i) = parentI i)
    (theta : Prediction.coefficientSet parentJ) : Prediction.coefficientSet parentI :=
  ⟨fun i => theta.val (e i),
    ⟨fun i => theta.property.1 (e i), fun p => by
      rw [coefficientSum_pullCoeff e hp]
      exact theta.property.2 p⟩⟩

@[simp] theorem pullCoeff_apply (e : I ≃ J)
    (hp : ∀ i, parentJ (e i) = parentI i)
    (theta : Prediction.coefficientSet parentJ) (i : I) :
    (pullCoeff e hp theta).val i = theta.val (e i) := rfl

/-- Reindexing is an equivalence of the entire admissible coefficient domains. -/
def pullCoeffEquiv (e : I ≃ J) (hp : ∀ i, parentJ (e i) = parentI i) :
    Prediction.coefficientSet parentJ ≃ Prediction.coefficientSet parentI where
  toFun := pullCoeff e hp
  invFun := pullCoeff e.symm (fun j => by simpa using (hp (e.symm j)).symm)
  left_inv theta := by
    apply Subtype.ext
    funext j
    simp only [pullCoeff_apply, Equiv.apply_symm_apply]
  right_inv theta := by
    apply Subtype.ext
    funext i
    simp only [pullCoeff_apply, Equiv.symm_apply_apply]

@[simp] theorem pullCoeffEquiv_apply (e : I ≃ J)
    (hp : ∀ i, parentJ (e i) = parentI i)
    (theta : Prediction.coefficientSet parentJ) :
    pullCoeffEquiv e hp theta = pullCoeff e hp theta := rfl

/-- The ambient residual finite sum is unchanged by reindexing every candidate. -/
theorem residualPoint_pullCoeff (e : I ≃ J)
    (hp : ∀ i, parentJ (e i) = parentI i)
    (yI : I → X) (yJ : J → X) (hy : ∀ i, yJ (e i) = yI i)
    (b : X) (theta : Prediction.coefficientSet parentJ) (p : P) :
    Prediction.residualPoint parentI yI b (pullCoeff e hp theta).val p =
      Prediction.residualPoint parentJ yJ b theta.val p := by
  unfold Prediction.residualPoint
  apply congrArg (fun s : X => b + s)
  calc
    (∑ i, Prediction.groupedCoefficient parentI (pullCoeff e hp theta).val p i • (yI i - b)) =
        ∑ i, Prediction.groupedCoefficient parentJ theta.val p (e i) • (yJ (e i) - b) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Prediction.groupedCoefficient, pullCoeff_apply, hp, hy]
    _ = ∑ j, Prediction.groupedCoefficient parentJ theta.val p j • (yJ j - b) :=
      e.sum_comp (fun j => Prediction.groupedCoefficient parentJ theta.val p j • (yJ j - b))

section ActualOutputs

variable {K : Set X}
variable (hconvex : Convex ℝ K)
variable (maps : P → K → K) (evaluate : (P → K) → K)
variable (e : I ≃ J) (hp : ∀ i, parentJ (e i) = parentI i)
variable (yI : I → K) (yJ : J → K) (hy : ∀ i, yJ (e i) = yI i)
include e hp hy

/-- The residual inputs agree as elements of the actual norm subtype. -/
theorem residualInput_pullCoeff (b : K) (theta : Prediction.coefficientSet parentJ) (p : P) :
    residualInput hconvex parentI yI b (pullCoeff e hp theta) p =
      residualInput hconvex parentJ yJ b theta p := by
  apply Subtype.ext
  exact residualPoint_pullCoeff e hp (fun i => (yI i : X)) (fun j => (yJ j : X))
    (fun i => congrArg Subtype.val (hy i)) (b : X) theta p

/-- Nonlinear maps receive exactly equal inputs; no linearity is required. -/
theorem evaluatedPrediction_pullCoeff (b : K) (theta : Prediction.coefficientSet parentJ) :
    evaluatedPrediction hconvex maps evaluate parentI yI b (pullCoeff e hp theta) =
      evaluatedPrediction hconvex maps evaluate parentJ yJ b theta := by
  unfold evaluatedPrediction
  apply congrArg evaluate
  funext p
  apply congrArg (maps p)
  exact residualInput_pullCoeff hconvex e hp yI yJ hy b theta p

/-- Equality of the actual sequences preserves the exact compactness-selected weak limit. -/
theorem predictionWeakLimit_pullCoeff (hK : WeaklyCompact K) (b : ℕ → K)
    (U : Ultrafilter ℕ) (theta : Prediction.coefficientSet parentJ) :
    predictionWeakLimit hconvex maps evaluate parentI yI hK b U (pullCoeff e hp theta) =
      predictionWeakLimit hconvex maps evaluate parentJ yJ hK b U theta := by
  unfold predictionWeakLimit
  apply congrArg (fun q : ℕ → K => Prediction.chosenWeakLimit hK q U)
  funext j
  exact evaluatedPrediction_pullCoeff hconvex maps evaluate e hp yI yJ hy (b j) theta

/-- Reindexing preserves the full prediction image, not merely a selected parameter. -/
theorem predictionWeakLimit_range_reindex (hK : WeaklyCompact K) (b : ℕ → K)
    (U : Ultrafilter ℕ) :
    Set.range (fun theta =>
      (predictionWeakLimit hconvex maps evaluate parentI yI hK b U theta : X)) =
    Set.range (fun theta =>
      (predictionWeakLimit hconvex maps evaluate parentJ yJ hK b U theta : X)) := by
  ext x
  constructor
  · rintro ⟨thetaI, rfl⟩
    obtain ⟨thetaJ, htheta⟩ := (pullCoeffEquiv e hp).surjective thetaI
    change pullCoeff e hp thetaJ = thetaI at htheta
    rw [← htheta]
    exact ⟨thetaJ, congrArg Subtype.val
      (predictionWeakLimit_pullCoeff hconvex maps evaluate e hp yI yJ hy hK b U thetaJ).symm⟩
  · rintro ⟨thetaJ, rfl⟩
    exact ⟨pullCoeff e hp thetaJ, congrArg Subtype.val
      (predictionWeakLimit_pullCoeff hconvex maps evaluate e hp yI yJ hy hK b U thetaJ)⟩

/-- The complete pre-map detector set is identical after a finite history reindexing. -/
theorem detectorSet_reindex (hK : WeaklyCompact K) (b : ℕ → K)
    (U : Ultrafilter ℕ) (densePoints : ℕ → K) (densePrefixLength : ℕ) :
    detectorSet hconvex maps evaluate parentI yI hK b U densePoints densePrefixLength =
      detectorSet hconvex maps evaluate parentJ yJ hK b U densePoints densePrefixLength := by
  unfold detectorSet
  rw [predictionWeakLimit_range_reindex hconvex maps evaluate e hp yI yJ hy hK b U]

end ActualOutputs

end ReflexiveFixedPoints.Prediction.Prefix

end

end OAI
