import OAI.NumberTheory.TotientAsymptotic.ActualCollisionExponent
import OAI.NumberTheory.TotientAsymptotic.CollisionAllSize
import OAI.NumberTheory.TotientAsymptotic.CollisionClassData

namespace OAI

/-! All Ford hypotheses for a block of actual good tuple pairs. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

/-- The arithmetic data of a good collision in a single counting block.
The positive-index block endpoints will be supplied by dyadic subdivision. -/
structure GoodCollisionBlock (x t : ℝ) (H i : ℕ) (y : ℝ)
    (q : TotientTuple (R x H) × TotientTuple (R x H)) : Prop where
  left : IsGoodTuple x H t q.1
  right : IsGoodTuple x H t q.2
  value : tupleValue q.1=tupleValue q.2
  first : wholeWitnessPrime q.1.head (chosenRemainder x H q.1.tail) i ≠
    wholeWitnessPrime q.2.head (chosenRemainder x H q.2.tail) i
  common : ∀ j < i, wholeWitnessPrime q.1.head (chosenRemainder x H q.1.tail) j =
    wholeWitnessPrime q.2.head (chosenRemainder x H q.2.tail) j
  minLeft : y^(9/10 : ℝ) ≤ wholeWitnessPrime q.1.head (chosenRemainder x H q.1.tail) i
  minRight : y^(9/10 : ℝ) ≤ wholeWitnessPrime q.2.head (chosenRemainder x H q.2.tail) i
  size : (witnessBlockValue q.1.head (chosenRemainder x H q.1.tail) i (collisionLastIndex x i) : ℝ) ≤ y
  zero : i=0 → y=x

/-- The finite grid, all published parameter and pointwise restrictions, and
the full strict exponent saving are consequences of the actual good data. -/
theorem actual_ford_data : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i : ℕ, i ≤ R x H → L x H < m x → R x H < L x H → ∀ t y : ℝ,
    1 < y → 0 < B y → (87/100 : ℝ)*fordBandScale x i ≤ B y →
    B y ≤ 2*fordBandScale x i →
    ∀ q : TotientTuple (R x H) × TotientTuple (R x H), GoodCollisionBlock x t H i y q →
    let η := chosenRemainder x H q.1.tail
    let ξ := chosenRemainder x H q.2.tail
    let I := collisionSurvivors q.1.head q.2.head η ξ i (collisionLastIndex x i)
    let T := comparisonPairAt x H (collisionLastIndex x i) I q
    let δ := collisionMesh x y i
    let Z := fordBandScale x (collisionLastIndex x i)
    let Y := comparisonCutoffs y (pairUpperCoordinates T y Z δ)
    let U := comparisonCutoffs y (pairLowerCoordinates T y δ)
    pairGridLabel T y δ ∈ collisionGridFamilies δ I.card ∧
    FordComparisonParameters I.card y (normalityScale x i) (collisionResidual η i)
      (collisionCanceledProduct q.1.head q.2.head η ξ i (collisionLastIndex x i)) Y U ∧
    FordComparisonConditions I.card y (normalityScale x i) (collisionResidual η i)
      (collisionCanceledProduct q.1.head q.2.head η ξ i (collisionLastIndex x i)) Y U T ∧
    (-2+(∑ j ∈ Finset.Icc 1 (I.card-1), a j*(B (Y j)/B y))+
      comparisonError I.card y (normalityScale x i) Y U ≤
        -1-1/(2*((m x-i : ℕ) : ℝ)^4)) := by
  filter_upwards [actual_comparison_parameters,actual_collision_exponent,collision_small_factors_all]
    with H hparam hexp hsmall
  filter_upwards [hparam,hexp,hsmall] with x hp he hs
  intro i hi hL hR t y hy hBy hByl hByu q hq
  let η := chosenRemainder x H q.1.tail
  let ξ := chosenRemainder x H q.2.tail
  have hη : IsBasicRemainder x H η := (chosenRemainder_spec hq.left.1.2.2.1).1
  have hξ : IsBasicRemainder x H ξ := (chosenRemainder_spec hq.right.1.2.2.1).1
  have hv : tupleValue (witnessTuple q.1.head η)=tupleValue (witnessTuple q.2.head ξ) := by
    dsimp only [η,ξ]
    rw [chosenRemainder_tuple hq.left.1,chosenRemainder_tuple hq.right.1]
    exact hq.value
  obtain ⟨hD,hr⟩ := hs i q.1.head q.2.head hi hL hq.left.1.1 η ξ hη hq.first y hy.le hq.size hq.zero
  have hparams := hp i q.1.head q.2.head hi hL hR hq.left.1.1 η ξ hη hξ
    (chosenRemainder_good hq.left) (chosenRemainder_good hq.right) hv hq.first hq.common
    y hy hBy hByl hByu hq.minLeft hq.minRight hq.size hD hr
  have hexponent := he i q.1.head q.2.head hi hL hR hq.left.1.1 η ξ hη hξ
    (chosenRemainder_good hq.left) (chosenRemainder_good hq.right) hv hq.first hq.common
    y hy hBy hByl hByu hq.minLeft hq.minRight hq.size hq.zero
  exact ⟨hparams.1,hparams.2.1,hparams.2.2,hexponent⟩

end TotientAsymptotic

end

end OAI
