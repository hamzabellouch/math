import OAI.NumberTheory.TotientAsymptotic.WitnessCollision
import OAI.NumberTheory.TotientAsymptotic.ResidualCutoff
import OAI.NumberTheory.TotientAsymptotic.CollisionIndices
import OAI.NumberTheory.TotientAsymptotic.TupleCounting

namespace OAI

/-! Actual good tuples: every basic witness must satisfy the four collision conditions. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def normalityScale (x : ℝ) (i : ℕ) : ℝ :=
  Real.exp (Real.exp ((fordBandScale x i)^(1/3 : ℝ)))

def collisionLastIndex (x : ℝ) (i : ℕ) : ℕ := i+collisionCutoff (m x-i)

def collisionSmoothCutoff (x : ℝ) (i : ℕ) : ℝ :=
  Real.exp (Real.exp ((7/10 : ℝ)*fordBandScale x (collisionLastIndex x i)))

def collisionResidual {x : ℝ} {H : ℕ} (η : RemainderDatum (L x H)) (i : ℕ) : ℕ :=
  (suffixPreimage η (collisionLastIndex x i)).totient

/-- The four conditions in extraction.tex, equation good-conditions. The
coordinates and scales are those of the common original endpoint `x`. -/
def GoodWitnessConditions {x : ℝ} {H : ℕ} (p : ℕ)
    (η : RemainderDatum (L x H)) : Prop :=
  ∀ i ∈ Finset.Icc 0 (R x H),
    (∑ r ∈ Finset.Icc (i+1) (L x H), a (r-i)*remainderCoord x η r) ≤
      (1-1/((m x-i : ℕ) : ℝ)^4)*remainderCoord x η i ∧
    (∀ j ∈ Finset.Icc i (collisionLastIndex x i),
      IsNormalPrime (normalityScale x i) (wholeWitnessPrime p η j)) ∧
    SquarefreeAbove (∏ j ∈ Finset.Icc i (collisionLastIndex x i),
      (wholeWitnessPrime p η j-1)) (collisionSmoothCutoff x i) ∧
    ((collisionResidual η i).primeFactorsList.length : ℝ) ≤
      fordBandScale x i/((m x-i : ℕ) : ℝ)^8

/-- Witnesses are universally quantified; no arbitrary choice can turn a
bad tuple into a good one. -/
def IsGoodTuple (x : ℝ) (H : ℕ) (t : ℝ) (τ : TotientTuple (R x H)) : Prop :=
  IsBasicTuple x H t τ ∧
  ∀ η : RemainderDatum (L x H), IsBasicRemainder x H η →
    prefixOfRemainder x H η = τ.tail → GoodWitnessConditions τ.head η

def goodTupleFinset (x : ℝ) (H : ℕ) (t : ℝ) : Finset (TotientTuple (R x H)) :=
  (tupleFinset x H t).filter (IsGoodTuple x H t)

def badTupleFinset (x : ℝ) (H : ℕ) (t : ℝ) : Finset (TotientTuple (R x H)) :=
  tupleFinset x H t \ goodTupleFinset x H t

lemma mem_goodTupleFinset {x t : ℝ} {H : ℕ} {τ : TotientTuple (R x H)}
    (hPH : P H ≤ H) : τ ∈ goodTupleFinset x H t ↔ IsGoodTuple x H t τ := by
  simp only [goodTupleFinset, Finset.mem_filter]
  exact ⟨And.right, fun h => ⟨(mem_tupleFinset hPH).mpr h.1,h⟩⟩

lemma bad_tuple_failing_witness {x t : ℝ} {H : ℕ} {τ : TotientTuple (R x H)}
    (hPH : P H ≤ H) (hτ : τ ∈ badTupleFinset x H t) :
    ∃ η : RemainderDatum (L x H), IsBasicRemainder x H η ∧
      witnessTuple τ.head η = τ ∧ ¬ GoodWitnessConditions τ.head η := by
  obtain ⟨ht,hng⟩ := Finset.mem_sdiff.mp hτ
  have hb := (mem_tupleFinset hPH).mp ht
  have hn : ¬ IsGoodTuple x H t τ := mt (mem_goodTupleFinset hPH).mpr hng
  have hw : ¬ ∀ η : RemainderDatum (L x H), IsBasicRemainder x H η →
      prefixOfRemainder x H η = τ.tail → GoodWitnessConditions τ.head η := by
    intro h
    exact hn ⟨hb,h⟩
  push Not at hw
  obtain ⟨η,hη,he,hfail⟩ := hw
  refine ⟨η,hη,?_,hfail⟩
  cases τ
  simpa only [witnessTuple, TotientTuple.mk.injEq, true_and] using he

/-- The finite witness space used to bound discarded tuples. -/
def failingWitnessFinset (x : ℝ) (H : ℕ) (t : ℝ) :
    Finset (ℕ × RemainderDatum (L x H)) :=
  ((Finset.range (⌊t⌋₊+2)) ×ˢ (basicRemainders_finite x H).toFinset).filter
    (fun q => IsBasicTuple x H t (witnessTuple q.1 q.2) ∧ ¬ GoodWitnessConditions q.1 q.2)

/-- Multiple basic witnesses cause no loss: counting all failing witnesses
is an upper bound for the number of bad tuples. -/
theorem bad_tuple_card_le_failing_witnesses {x t : ℝ} {H : ℕ} (hPH : P H ≤ H) :
    (badTupleFinset x H t).card ≤ (failingWitnessFinset x H t).card := by
  have hsub : badTupleFinset x H t ⊆ (failingWitnessFinset x H t).image
      (fun q => witnessTuple q.1 q.2) := by
    intro τ hτ
    obtain ⟨η,hη,he,hfail⟩ := bad_tuple_failing_witness hPH hτ
    have hb := (mem_tupleFinset hPH).mp (Finset.mem_sdiff.mp hτ).1
    refine Finset.mem_image.mpr ⟨(τ.head,η),?_,he⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (basic_tuple_head_bound hPH hb),?_⟩,?_⟩
    · exact (basicRemainders_finite x H).mem_toFinset.mpr hη
    · exact ⟨he.symm ▸ hb,hfail⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le)

end TotientAsymptotic

end

end OAI
