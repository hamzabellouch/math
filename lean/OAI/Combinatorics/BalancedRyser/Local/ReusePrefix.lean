import OAI.Combinatorics.BalancedRyser.Local.ConfigurationReuse
import OAI.Combinatorics.BalancedRyser.Local.ReuseTower

namespace OAI

namespace Balanced.ReuseTower

open scoped BigOperators
noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

abbrev Prescription (F : Type*) := Slot F × Local.TupleCode F

def prescriptionTuple (r : Prescription F) : FourTuple F := Local.decodeTuple r.2

def prescriptionGenerators (r : Prescription F) : Finset (Direction F) :=
  generatorSet (prescriptionTuple r)

def exposedDirections (pre : List (Prescription F)) : Finset (Direction F) :=
  pre.toFinset.biUnion prescriptionGenerators

def oldCount (pre : List (Prescription F)) (r : Prescription F) : ℕ :=
  (oldGeneratorIndices (prescriptionTuple r) (exposedDirections pre)).card

def prescriptionEvent (p : Point F) (r : Prescription F) (M : MergedPairs F) : Prop :=
  Function.Injective r.2.1 ∧ (∀ i, r.2.1 i ≠ r.1.1) ∧
    (∀ i, OnLine (tuplePoint M (prescriptionTuple r) i) (lineThrough r.1.1 p)) ∧
    ∀ i, tuplePoint M (prescriptionTuple r) i ≠ p

def prefixEvent (p : Point F) (pre : List (Prescription F)) (M : MergedPairs F) : Prop :=
  ∀ r ∈ pre, prescriptionEvent p r M

def prefixWeight (K : ℝ) (p : Point F) (pre : List (Prescription F)) : ℝ :=
  (K / Fintype.card F) ^ pre.length * Local.offsetProbability (prefixEvent p pre)

def expose (old : Finset (Direction F)) (M : MergedPairs F) : old → Bool → F :=
  fun d => M d

omit [Field F] [Fintype F] [DecidableEq F] in
@[simp] theorem expose_eq_iff (old : Finset (Direction F)) (M N : MergedPairs F) :
    expose old M = expose old N ↔ ∀ d ∈ old, M d = N d := by
  constructor
  · intro h d hd
    exact congrFun h ⟨d, hd⟩
  · intro h
    funext d
    exact h d d.2

omit [Fintype F] in
theorem tuplePoint_eq_of_expose_eq (pre : List (Prescription F))
    (r : Prescription F) (hr : r ∈ pre) (M N : MergedPairs F)
    (hMN : expose (exposedDirections pre) M = expose (exposedDirections pre) N)
    (i : Fin 4) :
    tuplePoint M (prescriptionTuple r) i = tuplePoint N (prescriptionTuple r) i := by
  have hg (j : Fin 4) : (prescriptionTuple r).generator j ∈ exposedDirections pre := by
    apply Finset.mem_biUnion.mpr
    exact ⟨r, List.mem_toFinset.mpr hr, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
  have heq := (expose_eq_iff _ _ _).mp hMN
  simp only [tuplePoint, constituent, heq _ (hg i), heq _ (hg (i + 1))]

omit [Fintype F] in
theorem prefixEvent_depends_on_exposed (p : Point F) (pre : List (Prescription F))
    (M N : MergedPairs F)
    (hMN : expose (exposedDirections pre) M = expose (exposedDirections pre) N) :
    prefixEvent p pre M ↔ prefixEvent p pre N := by
  unfold prefixEvent prescriptionEvent
  apply forall_congr'
  intro r
  apply forall_congr'
  intro hr
  simp only [tuplePoint_eq_of_expose_eq pre r hr M N hMN]

omit [Field F] [Fintype F] in
theorem exposedDirections_card_le (pre : List (Prescription F)) :
    (exposedDirections pre).card ≤ 4 * pre.length := by
  calc
    (exposedDirections pre).card ≤ ∑ r ∈ pre.toFinset, (prescriptionGenerators r).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _r ∈ pre.toFinset, 4 := by
      apply Finset.sum_le_sum
      intro r _
      exact (Finset.card_image_le).trans (by simp)
    _ ≤ 4 * pre.length := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      nlinarith [List.toFinset_card_le pre]

omit [Field F] [Fintype F] in
theorem oldCount_le_four (pre : List (Prescription F)) (r : Prescription F) :
    oldCount pre r ≤ 4 := by
  exact (Finset.card_le_univ _).trans_eq (by simp)

@[simp] theorem prefixWeight_nil (K : ℝ) (p : Point F) :
    prefixWeight K p [] = 1 := by
  simp [prefixWeight, Local.offsetProbability, prefixEvent]

theorem prefixWeight_nonneg (K : ℝ) (hK : 0 ≤ K) (p : Point F)
    (pre : List (Prescription F)) : 0 ≤ prefixWeight K p pre := by
  unfold prefixWeight Local.offsetProbability
  positivity

theorem offsetProbability_eq_uniform (E : MergedPairs F → Prop) :
    Local.offsetProbability E =
      ((PMF.uniformOfFintype (MergedPairs F)).toOuterMeasure {M | E M}).toReal :=
  (uniform_probability_eq_average E).symm

end
end Balanced.ReuseTower

end OAI
