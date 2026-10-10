import OAI.Combinatorics.ContingencyTables.Transport.ReflectedSlices
import OAI.Combinatorics.ContingencyTables.Transport.NestedPenaltyApplication

namespace OAI

/-!
# Both literal factorial lifts of the first paper's nested marginal

Reflection changes the affine offsets and signs in the full-line and
small-subset penalties. The same actual positive nested factors therefore
prove the complementary lift's addition property, including its hard limit.
-/

namespace ContingencyTables.ReflectedNested

open scoped BigOperators Classical Matrix Topology
open Filter CommonBasesFPRAS FactorialSignatures ProductIntegerSignature
open NestedProductSignature NestedPenaltyApplication IntegerReflection
open BalancedBox BalancedFamily LabelledFactorial ReflectedSlices

variable {C G : Type*} [Fintype C] [Fintype G]

omit [Fintype G] in
lemma smallTotal_reflect_add (line : C → G) (inner : C → Bool) (m z : C → ℕ)
    (hz : InBox m z) (g : G) :
    smallTotal line inner (reflect m z) g+smallTotal line inner z g=smallTotal line inner m g :=
  lineTotal_reflect_add (fun i => (line i,inner i)) m z hz (g,true)

theorem softWeight_reflect (line : C → G) (inner : C → Bool)
    (offset slope smallOffset smallSlope : G → ℝ) (L : ℝ) (m z : C → ℕ) (hz : InBox m z) :
    softWeight line inner offset slope smallOffset smallSlope L (reflect m z) =
      softWeight line inner
        (fun g => offset g+(lineTotal line m g:ℝ)*slope g) (fun g => -slope g)
        (fun g => smallOffset g+(smallTotal line inner m g:ℝ)*smallSlope g)
        (fun g => -smallSlope g) L z := by
  unfold softWeight nestedWeight ScalarPenalty.factor
  congr 1
  · apply Finset.prod_congr rfl
    intro g _
    dsimp only
    rw [affine_reflect (offset g) (slope g) _ _ _ (lineTotal_reflect_add line m z hz g)]
  · apply Finset.prod_congr rfl
    intro g _
    dsimp only
    rw [affine_reflect (smallOffset g) (smallSlope g) _ _ _ (smallTotal_reflect_add line inner m z hz g)]

theorem reflected_soft_removal (line : C → G) (inner : C → Bool)
    (offset slope smallOffset smallSlope : G → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (m z : C → ℕ) (hz : InBox m z) :
    OnePositiveDirection (integerRemovalMatrix
      (fun x => softWeight line inner offset slope smallOffset smallSlope L (reflect m x)) z).toBilin' := by
  rw [removal_congr_box _ _ m z hz (fun x hx => softWeight_reflect line inner offset slope smallOffset smallSlope L m x hx)]
  exact softWeight_removal line inner
    (fun g => offset g+(lineTotal line m g:ℝ)*slope g) (fun g => -slope g)
    (fun g => smallOffset g+(smallTotal line inner m g:ℝ)*smallSlope g)
    (fun g => -smallSlope g) L hL z

variable {I : Type*} [Fintype I]

theorem reflected_soft_marginal (Ms : List ℕ) (m : I → ℕ) (R : ℕ)
    (line : Coordinates I Ms → G) (inner : Coordinates I Ms → Bool)
    (offset slope smallOffset smallSlope : G → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hwidth : ∀ M ∈ Ms, 2 ≤ M) :
    RemovalSlice (fun z => eliminate Ms
      (softWeight line inner offset slope smallOffset smallSlope L) (reflect m z)) m R := by
  let F := softWeight line inner offset slope smallOffset smallSlope L
  have hp : PositiveSlice (fun x => F (reflect (bounds m Ms) x)) (bounds m Ms) (R+Ms.sum) := by
    intro x _ _
    exact softWeight_positive line inner offset slope smallOffset smallSlope L _
  have hs : RemovalSlice (fun x => F (reflect (bounds m Ms) x)) (bounds m Ms) (R+Ms.sum) := by
    intro x hx _
    convert reflected_soft_removal line inner offset slope smallOffset smallSlope L hL (bounds m Ms) x hx using 1
    congr 2 <;> exact Subsingleton.elim _ _
  have h := (eliminate_slices Ms m R _ hwidth hp hs).2
  have he : eliminate Ms (fun x => F (reflect (bounds m Ms) x)) =
      fun z => eliminate Ms F (reflect m z) := by
    funext z
    exact eliminate_reflect Ms m F z
  rwa [he] at h

theorem reflected_hard_marginal (Ms : List ℕ) (m : I → ℕ) (R : ℕ)
    (line : Coordinates I Ms → G) (inner : Coordinates I Ms → Bool)
    (offset slope smallOffset smallSlope : G → ℝ) (hwidth : ∀ M ∈ Ms, 2 ≤ M) :
    RemovalSlice (fun z => eliminate Ms
      (hardWeight line inner offset slope smallOffset smallSlope) (reflect m z)) m R := by
  intro z hz ht
  apply IntegerMarginal.removal_signature_limit (l := (atTop : Filter ℝ))
    (fun L x => eliminate Ms (softWeight line inner offset slope smallOffset smallSlope L) (reflect m x))
    (fun x => eliminate Ms (hardWeight line inner offset slope smallOffset smallSlope) (reflect m x)) z
  · intro x
    exact eliminate_tendsto Ms _ _
      (softWeight_tendsto line inner offset slope smallOffset smallSlope) (reflect m x)
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
    exact reflected_soft_marginal Ms m R line inner offset slope smallOffset smallSlope L hL hwidth z hz ht

/-- Both actual positive factorial lifts have their original manuscript
degree and signature conventions, derived from the explicit penalties. -/
theorem softened_twoLift_data {A : Type*} [Fintype A] (group : A → I)
    (Ms : List ℕ) (R : ℕ) (hR : R ≤ Fintype.card A) (D : ℝ) (hD : 0 < D)
    (line : Coordinates I Ms → G) (inner : Coordinates I Ms → Bool)
    (offset slope smallOffset smallSlope : G → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hwidth : ∀ M ∈ Ms, 2 ≤ M) :
    let h := eliminate Ms (softWeight line inner offset slope smallOffset smallSlope L)
    BinaryContraction.DegreePositive (firstLift group h D) R ∧
      BinaryContraction.OmissionProperty (firstLift group h D) R ∧
      BinaryContraction.AdditionProperty (secondLift group h D) R := by
  have hf := softened_firstLift_data group Ms R D hD line inner offset slope smallOffset smallSlope L hL hwidth
  refine ⟨hf.1,hf.2,?_⟩
  apply secondLift_addition_reflected_slice group _ D R hR hD
  · intro z
    exact eliminate_nonnegative Ms _ (fun x => (softWeight_positive line inner offset slope smallOffset smallSlope L x).le) z
  · exact reflected_soft_marginal Ms (groupCount group Set.univ) (Fintype.card A-R)
      line inner offset slope smallOffset smallSlope L hL hwidth

end ContingencyTables.ReflectedNested

end OAI
