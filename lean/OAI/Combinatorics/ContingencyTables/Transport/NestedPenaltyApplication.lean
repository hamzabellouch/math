import OAI.Combinatorics.ContingencyTables.Transport.NestedProductSignature
import OAI.Combinatorics.ContingencyTables.Transport.ScalarPenalty
import OAI.Combinatorics.ContingencyTables.Transport.BalancedFamily
import OAI.Combinatorics.ContingencyTables.Transport.IntegerBoxTruncation
import OAI.Combinatorics.ContingencyTables.Transport.SliceFactorial
import OAI.Combinatorics.ContingencyTables.Transport.HardZeroTransport

namespace OAI

/-!
# The first paper's actual positive penalties and hard equality limit

Full row/column deviations give absolute affine line factors; the nested
small-slot residual constraints give positive-part affine factors. Their
product is exactly 2^(-L D). Balanced large-slot sums retain their proved
signature, and their finite limit is the exact zero-penalty indicator sum.
-/

namespace ContingencyTables.NestedPenaltyApplication

open scoped BigOperators Classical Matrix Topology
open Filter CommonBasesFPRAS FactorialSignatures ProductIntegerSignature
open NestedProductSignature ScalarPenalty IntegerMarginal BalancedBox BalancedFamily

variable {C G : Type*} [Fintype C] [Fintype G]

noncomputable def penalty (line : C → G) (inner : C → Bool)
    (offset slope smallOffset smallSlope : G → ℝ) (z : C → ℕ) : ℝ :=
  (∑ g, |offset g+(lineTotal line z g:ℝ)*slope g|)+
    ∑ g, max (smallOffset g+(smallTotal line inner z g:ℝ)*smallSlope g) 0

noncomputable def softWeight (line : C → G) (inner : C → Bool)
    (offset slope smallOffset smallSlope : G → ℝ) (L : ℝ) : (C → ℕ) → ℝ :=
  nestedWeight line inner
    (fun g => factor L (fun n => |offset g+(n:ℝ)*slope g|))
    (fun g => factor L (fun n => max (smallOffset g+(n:ℝ)*smallSlope g) 0))

noncomputable def hardWeight (line : C → G) (inner : C → Bool)
    (offset slope smallOffset smallSlope : G → ℝ) (z : C → ℕ) : ℝ :=
  if penalty line inner offset slope smallOffset smallSlope z=0 then 1 else 0

lemma penalty_nonnegative (line : C → G) (inner : C → Bool)
    (offset slope smallOffset smallSlope : G → ℝ) (z : C → ℕ) :
    0 ≤ penalty line inner offset slope smallOffset smallSlope z := by
  apply add_nonneg <;> apply Finset.sum_nonneg
  · intro g _; exact abs_nonneg _
  · intro g _; exact le_max_right _ _

private lemma prod_pow (L : ℝ) (p : G → ℝ) :
    (∏ g, (2:ℝ)^(-L*p g))=(2:ℝ)^(-L*∑ g, p g) := by
  rw [← Real.rpow_sum_of_pos (by norm_num : (0:ℝ)<2)]
  congr 1
  rw [Finset.mul_sum]

/-- This is the manuscript's literal exponential of the full deviation
plus the small residual violation penalty, with eta=2^(-L). -/
theorem softWeight_eq (line : C → G) (inner : C → Bool)
    (offset slope smallOffset smallSlope : G → ℝ) (L : ℝ) (z : C → ℕ) :
    softWeight line inner offset slope smallOffset smallSlope L z =
      (2:ℝ)^(-L*penalty line inner offset slope smallOffset smallSlope z) := by
  unfold softWeight nestedWeight factor penalty
  rw [prod_pow,prod_pow,← Real.rpow_add (by norm_num : (0:ℝ)<2)]
  congr 1
  ring

lemma softWeight_positive (line : C → G) (inner : C → Bool)
    (offset slope smallOffset smallSlope : G → ℝ) (L : ℝ) (z : C → ℕ) :
    0 < softWeight line inner offset slope smallOffset smallSlope L z := by
  rw [softWeight_eq]
  exact Real.rpow_pos_of_pos (by norm_num) _

theorem softWeight_removal (line : C → G) (inner : C → Bool)
    (offset slope smallOffset smallSlope : G → ℝ) (L : ℝ) (hL : 0 ≤ L) (z : C → ℕ) :
    OnePositiveDirection
      (integerRemovalMatrix (softWeight line inner offset slope smallOffset smallSlope L) z).toBilin' := by
  apply nested_product_removal_onePositive line inner
  · intro g n _; exact factor_positive _ _ _
  · intro g n _; exact factor_positive _ _ _
  · intro g hn; exact abs_factor_logConcave L (offset g) (slope g) hL _ hn
  · intro g hn; exact positivePart_factor_logConcave L (smallOffset g) (smallSlope g) hL _ hn

theorem softWeight_tendsto (line : C → G) (inner : C → Bool)
    (offset slope smallOffset smallSlope : G → ℝ) (z : C → ℕ) :
    Tendsto (fun L : ℝ => softWeight line inner offset slope smallOffset smallSlope L z) atTop
      (nhds (hardWeight line inner offset slope smallOffset smallSlope z)) := by
  simp_rw [softWeight_eq]
  exact factor_limit _ (penalty_nonnegative line inner offset slope smallOffset smallSlope z)

variable {I : Type*} [Fintype I]

/-- The actual softened marginal is positive before the hard limit and
has the raw integer removal signature on every required display. -/
theorem softened_marginal_slices (Ms : List ℕ) (m : I → ℕ) (R : ℕ)
    (line : Coordinates I Ms → G) (inner : Coordinates I Ms → Bool)
    (offset slope smallOffset smallSlope : G → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hwidth : ∀ M ∈ Ms, 2 ≤ M) :
    PositiveSlice (eliminate Ms (softWeight line inner offset slope smallOffset smallSlope L)) m R ∧
      RemovalSlice (eliminate Ms (softWeight line inner offset slope smallOffset smallSlope L)) m R := by
  apply eliminate_slices Ms m R _ hwidth
  · intro z _ _; exact softWeight_positive line inner offset slope smallOffset smallSlope L z
  · intro z _ _
    convert softWeight_removal line inner offset slope smallOffset smallSlope L hL z using 1
    congr 2 <;> exact Subsingleton.elim _ _

/-- The first paper's hard-zero finite marginal inherits its actual raw
signature. This proves the required input to factorial omission lifting. -/
theorem hard_marginal_removal (Ms : List ℕ) (m : I → ℕ) (R : ℕ)
    (line : Coordinates I Ms → G) (inner : Coordinates I Ms → Bool)
    (offset slope smallOffset smallSlope : G → ℝ)
    (hwidth : ∀ M ∈ Ms, 2 ≤ M) :
    RemovalSlice (eliminate Ms (hardWeight line inner offset slope smallOffset smallSlope)) m R := by
  intro z hz htotal
  apply removal_signature_limit (l := (atTop : Filter ℝ))
    (fun L => eliminate Ms (softWeight line inner offset slope smallOffset smallSlope L))
    (eliminate Ms (hardWeight line inner offset slope smallOffset smallSlope)) z
  · intro x
    exact eliminate_tendsto Ms _ _ (softWeight_tendsto line inner offset slope smallOffset smallSlope) x
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
    exact (softened_marginal_slices Ms m R line inner offset slope smallOffset smallSlope L hL hwidth).2
      z hz htotal

/-- Zero extension outside the box and full total gives precisely the
same actual softened marginal on its required state slice. -/
theorem truncate_softened_marginal (Ms : List ℕ) (m : I → ℕ) (R : ℕ)
    (line : Coordinates I Ms → G) (inner : Coordinates I Ms → Bool)
    (offset slope smallOffset smallSlope : G → ℝ) (L : ℝ)
    (z : I → ℕ) (hz : InBox m z) (htotal : (∑ i, z i)=R) :
    eliminate Ms
      (IntegerBoxTruncation.truncate
        (softWeight line inner offset slope smallOffset smallSlope L) (bounds m Ms) (R+Ms.sum)) z =
      eliminate Ms (softWeight line inner offset slope smallOffset smallSlope L) z := by
  apply eliminate_congr_slice Ms m R _ _ _ z hz htotal
  intro x hx ht
  exact ite_eq_left ⟨hx,ht⟩

/-- The actual softened factorial lift now has both required properties
by the integer proofs above; neither binary property is assumed. -/
theorem softened_firstLift_data {L : Type*} [Fintype L] (group : L → I)
    (Ms : List ℕ) (R : ℕ) (D : ℝ) (hD : 0 < D)
    (line : Coordinates I Ms → G) (inner : Coordinates I Ms → Bool)
    (offset slope smallOffset smallSlope : G → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hwidth : ∀ M ∈ Ms, 2 ≤ M) :
    let f := LabelledFactorial.firstLift group
      (eliminate Ms (softWeight line inner offset slope smallOffset smallSlope a)) D
    BinaryContraction.DegreePositive f R ∧ BinaryContraction.OmissionProperty f R := by
  have hs := softened_marginal_slices Ms (LabelledFactorial.groupCount group Set.univ) R
    line inner offset slope smallOffset smallSlope a ha hwidth
  exact ⟨SliceFactorial.firstLift_degreePositive group _ D R hD hs.1,
    SliceFactorial.firstLift_omission_slice group _ D R hD
      (fun z => eliminate_nonnegative Ms _
        (fun x => (softWeight_positive line inner offset slope smallOffset smallSlope a x).le) z) hs.2⟩

/-- These are the literal subset weights consumed by endpoint-positive
hard-zero transport, with no positivity requirement on internal limits. -/
theorem firstLift_limit {L : Type*} [Fintype L] (group : L → I)
    (Ms : List ℕ) (D : ℝ) (line : Coordinates I Ms → G) (inner : Coordinates I Ms → Bool)
    (offset slope smallOffset smallSlope : G → ℝ) (S : Set L) :
    Tendsto (fun a : ℝ => LabelledFactorial.firstLift group
      (eliminate Ms (softWeight line inner offset slope smallOffset smallSlope a)) D S) atTop
      (nhds (LabelledFactorial.firstLift group
        (eliminate Ms (hardWeight line inner offset slope smallOffset smallSlope)) D S)) := by
  apply SliceFactorial.firstLift_tendsto
  intro z
  exact eliminate_tendsto Ms _ _
    (softWeight_tendsto line inner offset slope smallOffset smallSlope) z

/-- Actual first-paper hard transport. The positive softened factorial
properties are proved above from the explicit deviation penalties. Only
the two hard limiting endpoint masses are required to be positive. -/
theorem hard_firstLift_transport {L : Type*} [Fintype L]
    (group : L → I) (Ms : List ℕ) (R : ℕ) (D : ℝ) (hD : 0 < D)
    (line : Coordinates I Ms → G) (inner : Coordinates I Ms → Bool)
    (offset slope smallOffset smallSlope : G → ℝ) (hwidth : ∀ M ∈ Ms, 2 ≤ M)
    (ps : List (L × L)) (H : Set L → ℝ) (A : Set L) (p d : L) (W : L → ℝ)
    (hR : R ≤ Fintype.card L) (hdegree : A.ncard+ps.length+1=Fintype.card L-R)
    (hpd : p≠d) (hpA : p∉A) (hdA : d∉A)
    (hps : CommonBasesFPRAS.SlotsFresh ps (A ∪ Set.range (CommonBasesFPRAS.rootEmbedding p d)))
    (hW : ∀ i, 0 < W i) (hw : ∀ a∈ps, W a.1=W a.2)
    (hsp : 0 < CommonBasesFPRAS.slotTotal ps
      (BinaryContraction.complementWeight (LabelledFactorial.firstLift group
        (eliminate Ms (hardWeight line inner offset slope smallOffset smallSlope)) D)) (insert p A))
    (hsd : 0 < CommonBasesFPRAS.slotTotal ps
      (BinaryContraction.complementWeight (LabelledFactorial.firstLift group
        (eliminate Ms (hardWeight line inner offset slope smallOffset smallSlope)) D)) (insert d A)) :
    let f := BinaryContraction.complementWeight (LabelledFactorial.firstLift group
      (eliminate Ms (hardWeight line inner offset slope smallOffset smallSlope)) D)
    let Hc := BinaryContraction.complementWeight H
    (CommonBasesFPRAS.slotTotal ps (fun S => f S*Hc S) (insert p A)/
        CommonBasesFPRAS.slotTotal ps f (insert p A)-
      CommonBasesFPRAS.slotTotal ps (fun S => f S*Hc S) (insert d A)/
        CommonBasesFPRAS.slotTotal ps f (insert d A))^2 ≤
      CommonBasesFPRAS.rootCoefficient ps f A p d W*
        CommonBasesFPRAS.slotGraphEnergy ps f Hc A (CommonBasesFPRAS.rootEmbedding p d) W := by
  apply HardZeroTransport.one_hole_transport_limit (l := (atTop : Filter ℝ)) ps
    (fun a => LabelledFactorial.firstLift group
      (eliminate Ms (softWeight line inner offset slope smallOffset smallSlope a)) D)
    (LabelledFactorial.firstLift group
      (eliminate Ms (hardWeight line inner offset slope smallOffset smallSlope)) D) H
    (firstLift_limit group Ms D line inner offset slope smallOffset smallSlope)
    A p d W R hR
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with a ha
    exact softened_firstLift_data group Ms R D hD line inner offset slope smallOffset smallSlope a ha hwidth
  · exact hdegree
  · exact hpd
  · exact hpA
  · exact hdA
  · exact hps
  · exact hW
  · exact hw
  · exact hsp
  · exact hsd

end ContingencyTables.NestedPenaltyApplication

end OAI
