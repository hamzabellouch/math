import OAI.Combinatorics.ContingencyTables.Transport.EqualitySoftening
import OAI.Combinatorics.ContingencyTables.Transport.SliceFactorial
import OAI.Combinatorics.ContingencyTables.Transport.IntegerBoxTruncation

namespace OAI

/-!
# Reflected actual penalties and the complementary factorial lift

Reflecting a physical box changes affine offsets and reverses their
slopes. The root/equality and unary interval factors therefore have the
same proved scalar signatures. All finite balanced pairs are reflected
as well, before transferring the resulting addition signature to labels.
-/

namespace ContingencyTables.ReflectedSlices

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS FactorialSignatures ProductIntegerSignature
open IntegerReflection EqualitySoftening BalancedBox BalancedFamily LabelledFactorial

variable {C G : Type*} [Fintype C] [Fintype G]

omit [Fintype G] in
lemma lineTotal_reflect_add (line : C → G) (m z : C → ℕ) (hz : InBox m z) (g : G) :
    lineTotal line (reflect m z) g+lineTotal line z g=lineTotal line m g := by
  unfold lineTotal reflect
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : line i=g
  · simp only [hi,ite_true]
    exact Nat.sub_add_cancel (hz i)
  · simp only [hi,ite_false,add_zero]

lemma affine_reflect (a slope : ℝ) (M r n : ℕ) (h : r+n=M) :
    a+(r:ℝ)*slope=(a+(M:ℝ)*slope)+(n:ℝ)*(-slope) := by
  have hh : (r:ℝ)+(n:ℝ)=M := by exact_mod_cast h
  rw [← hh]
  ring

theorem softenedWeight_reflect (line : C → G) (root : G → Bool)
    (rate offset slope : G → ℝ) (urate ell uslope cap : C → ℝ) (L : ℝ)
    (m z : C → ℕ) (hz : InBox m z) :
    softenedWeight line root rate offset slope urate ell uslope cap L (reflect m z) =
      softenedWeight line root rate
        (fun g => offset g+(lineTotal line m g:ℝ)*slope g) (fun g => -slope g)
        urate (fun i => ell i+(m i:ℝ)*uslope i) (fun i => -uslope i) cap L z := by
  unfold softenedWeight productWeight
  congr 1
  · apply Finset.prod_congr rfl
    intro g _
    unfold lineFactor ScalarPenalty.factor
    dsimp only
    rw [affine_reflect (offset g) (slope g) _ _ _ (lineTotal_reflect_add line m z hz g)]
  · apply Finset.prod_congr rfl
    intro i _
    unfold unaryFactor ScalarPenalty.factor affineDistance reflect
    dsimp only
    rw [affine_reflect (ell i) (uslope i) (m i) (m i-z i) (z i) (Nat.sub_add_cancel (hz i))]

omit [Fintype G] [Fintype C] in
lemma removal_congr_box (f h : (C → ℕ) → ℝ) (m z : C → ℕ) (hz : InBox m z)
    (heq : ∀ x, InBox m x → f x=h x) : integerRemovalMatrix f z=integerRemovalMatrix h z := by
  ext i j
  unfold integerRemovalMatrix
  split_ifs with hv
  · exact heq _ (IntegerBoxTruncation.removal_inBox m z hz i j)
  · rfl

/-- The original globally reflected positive weight has its raw removal
signature throughout the physical box, from explicit reflected factors. -/
theorem reflected_softened_removal (line : C → G) (root : G → Bool)
    (rate offset slope : G → ℝ) (urate ell uslope cap : C → ℝ) (L : ℝ)
    (hrate : ∀ g, 0 ≤ rate g) (hu : ∀ i, 0 ≤ urate i) (hL : 0 ≤ L)
    (m z : C → ℕ) (hz : InBox m z) :
    OnePositiveDirection (integerRemovalMatrix
      (fun x => softenedWeight line root rate offset slope urate ell uslope cap L (reflect m x)) z).toBilin' := by
  rw [removal_congr_box _ _ m z hz (fun x hx => softenedWeight_reflect line root rate offset slope
    urate ell uslope cap L m x hx)]
  exact softenedWeight_removal line root rate
    (fun g => offset g+(lineTotal line m g:ℝ)*slope g) (fun g => -slope g)
    urate (fun i => ell i+(m i:ℝ)*uslope i) (fun i => -uslope i) cap L hrate hu hL z

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The companion's actual positive finite marginal has the reflected
removal signature needed for its two-addition matrix. -/
theorem reflected_softened_marginal (Ms : List ℕ) (m : I → ℕ) (R : ℕ)
    (line : Coordinates I Ms → G) (root : G → Bool) (rate offset slope : G → ℝ)
    (urate ell uslope cap : Coordinates I Ms → ℝ) (L : ℝ)
    (hwidth : ∀ M ∈ Ms, 2 ≤ M) (hrate : ∀ g, 0 ≤ rate g)
    (hu : ∀ i, 0 ≤ urate i) (hL : 0 ≤ L) :
    RemovalSlice
      (fun z => eliminate Ms (softenedWeight line root rate offset slope urate ell uslope cap L)
        (reflect m z)) m R := by
  let F := softenedWeight line root rate offset slope urate ell uslope cap L
  have hp : PositiveSlice (fun x => F (reflect (bounds m Ms) x)) (bounds m Ms) (R+Ms.sum) := by
    intro x _ _
    exact softenedWeight_positive line root rate offset slope urate ell uslope cap L _
  have hs : RemovalSlice (fun x => F (reflect (bounds m Ms) x)) (bounds m Ms) (R+Ms.sum) := by
    intro x hx _
    convert reflected_softened_removal line root rate offset slope urate ell uslope cap L
      hrate hu hL (bounds m Ms) x hx using 1
    congr 2 <;> exact Subsingleton.elim _ _
  have h := (eliminate_slices Ms m R _ hwidth hp hs).2
  have he : eliminate Ms (fun x => F (reflect (bounds m Ms) x)) =
      fun z => eliminate Ms F (reflect m z) := by
    funext z
    exact eliminate_reflect Ms m F z
  rwa [he] at h

/-- The reflected addition input survives the nonroot-equality limit
after all balanced large-cell sums, exactly as the removal input does. -/
theorem reflected_exact_marginal (Ms : List ℕ) (m : I → ℕ) (R : ℕ)
    (line : Coordinates I Ms → G) (root : G → Bool) (rate offset slope : G → ℝ)
    (urate ell uslope cap : Coordinates I Ms → ℝ)
    (hwidth : ∀ M ∈ Ms, 2 ≤ M) (hrate : ∀ g, 0 ≤ rate g) (hu : ∀ i, 0 ≤ urate i) :
    RemovalSlice
      (fun z => eliminate Ms (exactWeight line root rate offset slope urate ell uslope cap)
        (reflect m z)) m R := by
  intro z hz ht
  apply IntegerMarginal.removal_signature_limit (l := (Filter.atTop : Filter ℝ))
    (fun L x => eliminate Ms (softenedWeight line root rate offset slope urate ell uslope cap L)
      (reflect m x))
    (fun x => eliminate Ms (exactWeight line root rate offset slope urate ell uslope cap)
      (reflect m x)) z
  · intro x
    exact eliminate_tendsto Ms _ _
      (softenedWeight_tendsto line root rate offset slope urate ell uslope cap) (reflect m x)
  · filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with L hL
    exact reflected_softened_marginal Ms m R line root rate offset slope urate ell uslope cap L
      hwidth hrate hu hL z hz ht

variable {A : Type*} [Fintype A]

omit [Fintype I] [DecidableEq I] [Fintype G] [Fintype C] in
lemma groupCount_complement (group : A → C) (S : Set A) (c : C) :
    groupCount group S c+groupCount group Sᶜ c=groupCount group Set.univ c := by
  unfold groupCount
  simp_rw [Finset.card_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hg : group a=c <;> by_cases hs : a∈S <;> simp [hg,hs]

omit [Fintype I] [DecidableEq I] [Fintype G] in
/-- The actual reflected raw slice proves the addition property of the
literal complementary-factorial lift in the original coordinates. -/
theorem secondLift_addition_reflected_slice (group : A → C) (h : (C → ℕ) → ℝ)
    (D : ℝ) (R : ℕ) (hR : R ≤ Fintype.card A) (hD : 0 < D) (hh : ∀ z, 0 ≤ h z)
    (hsig : RemovalSlice (fun z => h (reflect (groupCount group Set.univ) z))
      (groupCount group Set.univ) (Fintype.card A-R)) :
    BinaryContraction.AdditionProperty (secondLift group h D) R := by
  apply secondLift_addition group h D R hD hh
  intro S hS
  apply addition_onePositive_of_reflection h (groupCount group Set.univ)
    (groupCount group S) (groupCount group Sᶜ) (groupCount_complement group S)
  apply hsig _ (SliceFactorial.groupCount_inBox group Sᶜ)
  rw [groupCount_total]
  have hc := Set.ncard_add_ncard_compl S
  simp only [Nat.card_eq_fintype_card] at hc
  omega

end ContingencyTables.ReflectedSlices

end OAI
