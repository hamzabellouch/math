import OAI.Combinatorics.ContingencyTables.Transport.EqualityReindex
import OAI.Combinatorics.ContingencyTables.Transport.NestedPenaltyApplication
import OAI.Combinatorics.ContingencyTables.Transport.ReflectedNested

namespace OAI

/-! # Physical coordinate reindexing of the first paper's nested penalties -/

namespace ContingencyTables.NestedReindex

open scoped BigOperators Classical
open ProductIntegerSignature NestedProductSignature NestedPenaltyApplication
open BalancedFamily BalancedBox EqualityReindex

variable {C D G : Type*} [Fintype C] [Fintype D] [Fintype G]

omit [Fintype G] in
lemma smallTotal_reindex (e : C ≃ D) (line : D → G) (inner : D → Bool)
    (z : C → ℕ) (g : G) :
    smallTotal (line ∘ e) (inner ∘ e) z g=smallTotal line inner (z ∘ e.symm) g := by
  exact lineTotal_reindex e (fun d => (line d,inner d)) z (g,true)

lemma penalty_reindex (e : C ≃ D) (line : D → G) (inner : D → Bool)
    (offset slope smallOffset smallSlope : G → ℝ) (z : C → ℕ) :
    penalty (line ∘ e) (inner ∘ e) offset slope smallOffset smallSlope z=
      penalty line inner offset slope smallOffset smallSlope (z ∘ e.symm) := by
  unfold penalty
  simp_rw [lineTotal_reindex,smallTotal_reindex]

lemma hardWeight_reindex (e : C ≃ D) (line : D → G) (inner : D → Bool)
    (offset slope smallOffset smallSlope : G → ℝ) (z : C → ℕ) :
    hardWeight (line ∘ e) (inner ∘ e) offset slope smallOffset smallSlope z=
      hardWeight line inner offset slope smallOffset smallSlope (z ∘ e.symm) := by
  unfold hardWeight
  rw [penalty_reindex]

lemma softWeight_reindex (e : C ≃ D) (line : D → G) (inner : D → Bool)
    (offset slope smallOffset smallSlope : G → ℝ) (L : ℝ) (z : C → ℕ) :
    softWeight (line ∘ e) (inner ∘ e) offset slope smallOffset smallSlope L z=
      softWeight line inner offset slope smallOffset smallSlope L (z ∘ e.symm) := by
  rw [softWeight_eq,softWeight_eq,penalty_reindex]

variable {S : Type*} [Fintype S] [DecidableEq S]

omit [Fintype S] in
/-- Box congruence with the ambient equality decision used by the actual
physical view type. -/
lemma removal_congr_box (f h : (S → ℕ) → ℝ) (m z : S → ℕ) (hz : InBox m z)
    (heq : ∀ x, InBox m x → f x=h x) :
    FactorialSignatures.integerRemovalMatrix f z=FactorialSignatures.integerRemovalMatrix h z := by
  have hd : (inferInstance : DecidableEq S)=Classical.decEq S := Subsingleton.elim _ _
  cases hd
  ext i j
  unfold FactorialSignatures.integerRemovalMatrix
  split_ifs with hv
  · exact heq _ (IntegerBoxTruncation.removal_inBox m z hz i j)
  · rfl

theorem physical_soft_marginal_slices (Ms : List ℕ) (m : S → ℕ) (R : ℕ)
    (e : Coordinates S Ms ≃ D) (line : D → G) (inner : D → Bool)
    (offset slope smallOffset smallSlope : G → ℝ) (L : ℝ) (hL : 0≤L)
    (hwidth : ∀ M ∈ Ms, 2≤M) :
    PositiveSlice (eliminate Ms (fun z =>
      softWeight line inner offset slope smallOffset smallSlope L (z ∘ e.symm))) m R ∧
    RemovalSlice (eliminate Ms (fun z =>
      softWeight line inner offset slope smallOffset smallSlope L (z ∘ e.symm))) m R := by
  have hd : (inferInstance : DecidableEq S)=Classical.decEq S := Subsingleton.elim _ _
  cases hd
  have heq : (fun z => softWeight line inner offset slope smallOffset smallSlope L
      (z ∘ e.symm))=softWeight (line ∘ e) (inner ∘ e) offset slope smallOffset smallSlope L := by
    funext z
    exact (softWeight_reindex e line inner offset slope smallOffset smallSlope L z).symm
  rw [heq]
  exact softened_marginal_slices Ms m R (line ∘ e) (inner ∘ e)
    offset slope smallOffset smallSlope L hL hwidth

theorem physical_hard_marginal_removal (Ms : List ℕ) (m : S → ℕ) (R : ℕ)
    (e : Coordinates S Ms ≃ D) (line : D → G) (inner : D → Bool)
    (offset slope smallOffset smallSlope : G → ℝ) (hwidth : ∀ M ∈ Ms, 2≤M) :
    RemovalSlice (eliminate Ms (fun z =>
      hardWeight line inner offset slope smallOffset smallSlope (z ∘ e.symm))) m R := by
  have hd : (inferInstance : DecidableEq S)=Classical.decEq S := Subsingleton.elim _ _
  cases hd
  have heq : (fun z => hardWeight line inner offset slope smallOffset smallSlope
      (z ∘ e.symm))=hardWeight (line ∘ e) (inner ∘ e) offset slope smallOffset smallSlope := by
    funext z
    exact (hardWeight_reindex e line inner offset slope smallOffset smallSlope z).symm
  rw [heq]
  exact hard_marginal_removal Ms m R (line ∘ e) (inner ∘ e) offset slope smallOffset smallSlope hwidth

theorem physical_hard_marginal_reflected (Ms : List ℕ) (m : S → ℕ) (R : ℕ)
    (e : Coordinates S Ms ≃ D) (line : D → G) (inner : D → Bool)
    (offset slope smallOffset smallSlope : G → ℝ) (hwidth : ∀ M ∈ Ms, 2≤M) :
    RemovalSlice (fun z => eliminate Ms (fun q =>
      hardWeight line inner offset slope smallOffset smallSlope (q ∘ e.symm))
      (IntegerReflection.reflect m z)) m R := by
  have hd : (inferInstance : DecidableEq S)=Classical.decEq S := Subsingleton.elim _ _
  cases hd
  have heq : (fun z => hardWeight line inner offset slope smallOffset smallSlope
      (z ∘ e.symm))=hardWeight (line ∘ e) (inner ∘ e) offset slope smallOffset smallSlope := by
    funext z
    exact (hardWeight_reindex e line inner offset slope smallOffset smallSlope z).symm
  rw [heq]
  exact ReflectedNested.reflected_hard_marginal Ms m R (line ∘ e) (inner ∘ e)
    offset slope smallOffset smallSlope hwidth

end ContingencyTables.NestedReindex

end OAI
