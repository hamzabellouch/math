import OAI.Combinatorics.ContingencyTables.Transport.IntegerTransportLimit
import OAI.Combinatorics.ContingencyTables.Transport.PositiveSequenceMinimum

namespace OAI

/-! # Conditional child masses have no internal valley

The actual two-coordinate removal form gives the local log-concavity
inequality. The endpoint-minimum property passes to the hard-zero limit.
-/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical Topology Matrix
open CommonBasesFPRAS FactorialSignatures IntegerMarginal BalancedBox Filter

def childProfile (U k : ℕ) : Bool → ℕ := fun b => if b then U-k else k

lemma bool_diagonal_product (A : Matrix Bool Bool ℝ)
    (hsymm : ∀ i j, A i j=A j i) (hsig : OnePositiveDirection A.toBilin')
    (haa : 0 < A false false) : A false false*A true true ≤ (A false true)^2 := by
  let ea : Bool → ℝ := Pi.single false 1
  let eb : Bool → ℝ := Pi.single true 1
  have ha : 0 < A.toBilin' ea ea := by
    simpa [ea,Matrix.toBilin'_apply] using haa
  have hp := (le_div_iff₀ ha).mp
    (positive_projection A.toBilin' (fun x y => (matrix_bilin_symm A hsymm).eq x y) hsig ea eb ha)
  simpa [ea,eb,Matrix.toBilin'_apply,mul_comm] using hp

lemma childProfile_inBox (U k : ℕ) (hk : k ≤ U) :
    InBox (fun _ : Bool => U) (childProfile U k) := by
  intro b
  cases b
  · exact hk
  · exact Nat.sub_le _ _

lemma childProfile_total (U k : ℕ) (hk : k ≤ U) : (∑ b, childProfile U k b)=U := by
  simp only [Fintype.sum_bool,childProfile,Bool.false_eq_true,↓reduceIte]
  omega

theorem child_logConcave (f : (Bool → ℕ) → ℝ) (U : ℕ)
    (hp : PositiveSlice f (fun _ => U) U) (hs : RemovalSlice f (fun _ => U) U)
    (k : ℕ) (hk : k+2 ≤ U) :
    f (childProfile U k)*f (childProfile U (k+2)) ≤ (f (childProfile U (k+1)))^2 := by
  let D : Bool → ℕ := fun b => if b then U-k else k+2
  have hDbox : InBox (fun _ : Bool => U) D := by
    intro b
    cases b
    · exact hk
    · exact Nat.sub_le _ _
  have hDsum : (∑ b, D b)=U+2 := by
    simp only [D,Fintype.sum_bool,Bool.false_eq_true,↓reduceIte]
    omega
  have hsig := hs D hDbox hDsum
  have haa : integerRemovalMatrix f D false false=f (childProfile U k) := by
    have hv : ValidPair D false false := by simp [ValidPair,D]
    rw [integerRemovalMatrix,ite_eq_left hv]
    congr 1
    funext b
    cases b <;> simp [removeTwo,removeOne,D,childProfile]
  have hbb : integerRemovalMatrix f D true true=f (childProfile U (k+2)) := by
    have hv : ValidPair D true true := by simp [ValidPair,D]; omega
    rw [integerRemovalMatrix,ite_eq_left hv]
    congr 1
    funext b
    cases b
    · simp [removeTwo,removeOne,D,childProfile]
    · simp [removeTwo,removeOne,D,childProfile]
      omega
  have hab : integerRemovalMatrix f D false true=f (childProfile U (k+1)) := by
    have hv : ValidPair D false true := by simp [ValidPair,D]; omega
    rw [integerRemovalMatrix,ite_eq_left hv]
    congr 1
    funext b
    cases b
    · simp [removeTwo,removeOne,D,childProfile]
    · simp [removeTwo,removeOne,D,childProfile]
      omega
  have hpos : 0 < integerRemovalMatrix f D false false := by
    rw [haa]
    exact hp _ (childProfile_inBox U k (by omega)) (childProfile_total U k (by omega))
  have hdet := bool_diagonal_product _ (integerRemoval_symm f D) hsig hpos
  rwa [haa,hbb,hab] at hdet

theorem child_minimum (f : (Bool → ℕ) → ℝ) (U : ℕ)
    (hp : PositiveSlice f (fun _ => U) U) (hs : RemovalSlice f (fun _ => U) U)
    (a j b : ℕ) (haj : a ≤ j) (hjb : j ≤ b) (hbU : b ≤ U) :
    min (f (childProfile U a)) (f (childProfile U b)) ≤ f (childProfile U j) := by
  apply positive_sequence_minimum (fun k => f (childProfile U k)) U a j b
  · intro k hk
    exact hp _ (childProfile_inBox U k hk) (childProfile_total U k hk)
  · exact child_logConcave f U hp hs
  · exact haj
  · exact hjb
  · exact hbU

/-- Every mass between two positive hard children is at least the
smaller endpoint mass, including when other children have zero weight. -/
theorem child_minimum_limit {K : Type*} {l : Filter K} [l.NeBot]
    (F : K → (Bool → ℕ) → ℝ) (f : (Bool → ℕ) → ℝ) (U : ℕ)
    (hlim : ∀ z, Tendsto (fun t => F t z) l (nhds (f z)))
    (hsoft : ∀ᶠ t in l, PositiveSlice (F t) (fun _ => U) U ∧
      RemovalSlice (F t) (fun _ => U) U)
    (a j b : ℕ) (haj : a ≤ j) (hjb : j ≤ b) (hbU : b ≤ U) :
    min (f (childProfile U a)) (f (childProfile U b)) ≤ f (childProfile U j) := by
  apply le_of_tendsto_of_tendsto ((hlim _).min (hlim _)) (hlim _)
  filter_upwards [hsoft] with t ht
  exact child_minimum (F t) U ht.1 ht.2 a j b haj hjb hbU

end ContingencyTables.IntegerWeightedTransport

end OAI
