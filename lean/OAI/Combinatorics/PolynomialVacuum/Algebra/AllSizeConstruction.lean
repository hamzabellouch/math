import OAI.Combinatorics.PolynomialVacuum.Algebra.HomogeneityStep
import OAI.Combinatorics.PolynomialVacuum.Algebra.ChargeStep
import OAI.Combinatorics.PolynomialVacuum.Algebra.BaseGrading
import OAI.Combinatorics.PolynomialVacuum.Algebra.BaseBounds
import OAI.Combinatorics.PolynomialVacuum.Algebra.BaseEndpoints

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

 

noncomputable def polynomialVacuum : Family
  | 0 => vacuumZero
  | 1 => vacuumOne
  | 2 => vacuumTwo
  | 3 => vacuumThree
  | n+4 => interpolateState (polynomialVacuum (n+2)) (polynomialVacuum (n+3))

structure VacuumRegular {N : ℕ} (ψ : State N) : Prop where
  charge : ChargeZero ψ
  homogeneous : ∀ s, (ψ s).IsHomogeneous (N.choose 2)
  degree : ∀ s i, (ψ s).degreeOf i≤N-1
  plus : ∀ s i, s i=Spin.plus → (ψ s).degreeOf i≤N-2
  minus : MinusZero ψ
  exchange : LowerExchange (liftState ψ) N

structure VacuumAt (f : Family) (N : ℕ) : Prop where
  regular : VacuumRegular (f N)
  cyclic : ∀ n, N=n+1 → NaturalCyclic n (liftState (f (n+1)))
  nodes : ∀ n, N=n+2 → NaturalCupNodes (liftState (f (n+2))) (liftState (f n)) n
  firstCup : ∀ n, N=n+2 → FirstCupReduction (liftState (f (n+2))) (liftState (f n)) n
  cups : ∀ n, N=n+2 → ∀ i≤n, CupAt (liftState (f (n+2))) (liftState (f n)) n i
  lastZero : ∀ n, N=n+1 → LastZeroReduction (liftState (f (n+1))) (liftState (f n)) n

theorem vacuumZero_regular : VacuumRegular vacuumZero := by
  constructor
  · intro s hs; exact (hs (by simp)).elim
  · intro s; simpa [vacuumZero] using (isHomogeneous_one _ _)
  · intro s i; exact Fin.elim0 i
  · intro s i; exact Fin.elim0 i
  · intro s i; exact Fin.elim0 i
  · intro j hj; omega

theorem vacuumOne_regular : VacuumRegular vacuumOne := by
  constructor
  · intro s hs
    cases h : s 0 <;> simp_all [vacuumOne,charge]
  · intro s
    unfold vacuumOne
    split_ifs
    · simpa [vacuumZero] using (isHomogeneous_one _ _)
    · exact isHomogeneous_zero _ _ _
  · intro s i; unfold vacuumOne; split_ifs <;> simp
  · intro s i hi; unfold vacuumOne; split_ifs <;> simp
  · intro s i hi
    have he : i=0 := Subsingleton.elim _ _
    subst i
    simp [vacuumOne,hi]
  · intro j hj; omega

theorem vacuumTwo_regular : VacuumRegular vacuumTwo := by
  exact ⟨vacuumTwo_charge,vacuumTwo_homogeneous,(fun s j => (vacuumTwo_degrees s j).1),
    (fun s j => (vacuumTwo_degrees s j).2),vacuumTwo_minusZero,vacuumTwo_exchange⟩

theorem vacuumThree_regular : VacuumRegular vacuumThree := by
  exact ⟨vacuumThree_charge,vacuumThree_homogeneous,(fun s j => (vacuumThree_degrees s j).1),
    (fun s j => (vacuumThree_degrees s j).2),vacuumThree_minusZero,vacuumThree_exchange⟩

theorem vacuumOne_cyclic : NaturalCyclic 0 (liftState vacuumOne) := by
  intro X; funext s
  simp only [cyclicTransform,rotateTensor,lift_vacuumOne,natRotate_zero]
  cases h : s 0 <;> simp [charge]

theorem polynomialVacuum_at_zero : VacuumAt polynomialVacuum 0 := by
  constructor
  · exact vacuumZero_regular
  all_goals intro n hn; omega

theorem polynomialVacuum_at_one : VacuumAt polynomialVacuum 1 := by
  constructor
  · exact vacuumOne_regular
  · intro n hn; have : n=0 := by omega
    subst n; exact vacuumOne_cyclic
  · intro n hn; omega
  · intro n hn; omega
  · intro n hn; omega
  · intro n hn; have : n=0 := by omega
    subst n; exact vacuumOne_lastZero

theorem polynomialVacuum_at_two : VacuumAt polynomialVacuum 2 := by
  constructor
  · exact vacuumTwo_regular
  · intro n hn; have : n=1 := by omega
    subst n; exact vacuumTwo_cyclic
  · intro n hn; have : n=0 := by omega
    subst n; exact vacuumTwo_nodes
  · intro n hn; have : n=0 := by omega
    subst n; exact vacuumTwo_firstCup
  · intro n hn i hi; have : n=0 := by omega
    subst n
    have : i=0 := by omega
    subst i
    exact vacuumTwo_firstCup
  · intro n hn; have : n=1 := by omega
    subst n; exact vacuumTwo_lastZero

theorem polynomialVacuum_at_three : VacuumAt polynomialVacuum 3 := by
  constructor
  · exact vacuumThree_regular
  · intro n hn; have : n=2 := by omega
    subst n; exact vacuumThree_cyclic
  · intro n hn; have : n=1 := by omega
    subst n; exact vacuumThree_nodes
  · intro n hn; have : n=1 := by omega
    subst n; exact vacuumThree_firstCup
  · intro n hn i hi; have : n=1 := by omega
    subst n
    interval_cases i
    · exact vacuumThree_firstCup
    · exact vacuumThree_lastCup
  · intro n hn; have : n=2 := by omega
    subst n; exact vacuumThree_lastZero

end PolynomialVacuumAlgebra

end OAI
