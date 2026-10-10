import Mathlib
import OAI.Combinatorics.RamseyFive.Marking.ReciprocalBands
import OAI.Combinatorics.RamseyFive.Marking.Collisions

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open SharpRamseyFive.CoreGeometry SharpRamseyFive.LowConflict
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  {n : ℕ}

def reciprocalGood (p : Law (Fin n→FlagPair K V)) (u : Fin n→ℝ) (s : ℝ)
    (i j : Fin n) (a : ℙ K V) (b : ℙ K (Dual K V)) : Prop :=
  a∈goodFirstEndpoints (tupleMarginal p i) (32*Real.exp (5*Real.log (Nat.card K)-u i))
    ((Nat.card K:ℝ)^4) s ∧
  b∈goodFirstEndpoints (swap (tupleMarginal p j)) (32*Real.exp (u j))
    ((Nat.card K:ℝ)^4) s ∧ Incident a b

omit [Finite K] [FiniteDimensional K V] in
lemma reciprocalGood_positive (p : Law (Fin n→FlagPair K V)) (u : Fin n→ℝ) (s : ℝ)
    (i j : Fin n) (a : ℙ K V) (b : ℙ K (Dual K V)) (hg : reciprocalGood p u s i j a b) :
    0<first (tupleMarginal p i) a ∧ 0<second (tupleMarginal p j) b := by
  constructor
  · exact goodFirst_positive _ _ _ _ (by positivity) a hg.1
  · have h:=goodFirst_positive _ _ _ _ (by positivity : 0<32*Real.exp (u j)) b hg.2.1
    simpa only [first_swap] using h

omit [Finite K] in
lemma reciprocal_low_conflict (hdim : finrank K V=5)
    (p : Law (Fin n→FlagPair K V)) (u : Fin n→ℝ) (s : ℝ)
    (hcons : ∀ x,0<p x→TupleConsistent x) (i j : Fin n) (hij : i<j) :
    relationMass (reciprocalGood p u s i j) (first (tupleMarginal p i)) (second (tupleMarginal p j))≤
      80004*(entropy (tupleMarginal p i)+entropy (tupleMarginal p j)-
        entropy (pair p (fun x=>x i) (fun x=>x j))+
        tupleCollision p Projectivization.rep Projectivization.rep (reciprocalGood p u s) i j) := by
  apply tuple_low_conflict hdim p Projectivization.rep Projectivization.rep (reciprocalGood p u s) ?_ i j hij
  intro x hx i j hij hg
  exact (incident_iff _ _).mp (hcons x hx i j hij hg.2.2)

theorem reciprocal_closed_collisions (hdim : finrank K V=5)
    (p : Law (Fin n→FlagPair K V)) (u : Fin n→ℝ) (s width M : ℝ) (b : Fin 7)
    (hs : 2 ≤ s) (hband : ∀ i,BandCondition (Real.log (Nat.card K)) width (u i) b)
    (heven : b.val%2=0) (hsmall : Real.log 32+width+3*s<Real.log (Nat.card K))
    (hinc : ∀ x,0<p x→TupleIncident x)
    (hocc : ∀ x,0<p x→∀ S : Submodule K (Dual K V),
      (∑ i,if InRectangle S (x i).1.rep (x i).2.rep then (1:ℝ) else 0)≤M) :
    (∑ i,∑ j,tupleCollision p Projectivization.rep Projectivization.rep (reciprocalGood p u s) i j)≤2*n*M := by
  apply closed_tuple_collision_bound hdim (b.val/2+1) (by have := b.isLt;omega)
    p Projectivization.rep Projectivization.rep (reciprocalGood p u s) M
  · intro x hx i
    exact (incident_iff _ _).mp (hinc x hx i)
  · exact reciprocalGood_positive p u s
  · intro i j a y hg
    exact (closed_reciprocal_ranks hdim (tupleMarginal p i) (u i) s width b hs (hband i) heven hsmall).1 a hg.1
  · intro i j a y hg
    exact (closed_reciprocal_ranks hdim (tupleMarginal p j) (u j) s width b hs (hband j) heven hsmall).2 y hg.2.1
  · exact hocc

theorem reciprocal_open_collisions (hdim : finrank K V=5)
    (p : Law (Fin n→FlagPair K V)) (u : Fin n→ℝ) (s width : ℝ) (b : Fin 7)
    (hs : 2 ≤ s) (hband : ∀ i,BandCondition (Real.log (Nat.card K)) width (u i) b)
    (hodd : b.val%2≠0) (hwide : Real.log 32+3*s<width) (i j : Fin n) :
    tupleCollision p Projectivization.rep Projectivization.rep (reciprocalGood p u s) i j=0 := by
  apply open_tuple_collision_zero hdim (b.val/2+2) (by have := b.isLt;omega)
    p Projectivization.rep Projectivization.rep (reciprocalGood p u s)
  · intro i j a y hg
    exact (open_reciprocal_ranks hdim (tupleMarginal p i) (u i) s width b hs (hband i) hodd hwide).1 a hg.1
  · intro i j a y hg
    exact (open_reciprocal_ranks hdim (tupleMarginal p j) (u j) s width b hs (hband j) hodd hwide).2 y hg.2.1
end
end SharpRamseyFive.Marking

end OAI
