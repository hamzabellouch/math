import OAI.Combinatorics.ContingencyTables.Transport.IntegerLaw
import OAI.Combinatorics.ContingencyTables.Transport.RationalReindex

namespace OAI

/-! # Integer laws under bijective coordinate changes -/

namespace ContingencyTables.IntegerLaw
open scoped BigOperators
variable {A B : Type*} [Fintype A] [Fintype B] {Q : ℕ}

/-- A coordinate permutation leaves the common denominator unchanged. -/
def equiv (p : IntegerLaw A Q) (e : A ≃ B) : IntegerLaw B Q where
  count b := p.count (e.symm b)
  total := (e.symm.sum_comp p.count).trans p.total

@[simp] lemma equiv_count (p : IntegerLaw A Q) (e : A ≃ B) (b : B) :
    (p.equiv e).count b=p.count (e.symm b) := rfl

lemma toRational_equiv (p : IntegerLaw A Q) (e : A ≃ B) (hQ : 0<Q) :
    (p.equiv e).toRational hQ=FirstSuccess.equivLaw e (p.toRational hQ) := by
  apply ResidualMixture.RationalLaw.ext
  rfl

/-- The integer propagation table also defines a normalized finite law. -/
def walk [DecidableEq A] (K : A → IntegerLaw A Q) (x : A) (n : ℕ) :
    IntegerLaw A (Q^n) where
  count := IntegerPropagation.numerators (fun x y => (K x).count y) x n
  total := IntegerPropagation.numerators_total _ Q (fun x => (K x).total) x n

lemma toRational_walk [DecidableEq A] (K : A → IntegerLaw A Q) (hQ : 0<Q)
    (x : A) (n : ℕ) :
    (walk K x n).toRational (pow_pos hQ n)=
      FirstSuccess.walkLaw (fun x => (K x).toRational hQ) x n := by
  apply ResidualMixture.RationalLaw.ext
  funext y
  have hK : IntegerPropagation.kernel (fun x y => (K x).count y) Q hQ
      (fun x => (K x).total)=(fun x => (K x).toRational hQ) := by
    funext a
    apply ResidualMixture.RationalLaw.ext
    rfl
  have he := IntegerPropagation.numerators_walkLaw (fun x y => (K x).count y)
    Q hQ (fun x => (K x).total) x n y
  rw [hK] at he
  simpa only [toRational,walk,Nat.cast_pow] using
    he

end ContingencyTables.IntegerLaw

end OAI
