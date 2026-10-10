import OAI.Combinatorics.ContingencyTables.Dense.DenseDrawTabulation
import OAI.Combinatorics.ContingencyTables.Machines.EnumerationPointBounds
import OAI.Combinatorics.ContingencyTables.Sampling.PaddedEnumerationBounds

namespace OAI

/-! # Numeric dense-tabulation schedules versus binary margin size -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary Polynomial

lemma clog_succ_le_weight (n : ℕ) : Nat.clog 2 (n+1) ≤ weight n := by
  exact (Nat.clog_le_of_le_pow (Nat.succ_le_iff.mpr (Nat.lt_size_self n))).trans
    (size_le_weight n)

def offsetNumericMeasure (z : OffsetWidthData) : ℕ := z.1.2+z.2+weight z

theorem offsetLengths_sum_polynomial : ∃ p : Polynomial ℕ,∀ z,
    (offsetLengths z).sum ≤ p.eval (offsetNumericMeasure z) := by
  obtain ⟨p,hp⟩ := polynomial_freeCells
  obtain ⟨q,hq⟩ := polynomial_gridCellWidth
  let input : Polynomial ℕ := 1+X+p
  let entry : Polynomial ℕ := q.comp input+4*X
  refine ⟨p*entry,?_⟩
  intro z
  let M := offsetNumericMeasure z
  have hz : weight z ≤ M := by unfold M offsetNumericMeasure; omega
  have hfree := (hp z).trans (polynomial_eval_monotone p hz)
  have hlen : (freeCells z).length ≤ p.eval M :=
    (list_length_le_weight _).trans ((Nat.le_add_left _ _).trans hfree)
  have he (ij : ℕ×ℕ) (hij : ij∈freeCells z) : offsetLength (z,ij) ≤ entry.eval M := by
    have hw : weight ij ≤ p.eval M := (weight_mem hij).trans ((Nat.le_add_left _ _).trans hfree)
    have hi : weight (z.1,ij) ≤ input.eval M := by
      have hfirst : weight z.1 ≤ M := (weight_fst z).trans hz
      simp only [weight_prod,input,eval_add,eval_one,eval_X]
      omega
    have hg : weight (gridCellWidth (z.1,ij)) ≤ q.eval (input.eval M) :=
      (Nat.le_add_left _ _).trans ((hq _).trans (polynomial_eval_monotone q hi))
    have hn : z.2+z.1.2 ≤ M := by unfold M offsetNumericMeasure; omega
    have hc := (clog_succ_le_weight (gridCellWidth (z.1,ij))).trans hg
    change Nat.clog 2 (gridCellWidth (z.1,ij)+1)+4*(z.2+z.1.2) ≤ _
    simp only [entry,eval_add,eval_comp,eval_mul,eval_ofNat,eval_X]
    omega
  have hs := list_sum_le_length_mul (offsetLengths z) (entry.eval M) (by
    intro a ha
    rw [offsetLengths] at ha
    obtain ⟨ij,hij,rfl⟩ := List.mem_map.mp ha
    exact he ij hij)
  simp only [offsetLengths,List.length_map] at hs
  exact hs.trans (by rw [eval_mul]; exact Nat.mul_le_mul_right _ hlen)

def trialNumericMeasure (z : DenseDrawParameters) : ℕ := z.1.2+z.2+weight z

theorem trialWidth_polynomial : ∃ p : Polynomial ℕ,∀ z,
    trialWidth z ≤ p.eval (trialNumericMeasure z) := by
  have ht : PolynomialTime
      (pair (composition (first (B := ℕ)) flatToGridDataRealizer) second) :=
    polynomial_pair (polynomial_composition polynomial_first polynomial_flatToGridData) polynomial_second
  obtain ⟨p,hp⟩ := ht
  obtain ⟨q,hq⟩ := offsetLengths_sum_polynomial
  let walk : Polynomial ℕ := X^50*(X+1)^2*(16*X^5)
  refine ⟨walk+q.comp (X+p),?_⟩
  intro z
  let M := trialNumericMeasure z
  have hz : weight z ≤ M := by unfold M trialNumericMeasure; omega
  have hd : z.1.2 ≤ M := by unfold M trialNumericMeasure; omega
  have hh : z.2 ≤ M := by unfold M trialNumericMeasure; omega
  have hp' := (hp z).trans (polynomial_eval_monotone p hz)
  have hw : weight (flatToGridData z.1,z.2) ≤ p.eval M := (Nat.le_add_left _ _).trans hp'
  have hm : offsetNumericMeasure (flatToGridData z.1,z.2) ≤ (X+p).eval M := by
    change z.1.2+z.2+weight (flatToGridData z.1,z.2) ≤ _
    simp only [eval_add,eval_X]
    unfold M trialNumericMeasure at *
    omega
  have ho := (hq (flatToGridData z.1,z.2)).trans (polynomial_eval_monotone q hm)
  have hb := denseStepBits_upper z.1.2
  have hwalk : trialWalkBits (z,[]) ≤ walk.eval M := by
    simp only [trialWalkBits,walk,eval_mul,eval_pow,eval_add,eval_X,eval_one,eval_ofNat]
    exact Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.pow_le_pow_left hd _) (Nat.pow_le_pow_left (by omega) _))
      (hb.trans (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hd _)))
  simpa only [trialWidth,eval_add,eval_comp] using Nat.add_le_add hwalk ho

def canonicalNumericMeasure (z : CanonicalParameters) : ℕ := z.2.1+z.2.2+weight z

theorem rawTrialBits_polynomial : ∃ p : Polynomial ℕ,∀ z,
    rawTrialBits z ≤ p.eval (canonicalNumericMeasure z) := by
  obtain ⟨p,hp⟩ := polynomial_rawDrawParameters
  obtain ⟨q,hq⟩ := trialWidth_polynomial
  refine ⟨q.comp (X+p),?_⟩
  intro z
  have hz : weight z ≤ canonicalNumericMeasure z := by unfold canonicalNumericMeasure; omega
  have hw : weight (rawDrawParameters z) ≤ p.eval (canonicalNumericMeasure z) :=
    (Nat.le_add_left _ _).trans ((hp z).trans (polynomial_eval_monotone p hz))
  have hm : trialNumericMeasure (rawDrawParameters z) ≤ (X+p).eval (canonicalNumericMeasure z) := by
    change z.2.1+z.2.2+weight (rawDrawParameters z) ≤ _
    simp only [eval_add,eval_X]
    unfold canonicalNumericMeasure at hw ⊢
    omega
  simpa only [rawTrialBits,eval_comp] using
    (hq (rawDrawParameters z)).trans (polynomial_eval_monotone q hm)

/-- Only the two finite boxes contribute an exponential factor; the
numeric walk, rejection and reserved-word schedules are polynomial. -/
def rawBoxMeasure (z : CanonicalParameters) : ℕ :=
  (4*z.2.1^8)^tabulationDimension z+
    gridStateCount (completionEnumerationData z.1)+canonicalNumericMeasure z

theorem rawTabulationMeasure_polynomial : ∃ p : Polynomial ℕ,∀ z,
    rawTabulationMeasure z ≤ p.eval (rawBoxMeasure z) := by
  obtain ⟨p,hp⟩ := rawTrialBits_polynomial
  refine ⟨4*X+24*X^5+X^50*(X+1)^2+p+X^4*(X+1),?_⟩
  intro z
  let M := rawBoxMeasure z
  have hd : z.2.1 ≤ M := by unfold M rawBoxMeasure canonicalNumericMeasure; omega
  have hh : z.2.2 ≤ M := by unfold M rawBoxMeasure canonicalNumericMeasure; omega
  have hw : weight z ≤ M := by unfold M rawBoxMeasure canonicalNumericMeasure; omega
  have hg : (4*z.2.1^8)^tabulationDimension z ≤ M := by unfold M rawBoxMeasure; omega
  have hc : gridStateCount (completionEnumerationData z.1) ≤ M := by unfold M rawBoxMeasure; omega
  have ha : 8*z.2.1^5 ≤ 8*M^5 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hd _)
  have hb : denseStepBits z.2.1 ≤ 16*M^5 :=
    (denseStepBits_upper _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hd _))
  have hs : z.2.1^50*(z.2.2+1)^2 ≤ M^50*(M+1)^2 :=
    Nat.mul_le_mul (Nat.pow_le_pow_left hd _) (Nat.pow_le_pow_left (by omega) _)
  have hr : z.2.1^4*(z.2.2+1) ≤ M^4*(M+1) :=
    Nat.mul_le_mul (Nat.pow_le_pow_left hd _) (by omega)
  have ht : rawTrialBits z ≤ p.eval M :=
    (hp z).trans (polynomial_eval_monotone p (by unfold M rawBoxMeasure; omega))
  change (4*z.2.1^8)^tabulationDimension z+8*z.2.1^5+denseStepBits z.2.1+
    z.2.1^50*(z.2.2+1)^2+weight z+gridStateCount (completionEnumerationData z.1)+
    rawTrialBits z+z.2.1^4*(z.2.2+1) ≤ _
  change _ ≤ (4*X+24*X^5+X^50*(X+1)^2+p+X^4*(X+1)).eval M
  simp only [eval_add,eval_mul,eval_ofNat,eval_X,eval_pow,eval_one]
  omega

end ContingencyTables.DensePrograms

end OAI
