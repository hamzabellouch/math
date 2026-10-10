import Mathlib
import OAI.Computability.QuantumFactoring.TransitionEqualization
import OAI.Computability.QuantumFactoring.RetrospectiveCircuit
import OAI.Computability.QuantumFactoring.DivisorData

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open AuxiliaryTree

/-- The closed statistics are evaluated over the supplied exponent record,
not by enumerating residues or invoking a factorization oracle. -/
noncomputable def recordPhi (f : FactorRecord) : ℕ :=
  ∏ p∈f.support, primePowerUnitCount p (f p)

noncomputable def recordFavorable (n : ℕ) (f : FactorRecord) : ℕ :=
  recordPhi f - ∑ t : Fin (n+1), ∏ p∈f.support,
    closedLevelCount (primePowerUnitCount p (f p)) t.val

lemma recordPhi_factorization {m : ℕ} (hm : m≠0) : recordPhi m.factorization=m.totient := by
  rw [Nat.totient_eq_prod_factorization hm]
  apply Finset.prod_congr rfl
  intro p hp
  exact Nat.mul_comm _ _

lemma recordFavorable_factorization {m : ℕ} (hm : m≠0) (n : ℕ) :
    recordFavorable n m.factorization=favorableCount m n := by
  rw [recordFavorable,recordPhi_factorization hm,favorableCount]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  exact (Finset.prod_coe_sort _ _).symm

noncomputable def dataRecord (data : FactorData) (m : ℕ) : FactorRecord :=
  primeRecord (dataDivisorPrimes data m)

lemma dataRecord_correct {M m : ℕ} (hM : 0 < M) (hd : m∣M) :
    dataRecord (trueData M) m = m.factorization := by
  have hh := dataDivisorPrimes_correct hM hd
  rw [dataRecord,primeRecord_eq_factorization _ hh.1,hh.2]

noncomputable def dataPhi (data : FactorData) (m : ℕ) : ℕ := recordPhi (dataRecord data m)
noncomputable def dataFavorable (data : FactorData) (m n : ℕ) : ℕ := recordFavorable n (dataRecord data m)

lemma dataPhi_correct {M m : ℕ} (hM : 0 < M) (hm : 0 < m) (hd : m∣M) :
    dataPhi (trueData M) m=m.totient := by
  rw [dataPhi,dataRecord_correct hM hd,recordPhi_factorization hm.ne']

lemma dataFavorable_correct {M m : ℕ} (hM : 0 < M) (hm : 0 < m) (hd : m∣M) (n : ℕ) :
    dataFavorable (trueData M) m n=favorableCount m n := by
  rw [dataFavorable,dataRecord_correct hM hd,recordFavorable_factorization hm.ne']

/-- Literal prime stripping in natural modular arithmetic. This is exactly the
scan compiled by `stripScan`; its inputs come only from the supplied data. -/
def stripFactorsNat (a m : ℕ) : List ℕ→ℕ→ℕ
  | [], v => v
  | q::qs, v => stripFactorsNat a m qs (stripPrimeNat a m q v)

lemma stripFactorsNat_unit {m a : ℕ} (hm : 2 ≤ m) (u : (ZMod m)ˣ)
    (ha : (a : ZMod m)=(u : ZMod m)) (qs : List ℕ) (v : ℕ) :
    stripFactorsNat a m qs v=stripOrderFactors u qs v := by
  induction qs generalizing v with
  | nil => rfl
  | cons q qs ih => rw [stripFactorsNat,stripPrimeNat_unit hm u ha,ih]; rfl

noncomputable def dataOrder (data : FactorData) (a m : ℕ) : ℕ :=
  stripFactorsNat a m (dataTotientPrimes data m) (dataPhi data m)

/-- The retrospective order used for EVERY actual requested cofactor is the
true order, without calling an order oracle during execution. -/
lemma dataOrder_correct {M m a : ℕ} (hM : 0 < M) (hm : 2 ≤ m) (hd : m∣M)
    (u : (ZMod m)ˣ) (ha : (a : ZMod m)=(u : ZMod m)) :
    dataOrder (trueData M) a m=orderOf u := by
  have hh := dataTotientPrimes_correct hM (by omega : 0 < m) hd
  rw [dataOrder,dataPhi_correct hM (by omega) hd,stripFactorsNat_unit hm u ha]
  exact strip_totient_factors hm u _ hh.1 hh.2

noncomputable def dataListSuccess (data : FactorData) (m n K : ℕ) : ℚ :=
  1-(1-(dataFavorable data m n : ℚ)/(2:ℚ)^(Nat.clog 2 m))^K
noncomputable def dataOrderSuccess (data : FactorData) (a m K : ℕ) : ℚ :=
  Completion.orderSuccess (dataOrder data a m) K

lemma dataListSuccess_correct {M m : ℕ} (hM : 0 < M) (hm : 0 < m) (hd : m∣M) (n K : ℕ) :
    dataListSuccess (trueData M) m n K=Completion.listSuccess m n K := by
  rw [dataListSuccess,dataFavorable_correct hM hm hd]
  rfl

lemma dataOrderSuccess_correct {M m a : ℕ} (hM : 0 < M) (hm : 2 ≤ m) (hd : m∣M)
    (u : (ZMod m)ˣ) (ha : (a : ZMod m)=(u : ZMod m)) (K : ℕ) :
    dataOrderSuccess (trueData M) a m K=Completion.orderSuccess (orderOf u) K := by
  rw [dataOrderSuccess,dataOrder_correct hM hm hd u ha]

end ExactQuantumFactoring


end

end OAI
