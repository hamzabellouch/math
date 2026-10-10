import Mathlib
import OAI.Combinatorics.RamseyFive.Marking.ScanRecord
import OAI.Combinatorics.RamseyFive.Entropy.EntropyCrossEntropy

namespace OAI

namespace SharpRamseyFive.Marking

section
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V α κ : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype α] [Fintype κ]

noncomputable local instance (N : ℕ) : DecidableEq (Fin N) := Classical.decEq _

omit [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype α] [Fintype κ] in
lemma scanRecord_present (a : ℕ → ℙ K V) (b : ℕ → ℙ K (Dual K V)) (q : ℝ) (N : ℕ) :
    (∑ i : Fin N,present (scanRecord a b q i.val))=(scanSet a b q N).card := by
  rw [Fin.sum_univ_eq_sum_range (fun i => present (scanRecord a b q i)) N,scan_count]
  simp only [Finset.card_filter,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases he : Expensive (scanState a b q i) (a i) (b i) q
  · rw [scanRecord,ite_eq_left he]
    change Expensive (state a b (scanSet a b q i)) (a i) (b i) q at he
    rw [ite_eq_left he]
    norm_num [present]
  · rw [scanRecord,ite_eq_right he]
    change ¬Expensive (state a b (scanSet a b q i)) (a i) (b i) q at he
    rw [ite_eq_right he]
    norm_num [present]

omit [FiniteDimensional K V] in

theorem one_scan_entropy (p : Law (κ × α))
    (a : α → ℕ → ℙ K V) (b : α → ℕ → ℙ K (Dual K V)) (q : ℝ) (N : ℕ)
    (S : κ → Fin N → Finset (ℙ K V × ℙ K (Dual K V))) (cap : ℝ)
    (hcap : 1≤cap) (hS : ∀ c i,((S c i).card:ℝ)≤cap)
    (hsupp : ∀ c z,0<p (c,z) → ∀ i : Fin N,(a z i.val,b z i.val)∈S c i) :
    (∑ c,first p c*entropy (pair (fiber p c)
      (fun z => fun i : Fin N => rankMask (a z) (b z) q i.val)
      (fun z => fun i : Fin N => scanRecord (a z) (b z) q i.val)))≤
        (N:ℝ)*(Real.log 5+Real.log 2)+
          (∑ z,second p z*(scanSet (a z) (b z) q N).card)*Real.log cap := by
  have hh:=conditional_marked_entropy (β := ℙ K V × ℙ K (Dual K V))
    (ι := Fin N) (μ := Fin N → Fin 5) p
    (fun z => fun i : Fin N => rankMask (a z) (b z) q i.val)
    (fun z => fun i : Fin N => scanRecord (a z) (b z) q i.val) S cap hcap hS (by
      intro c z hz i ab he
      unfold scanRecord at he
      split_ifs at he with he'
      · have hval : (a z i.val,b z i.val)=ab := Option.some.inj he
        rw [←hval]
        exact hsupp c z hz i
)
  apply hh.trans_eq
  simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat,
    Real.log_pow,scanRecord_present]
  ring

end

open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
local instance finiteMarkingDecEq (N : ℕ) : DecidableEq (Fin N) := Classical.decEq _

variable {β : Type*} [Nonempty β] {N : ℕ}
def extendTuple (f : Fin N → β) (n : ℕ) : β :=
  if h:n<N then f ⟨n,h⟩ else Classical.choice ‹Nonempty β›
lemma extendTuple_at (f : Fin N → β) (i : Fin N) : extendTuple f i.val=f i := by
  simp only [extendTuple,dite_eq_left i.isLt]

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]

abbrev FlagPair (K V : Type*) [Field K] [AddCommGroup V] [Module K V] :=
  ℙ K V × ℙ K (Dual K V)

def tupleFirst (f : Fin N → FlagPair K V) (n : ℕ) := (extendTuple f n).1
def tupleSecond (f : Fin N → FlagPair K V) (n : ℕ) := (extendTuple f n).2

def TupleConsistent (f : Fin N → FlagPair K V) : Prop :=
  ∀ i j,i<j → Incident (f i).1 (f j).2 → Incident (f j).1 (f i).2

def TupleIncident (f : Fin N → FlagPair K V) : Prop := ∀ i,Incident (f i).1 (f i).2

omit [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma tupleConsistent_extend {f : Fin N → FlagPair K V} (h : TupleConsistent f) :
    ∀ i j,i<j → j<N → Incident (tupleFirst f i) (tupleSecond f j) →
      Incident (tupleFirst f j) (tupleSecond f i) := by
  intro i j hij hj
  have hi : i<N := hij.trans hj
  simpa only [tupleFirst,tupleSecond,extendTuple,dite_eq_left hi,dite_eq_left hj] using
    (h ⟨i,hi⟩ ⟨j,hj⟩ hij)

omit [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma tupleIncident_extend {f : Fin N → FlagPair K V} (h : TupleIncident f) :
    ∀ i,i<N → Incident (tupleFirst f i) (tupleSecond f i) := by
  intro i hi
  simpa only [tupleFirst,tupleSecond,extendTuple,dite_eq_left hi] using h ⟨i,hi⟩

def finiteRecord (f : Fin N → FlagPair K V) (q : ℝ) (i : Fin N) :=
  scanRecord (tupleFirst f) (tupleSecond f) q i.val

def finiteRank (f : Fin N → FlagPair K V) (q : ℝ) (i : Fin N) :=
  rankMask (tupleFirst f) (tupleSecond f) q i.val

def expensiveSet (f : Fin N → FlagPair K V) (q : ℝ) : Finset (Fin N) :=
  Finset.univ.filter fun i => (finiteRecord f q i).isSome

omit [FiniteDimensional K V] [Fintype (ℙ K V)] in
lemma finiteRecord_value (f : Fin N → FlagPair K V) (q : ℝ) (i : Fin N) :
    finiteRecord f q i = if i∈expensiveSet f q then some (f i) else none := by
  simp only [expensiveSet,finiteRecord,scanRecord]
  split_ifs with h <;> simp_all [tupleFirst,tupleSecond,extendTuple_at]

omit [FiniteDimensional K V] [Fintype (ℙ K V)] in
lemma expensiveSet_card (f : Fin N → FlagPair K V) (q : ℝ) :
    ((expensiveSet f q).card:ℝ) =
      (scanSet (tupleFirst f) (tupleSecond f) q N).card := by
  rw [←scanRecord_present]
  change _ = ∑ i : Fin N,present (finiteRecord f q i)
  simp_rw [finiteRecord_value]
  have he (i : Fin N) : present (if i∈expensiveSet f q then some (f i) else none) =
      if i∈expensiveSet f q then (1:ℝ) else 0 := by split_ifs <;> rfl
  simp_rw [he]
  rw [Finset.sum_ite_mem,Finset.univ_inter]
  simp

omit [Fintype (ℙ K V)] in
theorem expensiveSet_bound (hdim : finrank K V=5) (f : Fin N → FlagPair K V)
    (hf : TupleConsistent f) (q : ℝ) (hq : 0<q) :
    ((expensiveSet f q).card:ℝ)≤800*q*Real.log (1+Fintype.card (ℙ K (Dual K V))) := by
  rw [expensiveSet_card]
  exact scanSet_card_bound hdim _ _ q hq N (tupleConsistent_extend hf)

def finiteDecodeRecord (record : Fin N → Option (FlagPair K V)) (n : ℕ) :=
  if h:n<N then record ⟨n,h⟩ else none

def finiteDomain (record : Fin N → Option (FlagPair K V)) (r : Fin N → Fin 5)
    (i : Fin N) : Finset (FlagPair K V) :=
  cheapDomain (decodeState (finiteDecodeRecord record) i.val) (r i)

omit [FiniteDimensional K V] [Fintype (ℙ K V)] in
lemma finite_decode (f : Fin N → FlagPair K V) (q : ℝ) (i : Fin N) :
    decodeState (finiteDecodeRecord (finiteRecord f q)) i.val =
      decodeState (scanRecord (tupleFirst f) (tupleSecond f) q) i.val := by
  apply decodeState_congr_prefix
  intro j hj
  simp only [finiteDecodeRecord,dite_eq_left (hj.trans i.isLt),finiteRecord]

variable [Finite K]
omit [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))] in
theorem finiteDomain_card (hdim : finrank K V=5)
    (record : Fin N → Option (FlagPair K V)) (r : Fin N → Fin 5) (i : Fin N) :
    ((finiteDomain record r i).card:ℝ)≤153*(Nat.card K:ℝ)^4 :=
  cheapDomain_card hdim _ _

omit [Finite K] in
theorem finite_scan_decoding (hdim : finrank K V=5) (f : Fin N → FlagPair K V)
    (hflag : TupleIncident f) (hf : TupleConsistent f) (i : Fin N)
    (hi : i∉expensiveSet f (Nat.card K)) :
    f i∈finiteDomain (finiteRecord f (Nat.card K)) (finiteRank f (Nat.card K)) i := by
  have hr : finiteRecord f (Nat.card K) i=none := by rw [finiteRecord_value,ite_eq_right hi]
  have hh := scan_decoding hdim (tupleFirst f) (tupleSecond f) N
    (tupleIncident_extend hflag) (tupleConsistent_extend hf) i.isLt hr
  simpa only [finiteDomain,finite_decode,finiteRank,tupleFirst,tupleSecond,extendTuple_at] using hh
end
end SharpRamseyFive.Marking

end OAI
