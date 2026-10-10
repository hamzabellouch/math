import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.BaseSmallLaw
import OAI.Combinatorics.RamseyFive.Marking.ScanRecordPresent
import OAI.Combinatorics.RamseyFive.Entropy.SubsetDeficit

namespace OAI

noncomputable section

namespace SharpRamseyFive.Marking

section
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators
local instance twoScanDecEq (N : ℕ) : DecidableEq (Fin N) := Classical.decEq _
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {N : ℕ}

def swapFlag : FlagPair K V ≃ FlagPair K (Dual K V) :=
  (Equiv.prodComm _ _).trans (Equiv.prodCongr (Equiv.refl _) bidualPoint)

@[simp] lemma swapFlag_apply (f : FlagPair K V) : swapFlag f=(f.2,bidualPoint f.1) := rfl

def reverseTuple (f : Fin N → FlagPair K V) (i : Fin N) := swapFlag (f i.rev)

lemma reverseTuple_consistent {f : Fin N → FlagPair K V} (hf : TupleConsistent f) :
    TupleConsistent (reverseTuple f) := by
  intro i j hij hh
  simp only [reverseTuple,swapFlag_apply,incident_bidual] at hh ⊢
  exact hf j.rev i.rev (by simpa using hij) hh

lemma reverseTuple_incident {f : Fin N → FlagPair K V} (hf : TupleIncident f) :
    TupleIncident (reverseTuple f) := by
  intro i
  simpa only [reverseTuple,swapFlag_apply,incident_bidual] using hf i.rev

variable [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))]

def reverseExpensive (f : Fin N → FlagPair K V) (q : ℝ) : Finset (Fin N) :=
  (expensiveSet (reverseTuple f) q).image Fin.rev

omit [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] [Nonempty (ℙ K V)] in
@[simp] lemma mem_reverseExpensive (f : Fin N → FlagPair K V) (q : ℝ) (i : Fin N) :
    i∈reverseExpensive f q ↔ i.rev∈expensiveSet (reverseTuple f) q := by
  simp only [reverseExpensive,Finset.mem_image]
  constructor
  · rintro ⟨j,hj,rfl⟩
    simpa using hj
  · intro hi
    exact ⟨i.rev,hi,Fin.rev_rev i⟩

omit [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] [Nonempty (ℙ K V)] in
lemma reverseExpensive_card (f : Fin N → FlagPair K V) (q : ℝ) :
    (reverseExpensive f q).card=(expensiveSet (reverseTuple f) q).card := by
  exact Finset.card_image_of_injective _ (fun _ _ h=>by simpa using congrArg Fin.rev h)

theorem unionExpensive_bound (hdim : finrank K V=5) (f : Fin N → FlagPair K V)
    (hf : TupleConsistent f) (q : ℝ) (hq : 0<q) :
    ((expensiveSet f q ∪ reverseExpensive f q).card:ℝ)≤
      800*q*(Real.log (1+Fintype.card (ℙ K (Dual K V)))+
        Real.log (1+Fintype.card (ℙ K V))) := by
  have h₁ := expensiveSet_bound hdim f hf q hq
  have h₂ := expensiveSet_bound (K:=K) (V:=Dual K V) (by simpa using hdim)
    (reverseTuple f) (reverseTuple_consistent hf) q hq
  have hc : Fintype.card (ℙ K (Dual K (Dual K V)))=Fintype.card (ℙ K V) :=
    (Fintype.card_congr bidualPoint).symm
  rw [hc] at h₂
  have hu : ((expensiveSet f q ∪ reverseExpensive f q).card:ℝ)≤
      ((expensiveSet f q).card:ℝ)+((reverseExpensive f q).card:ℝ) := by
    exact_mod_cast Finset.card_union_le _ _
  rw [reverseExpensive_card] at hu
  nlinarith

end

section
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators
local instance typedScanDecEq (N : ℕ) : DecidableEq (Fin N) := Classical.decEq _
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))] {N : ℕ}

def typedDomain (W : ℙ K (Dual K V) → Submodule K (Dual K V))
    (r : Fin 5) (popular : Bool) : Finset (FlagPair K V) :=
  if (levelSet W (chooseLevel W r.val)).Nonempty then
    if popular then popularDomain W r.val (chooseLevel W r.val)
      else poorDomain W r.val (chooseLevel W r.val)
  else ∅

omit [FiniteDimensional K V] [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))] in
lemma typedDomain_subset (W : ℙ K (Dual K V) → Submodule K (Dual K V))
    (r : Fin 5) (popular : Bool) : typedDomain W r popular⊆cheapDomain W r := by
  unfold typedDomain cheapDomain
  split_ifs <;> simp only [Finset.subset_union_left,Finset.subset_union_right,
    Finset.Subset.refl]

def finiteTypedDomain (record : Fin N → Option (FlagPair K V))
    (r : Fin N → Fin 5) (popular : Fin N → Bool) (i : Fin N) :=
  typedDomain (decodeState (finiteDecodeRecord record) i.val) (r i) (popular i)

def finitePopular (f : Fin N → FlagPair K V) (q : ℝ) (i : Fin N) : Bool :=
  let W:=decodeState (finiteDecodeRecord (finiteRecord f q)) i.val
  let r:=finiteRank f q i
  decide (f i∈popularDomain W r.val (chooseLevel W r.val))

variable [Finite K]
omit [Finite K] in
lemma finite_typed_decoding (hdim : finrank K V=5) (f : Fin N → FlagPair K V)
    (hflag : TupleIncident f) (hf : TupleConsistent f) (i : Fin N)
    (hi : i∉expensiveSet f (Nat.card K)) :
    f i∈finiteTypedDomain (finiteRecord f (Nat.card K)) (finiteRank f (Nat.card K))
      (finitePopular f (Nat.card K)) i := by
  have hh := finite_scan_decoding hdim f hflag hf i hi
  unfold finiteDomain cheapDomain at hh
  unfold finiteTypedDomain typedDomain finitePopular
  split_ifs at hh ⊢ with hz hp
  · exact (of_decide_eq_true hp)
  · exact (Finset.mem_union.mp hh).resolve_left (by simpa using hp)
  · exact hh

omit [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))] in
lemma finiteTypedDomain_card (hdim : finrank K V=5)
    (record : Fin N → Option (FlagPair K V)) (r : Fin N → Fin 5)
    (popular : Fin N → Bool) (i : Fin N) :
    ((finiteTypedDomain record r popular i).card:ℝ)≤153*(Nat.card K:ℝ)^4 := by
  have h : ((finiteTypedDomain record r popular i).card:ℝ)≤
      ((finiteDomain record r i).card:ℝ) := by
    exact_mod_cast Finset.card_le_card (typedDomain_subset _ _ _)
  exact h.trans (finiteDomain_card hdim record r i)

end

open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators
local instance concreteMarkingDecEq (N : ℕ) : DecidableEq (Fin N) := Classical.decEq _
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] {N : ℕ}

def twoScanTypes (f : Fin N → FlagPair K V) (i : Fin N) : RankTypes :=
  ((finiteRank f (Nat.card K) i,finiteRank (reverseTuple f) (Nat.card K) i.rev),
    finitePopular f (Nat.card K) i,finitePopular (reverseTuple f) (Nat.card K) i.rev)

def markingMessage (f : Fin N → FlagPair K V) : UnionTranscript (Fin N) (FlagPair K V) :=
  unionMessage twoScanTypes (fun f=>expensiveSet f (Nat.card K))
    (fun f=>reverseExpensive f (Nat.card K)) f

def forwardRecord (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N) :=
  if (m.1 i).2.1 then m.2 i else none

def backwardRecord (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N) :=
  (if (m.1 i.rev).2.2 then m.2 i.rev else none).map swapFlag

lemma forwardRecord_marking (f : Fin N → FlagPair K V) :
    forwardRecord (markingMessage f)=finiteRecord f (Nat.card K) := by
  funext i
  simp only [forwardRecord,markingMessage,unionMessage,unionMask,decide_eq_true_eq]
  rw [unionRecord_decode_left id (fun f=>expensiveSet f (Nat.card K))
    (fun f=>reverseExpensive f (Nat.card K)) f i,finiteRecord_value]
  rfl

lemma backwardRecord_marking (f : Fin N → FlagPair K V) :
    backwardRecord (markingMessage f)=finiteRecord (reverseTuple f) (Nat.card K) := by
  funext i
  simp only [backwardRecord,markingMessage,unionMessage,unionMask,decide_eq_true_eq]
  rw [unionRecord_decode_right id (fun f=>expensiveSet f (Nat.card K))
    (fun f=>reverseExpensive f (Nat.card K)) f i.rev,finiteRecord_value]
  simp only [mem_reverseExpensive,Fin.rev_rev]
  split_ifs <;> rfl

def forwardDomain (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N) :=
  finiteTypedDomain (forwardRecord m) (fun j=>(m.1 j).1.1.1) (fun j=>(m.1 j).1.2.1) i

def backwardDomain (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N) :=
  finiteTypedDomain (backwardRecord m) (fun j=>(m.1 j.rev).1.1.2)
    (fun j=>(m.1 j.rev).1.2.2) i.rev

def markingDomain (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N) :=
  forwardDomain m i ∩ (backwardDomain m i).map swapFlag.symm.toEmbedding

variable [Finite K]
omit [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] in
lemma markingDomain_card (hdim : finrank K V=5)
    (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N) :
    ((markingDomain m i).card:ℝ)≤153*(Nat.card K:ℝ)^4 := by
  have h : ((markingDomain m i).card:ℝ)≤((forwardDomain m i).card:ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_left)
  exact h.trans (finiteTypedDomain_card hdim _ _ _ _)

omit [Finite K] in
theorem marking_decodes (hdim : finrank K V=5) (f : Fin N → FlagPair K V)
    (hflag : TupleIncident f) (hf : TupleConsistent f) (i : Fin N)
    (hi : i∈unspecified (markingMessage f)) : f i∈markingDomain (markingMessage f) i := by
  have hi' : i∉expensiveSet f (Nat.card K) ∪ reverseExpensive f (Nat.card K) := by
    simpa only [markingMessage,unspecified_unionMessage,Finset.mem_compl] using hi
  have h₁ : i∉expensiveSet f (Nat.card K) := fun h=>hi' (Finset.mem_union_left _ h)
  have h₂ : i.rev∉expensiveSet (reverseTuple f) (Nat.card K) :=
    fun h=>hi' (Finset.mem_union_right _ ((mem_reverseExpensive f _ i).mpr h))
  apply Finset.mem_inter.mpr
  constructor
  · unfold forwardDomain
    rw [forwardRecord_marking]
    simpa only [markingMessage,unionMessage,unionMask,twoScanTypes] using
      finite_typed_decoding hdim f hflag hf i h₁
  · apply Finset.mem_map.mpr
    refine ⟨swapFlag (f i),?_,swapFlag.symm_apply_apply _⟩
    unfold backwardDomain
    rw [backwardRecord_marking]
    simpa only [markingMessage,unionMessage,
      unionMask,twoScanTypes,Fin.rev_rev,reverseTuple] using
        finite_typed_decoding (K:=K) (V:=Dual K V) (by simpa using hdim) (reverseTuple f)
          (reverseTuple_incident hflag) (reverseTuple_consistent hf) i.rev h₂

end SharpRamseyFive.Marking

end

end OAI
