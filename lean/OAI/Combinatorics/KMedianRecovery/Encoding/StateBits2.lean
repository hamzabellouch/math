import Mathlib
import OAI.Combinatorics.KMedianRecovery.Machines.SensitiveMachine

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLabel
open RationalLeaves RationalHeight
lemma heightBound_height {m h : ℕ} {x : Label (Fin m)} (hx : HeightBound h x) :
    Height (rationalHeight x) h := by
  cases x with
  | inl i=>exact zero h
  | inr c=>exact hx
lemma encode_length_bound {m key h : ℕ} (x : Label (Fin m))
    (hk : level x≤key) (hh : HeightBound h x) : (encode x).length≤2*key+2*m+3*h+8 := by
  have hp : (parent x).val≤ m := (parent x).isLt.le
  have hl : (level x).size≤key := (Nat.size_le.mpr Nat.lt_two_pow_self).trans hk
  have hi : (parent x).val.size≤ m := (Nat.size_le.mpr Nat.lt_two_pow_self).trans hp
  have hr := BinaryRational.encode_height (heightBound_height hh)
  simp only [encode,pairBits_length,Nat.size_eq_bits_len]
  omega
end MetricKMedianRecovery.BitMachine.BinaryLabel

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteContext
open WordList RationalLeaves
lemma labels_length {m r B : ℕ} (xs : List (Label (Fin m))) (hn : xs.length≤r)
    (hB : ∀ x∈xs,(BinaryLabel.encode x).length≤B) :
    (labels xs).length≤r*(2*B+2) := by
  have h:=encode_le_bound (xs.map BinaryLabel.encode) B (by
    intro w hw
    obtain ⟨x,hx,rfl⟩:=List.mem_map.mp hw
    exact hB x hx)
  simp only [List.length_map] at h
  exact h.trans (Nat.mul_le_mul_right _ hn)
lemma setBits_length {m r B : ℕ} (S : Finset (Label (Fin m))) (hn : S.card≤r)
    (hB : ∀ x∈S,(BinaryLabel.encode x).length≤B) :
    (setBits S).length≤r*(2*B+2) := by
  apply labels_length _ (by simpa only [BinaryLabel.orderedSort,Finset.length_sort] using hn)
  intro x hx
  exact hB x (Finset.mem_sort _ |>.mp hx)
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

namespace MetricKMedianRecovery.BitMachine.BinaryCoupledState
open WordOperations WordList RationalLeaves RationalHeight CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)

def encode {m : ℕ} (s : State (Fin m)) : List Bool := WordList.encode
  [setBits s.B,setBits s.mapFree,historyBits s.P,historyBits s.mapPrefix,
    BinaryRational.encode s.lam,BinaryRational.encode s.lam',historyBits s.T,historyBits s.U]

def labelBound (m t h : ℕ) : ℕ := 6*t+2*m+3*h+8
def bankBound (m t : ℕ) : ℕ := t*(2*m+1)
def historyBound (m t h : ℕ) : ℕ := t*(2*(m+bankBound m t)*(2*labelBound m t h+2)+2)
def bound (m t h p : ℕ) : ℕ :=
  4*bankBound m t*(2*labelBound m t h+2)+8*historyBound m t h+12*p+40

lemma bank_labels {m q h p t : ℕ} {F : Finset (Fin m)} {s : State (Fin m)}
    (hs : s.Resources F q h p) (hq : q≤t) :
    ∀ x∈F.image original∪s.B,(BinaryLabel.encode x).length≤labelBound m t h := by
  intro x hx
  suffices hh : (BinaryLabel.encode x).length≤2*(3*t)+2*m+3*h+8 by
    exact hh.trans (by simp only [labelBound]; omega)
  apply BinaryLabel.encode_length_bound x
  · rcases Finset.mem_union.mp hx with hx|hx
    · obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hx
      exact Nat.zero_le _
    · exact (hs.bank.before.level x hx).trans (Nat.mul_le_mul_left _ hq)
  · rcases Finset.mem_union.mp hx with hx|hx
    · obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hx
      trivial
    · exact hs.bank.height x hx
lemma mapped_labels {m q h p t : ℕ} {F : Finset (Fin m)} {s : State (Fin m)}
    (hs : s.Resources F q h p) (hq : q≤t) :
    ∀ x∈F.image original∪s.mapFree,(BinaryLabel.encode x).length≤labelBound m t h := by
  intro x hx
  suffices hh : (BinaryLabel.encode x).length≤2*(3*t)+2*m+3*h+8 by
    exact hh.trans (by simp only [labelBound]; omega)
  apply BinaryLabel.encode_length_bound x
  · rcases Finset.mem_union.mp hx with hx|hx
    · obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hx
      exact Nat.zero_le _
    · exact (hs.map_bound.before.level x hx).trans (Nat.mul_le_mul_left _ hq)
  · rcases Finset.mem_union.mp hx with hx|hx
    · obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hx
      trivial
    · exact hs.map_bound.height x hx

lemma history_length {m d r t h : ℕ} [PseudoMetricSpace (Label (Fin m))]
    {loc : Fin d → Label (Fin m)} {F B Q : Finset (Label (Fin m))} {v lam eta : ℝ}
    {hs : List (List (Label (Fin m)))} (hh : History loc F B v lam eta r Q hs)
    (hn : hs.length≤t) (hF : F.card+B.card≤ m+bankBound m t)
    (hl : ∀ x∈F∪B,(BinaryLabel.encode x).length≤labelBound m t h) :
    (historyBits hs).length≤historyBound m t h := by
  have hb:=hh.phase_bound
  have he:=encode_le_bound (hs.map labels) ((m+bankBound m t)*(2*labelBound m t h+2)) (by
    intro w hw
    obtain ⟨H,hH,rfl⟩:=List.mem_map.mp hw
    exact BinaryFiniteContext.labels_length H ((hb H hH).1.trans hF) (fun x hx=>hl x ((hb H hH).2 x hx)))
  simp only [List.length_map] at he
  simpa only [historyBits,historyBound,Nat.mul_assoc] using he.trans (Nat.mul_le_mul_right _ hn)

section
variable {m d : ℕ} [PseudoMetricSpace (Fin m)]
attribute [local instance] RationalLeaves.metric
lemma length_bound {loc : Fin d → Fin m} {F : Finset (Fin m)} {v eta lo hi : ℝ}
    {q n k h p t : ℕ} {s : State (Fin m)}
    (hc : Certified loc F v eta lo hi q n k s) (hs : s.Resources F q h p) (ht : q+n≤t) :
    (encode s).length≤bound m t h p := by
  have hq : q≤t := by omega
  have hn : n≤t := by omega
  have hF : F.card≤ m := (Finset.card_le_univ F).trans_eq (Fintype.card_fin m)
  have hFi : (F.image original).card≤ m := (Finset.card_image_le).trans hF
  have hB : s.B.card≤bankBound m t := hs.bank.card.trans (Nat.mul_le_mul hq (by omega))
  have hB' : s.mapFree.card≤bankBound m t := hs.map_bound.card.trans (Nat.mul_le_mul hq (by omega))
  have hb := BinaryFiniteContext.setBits_length s.B hB (fun x hx=>bank_labels hs hq x (Finset.mem_union_right _ hx))
  have hb' := BinaryFiniteContext.setBits_length s.mapFree hB' (fun x hx=>mapped_labels hs hq x (Finset.mem_union_right _ hx))
  have hP := history_length hc.old_prefix.history (hc.old_prefix.length_eq.le.trans hq) (Nat.add_le_add hFi hB) (bank_labels hs hq)
  have hP' := history_length hc.new_prefix.history (hc.new_prefix.length_eq.le.trans hq) (Nat.add_le_add hFi hB') (mapped_labels hs hq)
  have hT := history_length hc.new_tail.2.1 (hc.new_tail.1.le.trans hn) (Nat.add_le_add hFi hB') (mapped_labels hs hq)
  have hU := history_length hc.old_tail.2.1 (hc.old_tail.1.le.trans hn) (Nat.add_le_add hFi hB) (bank_labels hs hq)
  have hlam:=BinaryRational.encode_height hs.oldPrice
  have hlam':=BinaryRational.encode_height hs.newPrice
  simp only [encode,WordList.length_encode,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil,bound]
  simp only [Nat.mul_assoc] at *
  omega
end
end MetricKMedianRecovery.BitMachine.BinaryCoupledState

end OAI
