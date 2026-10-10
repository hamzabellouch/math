import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.StateBits2
import OAI.Combinatorics.KMedianRecovery.Encoding.CoupledEncode

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open RationalLeaves
variable {V : Type*} [LinearOrder V] {d : ℕ}
def Correction.Keys (q : ℕ) : Correction V→Prop
  | .identity=>True
  | .shorten key _ _ _=>key<3*q
omit [LinearOrder V] in
lemma Correction.Keys.mono {r : Correction V} {q t : ℕ} (h : r.Keys q) (hqt : q≤t) : r.Keys t := by
  cases r with
  | identity=>trivial
  | shorten key i l u=>exact h.trans_le (Nat.mul_le_mul_left 3 hqt)
def Outcome.Keys (q : ℕ) : Outcome V→Prop
  | .inl _=>True
  | .inr s=>s.correction.Keys (q+1)
lemma resolve_keys (loc : Fin d→V) (distance : V→Fin d→ℚ) (F : Finset V)
    (v M : ℚ) (N precision q n k : ℕ) (B : Finset (Label V)) (lam : ℚ)
    (P : List (List (Label V))) (R : CanonicalMergeCrossing.Result (Label V)) :
    (resolve loc distance F v M N precision q n k (3*q+2) B lam P R).Keys q := by
  cases R with
  | success H T=>trivial
  | common H T U=>trivial
  | sensitive H G T U=>
    dsimp only [resolve]
    split
    · trivial
    · split
      · trivial
      · change 3*q+2<3*(q+1)
        omega
lemma step_keys (loc : Fin d→V) (distance : V→Fin d→ℚ) (F : Finset V)
    (v M : ℚ) (N precision q n k : ℕ) (s : State V) (hk : s.correction.Keys q) :
    (step loc distance F v M N precision q n k s).Keys q := by
  dsimp only [step]
  split
  · split_ifs
    · trivial
    · exact resolve_keys ..
    · change s.correction.Keys (q+1)
      exact hk.mono (by omega)
  · trivial
end MetricKMedianRecovery.CanonicalCoupledMerge

namespace MetricKMedianRecovery.BitMachine.BinaryCorrection
open WordOperations RationalLeaves CanonicalCoupledMerge
lemma length_bound {m q h : ℕ} (r : Correction (Fin m)) (hb : r.Bounded h) (hk : r.Keys q) :
    (encode r).length≤3*BinaryCoupledState.labelBound m q h+1 := by
  cases r with
  | identity=>simp only [encode,List.length_nil]; omega
  | shorten key i l u=>
    have hl:=BinaryLabel.encode_length_bound (leaf key i l) (show level (leaf key i l)≤3*q by exact hk)
      (show HeightBound h (leaf key i l) from hb.1)
    have hu:=BinaryLabel.encode_length_bound (leaf key i u) (show level (leaf key i u)≤3*q by exact hk)
      (show HeightBound h (leaf key i u) from hb.2)
    simp only [encode,pairBits_length,BinaryCoupledState.labelBound]
    omega
end MetricKMedianRecovery.BitMachine.BinaryCorrection

namespace MetricKMedianRecovery.BitMachine.BinaryCoupled
open WordOperations WordList RationalLeaves CanonicalCoupledMerge
variable {m d : ℕ} [PseudoMetricSpace (Fin m)]
attribute [local instance] RationalLeaves.metric
def bound (m t h p : ℕ) : ℕ := BinaryCoupledState.bound m t h p+6*BinaryCoupledState.labelBound m t h+2
lemma length_bound {loc : Fin d→Fin m} {F : Finset (Fin m)} {v eta lo hi : ℝ}
    {q n k h p t : ℕ} {s : State (Fin m)}
    (hc : Certified loc F v eta lo hi q n k s) (hs : s.Resources F q h p)
    (hk : s.correction.Keys q) (ht : q+n≤t) :
    (stateBits s).length≤bound m t h p := by
  have ho:=BinaryCoupledState.length_bound hc hs ht
  have hr:=BinaryCorrection.length_bound s.correction hs.correction (hk.mono (show q≤t by omega))
  have he : (stateBits s).length≤(BinaryCoupledState.encode s).length+2*(BinaryCorrection.encode s.correction).length := by
    simp only [stateBits,BinaryCoupledState.encode,length_encode,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
    omega
  dsimp only [bound]
  omega
end MetricKMedianRecovery.BitMachine.BinaryCoupled

namespace MetricKMedianRecovery.BitMachine.BinaryCoupled
open WordOperations WordList RationalLeaves RationalHeight CanonicalCoupledMerge
open BinaryCoupledState (labelBound bankBound historyBound)
open BinaryFiniteContext (setBits)
open BinaryFiniteMachine (historyBits)
variable {m d : ℕ} [PseudoMetricSpace (Fin m)]
attribute [local instance] RationalLeaves.metric
lemma output_length_bound {loc : Fin d→Fin m} {F : Finset (Fin m)} {v eta lo hi : ℝ}
    {t total q k h p : ℕ} {o : Output (Fin m)} (hc : o.Correct loc F v eta lo hi total k)
    (hs : o.Resources F q h p) (hq : q≤t) (ht : total≤t) :
    (outputBits o).length≤bound m t h p := by
  have hF : F.card≤ m := (Finset.card_le_univ F).trans_eq (Fintype.card_fin m)
  have hFi : (F.image original).card≤ m := Finset.card_image_le.trans hF
  have hB : o.B.card≤bankBound m t := hs.bank.card.trans (Nat.mul_le_mul hq (by omega))
  have hl : ∀ x∈F.image original∪o.B,(BinaryLabel.encode x).length≤labelBound m t h := by
    intro x hx
    apply (BinaryLabel.encode_length_bound x ?_ ?_).trans (show 2*(3*t)+2*m+3*h+8≤labelBound m t h by unfold labelBound; omega)
    · rcases Finset.mem_union.mp hx with hx|hx
      · obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hx
        exact Nat.zero_le _
      · exact (hs.bank.before.level x hx).trans (Nat.mul_le_mul_left _ hq)
    · rcases Finset.mem_union.mp hx with hx|hx
      · obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hx
        trivial
      · exact hs.bank.height x hx
  have hb:=BinaryFiniteContext.setBits_length o.B hB (fun x hx=>hl x (Finset.mem_union_right _ hx))
  have hp:=BinaryCoupledState.history_length hc.2.2.2.1.history (hc.2.2.2.1.length_eq.le.trans ht) (Nat.add_le_add hFi hB) hl
  have hprice:=BinaryRational.encode_height hs.price
  simp only [outputBits,length_encode,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil,
    bound,BinaryCoupledState.bound]
  simp only [Nat.mul_assoc] at *
  omega
end MetricKMedianRecovery.BitMachine.BinaryCoupled

end OAI
