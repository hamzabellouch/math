import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedModel
import Mathlib.Data.List.NodupEquivFin

namespace OAI

/-! Literal short support lists for the time-ordered history compiler.
The list order, duplicate removal, and local-coordinate equivalence are
explicit; no arbitrary finite-type enumeration enters the input algorithm. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedSupport
open scoped Classical

def gateSites (work : ℕ) : QMAGate → List (Fin (work+1))
  | .hadamard i => [qmaQubit work i]
  | .phaseT i => [qmaQubit work i]
  | .controlledNot i j => [qmaQubit work i,qmaQubit work j]

theorem gateSites_finset (work : ℕ) (g : QMAGate) :
    (gateSites work g).toFinset = qmaGateSites work g := by
  cases g <;> simp [gateSites,qmaGateSites]

theorem gateSites_length (work : ℕ) (g : QMAGate) : (gateSites work g).length ≤ 2 := by
  cases g <;> simp [gateSites]

def propagationSites (c : QMACircuit) (t : Fin c.gates.length) : List (QMACircuitQubit c) :=
  [Sum.inl (qmaClockLeft c.gates.length t),Sum.inl (qmaClockMiddle c.gates.length t),
    Sum.inl (qmaClockRight c.gates.length t)] ++
    (gateSites c.work (c.gates.getD t.val (.hadamard 0))).map Sum.inr

theorem propagationSites_finset (c : QMACircuit) (t : Fin c.gates.length) :
    (propagationSites c t).toFinset = qmaPropagationSites c t := by
  ext i
  simp [propagationSites,qmaPropagationSites,← gateSites_finset,Finset.mem_map]

theorem propagationSites_length (c : QMACircuit) (t : Fin c.gates.length) :
    (propagationSites c t).length ≤ 5 := by
  have h := gateSites_length c.work (c.gates.getD t.val (.hadamard 0))
  simpa only [propagationSites,List.length_append,List.length_cons,List.length_nil,
    List.length_map] using Nat.add_le_add_left h 3

def distributedSites (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) :
    QMACircuitTerm c → List (QMACircuitQubit c)
  | .inl i => [Sum.inl i.castSucc,Sum.inl i.succ]
  | .inr (.inl b) => if b = 0 then [Sum.inl 0]
      else [Sum.inl (Fin.last (c.gates.length+1))]
  | .inr (.inr (.inl i)) => [Sum.inl (τ i).castSucc,Sum.inl (τ i).succ,Sum.inr i]
  | .inr (.inr (.inr (.inl _))) =>
      [Sum.inl (qmaOutputMarker c),Sum.inr (Fin.last c.work)]
  | .inr (.inr (.inr (.inr t))) => propagationSites c t

theorem distributedSites_finset (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (a : QMACircuitTerm c) :
    (distributedSites c τ a).toFinset = qmaDistributedTermSites c τ a := by
  rcases a with i | (b | (i | (u | t)))
  · simp [distributedSites,qmaDistributedTermSites,qmaCircuitTermSites]
  · by_cases hb : b = 0 <;>
      simp [distributedSites,qmaDistributedTermSites,qmaCircuitTermSites,hb]
  · simp [distributedSites,qmaDistributedTermSites,qmaDistributedInputSites]
  · simp [distributedSites,qmaDistributedTermSites,qmaCircuitTermSites]
  · exact propagationSites_finset c t

theorem distributedSites_length (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (a : QMACircuitTerm c) :
    (distributedSites c τ a).length ≤ 5 := by
  rcases a with i | (b | (i | (u | t)))
  · simp [distributedSites]
  · by_cases hb : b = 0 <;> simp [distributedSites,hb]
  · simp [distributedSites]
  · simp [distributedSites]
  · exact propagationSites_length c t

abbrev Qubit (c : QMACircuit) := Fin (qmaHistoryReferenceWork c+1) ⊕ QMACircuitQubit c

def rawSites (c : QMACircuit) (hT : 0 < c.gates.length) :
    QMAReferenceTerm (qmaHistoryReferenceWork c) → List (Qubit c)
  | .inl i => Sum.inl i ::
      (distributedSites c (qmaFirstUseTime c)
        (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i)).map Sum.inr
  | .inr i => [Sum.inl i.castSucc,Sum.inl i.succ]

theorem rawSites_finset (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) :
    (rawSites c hT a).toFinset = (qmaOrderedHistoryModel c hT).sites a := by
  cases a with
  | inl i =>
    ext x
    simp [rawSites,qmaOrderedHistoryModel,qmaReferenceTermSites,qmaDistributedRebitSites,
      qmaOrderedHistorySites,← distributedSites_finset,Finset.mem_map]
  | inr i => simp [rawSites,qmaOrderedHistoryModel,qmaReferenceTermSites,qmaReferenceEdgeSites]

theorem rawSites_length (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) : (rawSites c hT a).length ≤ 6 := by
  cases a with
  | inl i =>
    have h := distributedSites_length c (qmaFirstUseTime c)
      (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i)
    simpa only [rawSites,List.length_cons,List.length_map] using Nat.succ_le_succ h
  | inr i => simp [rawSites]

def sites (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) : List (Qubit c) :=
  (rawSites c hT a).dedup

theorem sites_nodup (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) : (sites c hT a).Nodup := by
  exact List.nodup_dedup _

theorem sites_finset (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) :
    (sites c hT a).toFinset = (qmaOrderedHistoryModel c hT).sites a := by
  simpa [sites] using rawSites_finset c hT a

theorem sites_length (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) : (sites c hT a).length ≤ 6 := by
  rw [← List.toFinset_card_of_nodup (sites_nodup c hT a),sites_finset]
  exact (qmaOrderedHistoryModel c hT).card a

def supportEquiv (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) :
    Fin (sites c hT a).length ≃ {x // x ∈ (qmaOrderedHistoryModel c hT).sites a} :=
  (List.Nodup.getEquiv (sites c hT a) (sites_nodup c hT a)).trans
    (Equiv.subtypeEquivRight (fun x => by
      have he := congrArg (fun S : Finset (Qubit c) => x ∈ S) (sites_finset c hT a)
      exact List.mem_toFinset.symm.trans (Iff.of_eq he)))

theorem supportEquiv_apply (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) (i : Fin (sites c hT a).length) :
    (supportEquiv c hT a i).val = (sites c hT a).get i := rfl

def siteNumber (c : QMACircuit) : Qubit c → ℕ
  | .inl i => i.val
  | .inr (.inl i) => qmaHistoryReferenceWork c+1+i.val
  | .inr (.inr i) => qmaHistoryReferenceWork c+1+(c.gates.length+2)+i.val

theorem siteNumber_lt (c : QMACircuit) (i : Qubit c) :
    siteNumber c i < 3*c.gates.length+2*c.work+8 := by
  rcases i with i | (i | i) <;> have h := i.isLt <;>
    simp only [siteNumber,qmaHistoryReferenceWork] at * <;> omega

theorem siteNumber_injective (c : QMACircuit) : Function.Injective (siteNumber c) := by
  intro i j h
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
    simp only [siteNumber] at h
  all_goals have hi := i.isLt
  all_goals have hj := j.isLt
  · exact congrArg Sum.inl (Fin.ext h)
  · omega
  · omega
  · omega
  · exact congrArg (fun x => Sum.inr (Sum.inl x)) (Fin.ext (by omega))
  · omega
  · omega
  · omega
  · exact congrArg (fun x => Sum.inr (Sum.inr x)) (Fin.ext (by omega))

def encodedSites (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) : List ℕ :=
  (sites c hT a).map (siteNumber c)

theorem encodedSites_nodup (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) : (encodedSites c hT a).Nodup :=
  (sites_nodup c hT a).map (siteNumber_injective c)

theorem encodedSites_length (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) : (encodedSites c hT a).length ≤ 6 := by
  simpa only [encodedSites,List.length_map] using sites_length c hT a

end ContinuumCoulomb.QuantumOrderedSupport

end

end OAI
