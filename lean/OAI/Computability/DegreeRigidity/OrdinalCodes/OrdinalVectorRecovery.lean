import OAI.Computability.DegreeRigidity.OrdinalCodes.OrdinalVectorSyntax

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalArithmetic
universe u

theorem vectorCodeSentence_recovers (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (n : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (v : Fin n → Ordinal.{u}) (hc : e 0 = (vectorCode v).toZFSet)
    (hp : (vectorCodeSentence n).Sat (M : Set ZFSet) e) :
    ∀ i, e (i.val+1) = (v i).toZFSet := by
  induction n generalizing e with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨t,ht,hpair,hrest⟩ := hp
    rw [SentenceForm.sat_rename] at hpair hrest
    have hrec := pairCodeSentence_recovers M hM hω
      (fun i => cons t e (if i = 0 then 1 else if i = 1 then 2 else 0)) (fun i => by
        split; exact he 0
        split; exact he 1
        exact ht) (v 0) (vectorCode (fun i => v i.succ)) hc hpair
    have hh : e 1 = (v 0).toZFSet := hrec.1
    have htcode : t = (vectorCode (fun i => v i.succ)).toZFSet := hrec.2
    have htail := ih (fun i => cons t e (vectorTailSlots i)) (fun i => by
      cases i; exact ht; exact he _) (fun i => v i.succ) htcode hrest
    intro i
    exact Fin.cases hh (fun j => htail j) i

theorem vectorCodeSentence_recognition (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (n : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (v : Fin n → Ordinal.{u}) (hc : e 0 = (vectorCode v).toZFSet) :
    (vectorCodeSentence n).Sat (M : Set ZFSet) e ↔ ∀ i, e (i.val+1) = (v i).toZFSet := by
  refine ⟨vectorCodeSentence_recovers M hM
    (omega_mem M hM hT.separation.finitePrefix.bounded hT.infinity) n e he v hc,?_⟩
  intro hv
  exact (vectorCodeSentence_sourceT M hM hT n e he v hv).mpr hc

end TuringRigidity.OrdinalCoding

end OAI
