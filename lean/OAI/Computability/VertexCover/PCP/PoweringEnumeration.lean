import Mathlib
import OAI.Computability.VertexCover.PCP.PoweringAddresses

namespace OAI

                                                                                            

namespace UniqueGames.Foundations.PCP.PoweringEnumeration

open PoweringLabels
open scoped BigOperators

def addressCount (d t : Nat) : Nat := ∑ i : Fin (t + 1), d ^ i.val

def reverseWordEquiv (d n : Nat) : (Fin n → Fin d) ≃ (Fin n → Fin d) where
  toFun p i := p i.rev
  invFun p i := p i.rev
  left_inv p := by funext i; simp only [Fin.rev_rev]
  right_inv p := by funext i; simp only [Fin.rev_rev]

def wordEquiv (d n : Nat) : (Fin n → Fin d) ≃ Fin (d ^ n) :=
  (reverseWordEquiv d n).trans finFunctionFinEquiv

theorem wordEquiv_val (d n : Nat) (p : Fin n → Fin d) :
    (wordEquiv d n p).val = ∑ i : Fin n, (p i.rev).val * d ^ i.val := rfl

def addressEquiv (d t : Nat) : PortWords (Fin d) t ≃ Fin (addressCount d t) :=
  (Equiv.sigmaCongrRight (fun i : Fin (t + 1) => wordEquiv d i.val)).trans
    finSigmaFinEquiv

theorem addressEquiv_val (d t : Nat) (w : PortWords (Fin d) t) :
    (addressEquiv d t w).val =
      (∑ i : Fin w.1.val, d ^ i.val) + (wordEquiv d w.1.val w.2).val := by
  change (finSigmaFinEquiv
    (⟨w.1, wordEquiv d w.1.val w.2⟩ : (i : Fin (t + 1)) × Fin (d ^ i.val))).val = _
  rw [finSigmaFinEquiv_apply]
  rfl

def paddedLabelEquiv (d t q : Nat) :
    PaddedLabel (Fin d) t (Fin q) ≃ Fin (q ^ addressCount d t) :=
  ((addressEquiv d t).arrowCongr (Equiv.refl (Fin q))).trans
    (wordEquiv q (addressCount d t))

theorem paddedLabelEquiv_val (d t q : Nat) (a : PaddedLabel (Fin d) t (Fin q)) :
    (paddedLabelEquiv d t q a).val =
      ∑ i : Fin (addressCount d t),
        (a ((addressEquiv d t).symm i.rev)).val * q ^ i.val := rfl

def orientationEquiv : Bool ≃ Fin 2 := finTwoEquiv.symm

@[simp] theorem orientationEquiv_false : orientationEquiv false = 0 := rfl
@[simp] theorem orientationEquiv_true : orientationEquiv true = 1 := rfl

def dartBlockEquiv (d n : Nat) :
    ((Fin (n + 1) → Fin d) × Bool) ≃ Fin (2 * d ^ (n + 1)) :=
  ((wordEquiv d (n + 1)).prodCongr orientationEquiv).trans
    (finProdFinEquiv.trans (finCongr (Nat.mul_comm (d ^ (n + 1)) 2)))

theorem dartBlockEquiv_val (d n : Nat) (p : Fin (n + 1) → Fin d) (b : Bool) :
    (dartBlockEquiv d n (p, b)).val =
      2 * (wordEquiv d (n + 1) p).val + (orientationEquiv b).val := by
  change (orientationEquiv b).val + 2 * (wordEquiv d (n + 1) p).val = _
  exact Nat.add_comm _ _

def dartVertexEquiv (vertices d n : Nat) :
    (Bool × (Fin vertices × (Fin (n + 1) → Fin d))) ≃
      (Fin vertices × ((Fin (n + 1) → Fin d) × Bool)) where
  toFun x := (x.2.1, (x.2.2, x.1))
  invFun x := (x.2.2, (x.1, x.2.1))
  left_inv x := by rcases x with ⟨b, v, p⟩; rfl
  right_inv x := by rcases x with ⟨v, p, b⟩; rfl

def dartEquiv (vertices d n : Nat) :
    (Bool × (Fin vertices × (Fin (n + 1) → Fin d))) ≃
      Fin (2 * vertices * d ^ (n + 1)) :=
  (dartVertexEquiv vertices d n).trans
    (((Equiv.refl (Fin vertices)).prodCongr (dartBlockEquiv d n)).trans
      (finProdFinEquiv.trans
        (finCongr (show vertices * (2 * d ^ (n + 1)) =
          2 * vertices * d ^ (n + 1) by ac_rfl))))

theorem dartEquiv_val (vertices d n : Nat) (b : Bool) (v : Fin vertices)
    (p : Fin (n + 1) → Fin d) :
    (dartEquiv vertices d n (b, (v, p))).val =
      (2 * d ^ (n + 1)) * v.val +
        2 * (wordEquiv d (n + 1) p).val + (orientationEquiv b).val := by
  change (dartBlockEquiv d n (p, b)).val + (2 * d ^ (n + 1)) * v.val = _
  rw [dartBlockEquiv_val]
  omega

theorem dartEquiv_true_eq_false_add_one (vertices d n : Nat) (v : Fin vertices)
    (p : Fin (n + 1) → Fin d) :
    (dartEquiv vertices d n (true, (v, p))).val =
      (dartEquiv vertices d n (false, (v, p))).val + 1 := by
  rw [dartEquiv_val, dartEquiv_val, orientationEquiv_true, orientationEquiv_false]
  rfl

def encodeWord (d n : Nat) : (Fin n → Fin d) → Fin (d ^ n) := wordEquiv d n
def decodeWord (d n : Nat) : Fin (d ^ n) → (Fin n → Fin d) := (wordEquiv d n).symm

@[simp] theorem decodeWord_encodeWord (d n : Nat) (p : Fin n → Fin d) :
    decodeWord d n (encodeWord d n p) = p := (wordEquiv d n).symm_apply_apply p

@[simp] theorem encodeWord_decodeWord (d n : Nat) (i : Fin (d ^ n)) :
    encodeWord d n (decodeWord d n i) = i := (wordEquiv d n).apply_symm_apply i

def encodeAddress (d t : Nat) : PortWords (Fin d) t → Fin (addressCount d t) :=
  addressEquiv d t

def decodeAddress (d t : Nat) : Fin (addressCount d t) → PortWords (Fin d) t :=
  (addressEquiv d t).symm

@[simp] theorem decodeAddress_encodeAddress (d t : Nat) (w : PortWords (Fin d) t) :
    decodeAddress d t (encodeAddress d t w) = w := (addressEquiv d t).symm_apply_apply w

@[simp] theorem encodeAddress_decodeAddress (d t : Nat) (i : Fin (addressCount d t)) :
    encodeAddress d t (decodeAddress d t i) = i := (addressEquiv d t).apply_symm_apply i

def encodeLabel (d t q : Nat) :
    PaddedLabel (Fin d) t (Fin q) → Fin (q ^ addressCount d t) := paddedLabelEquiv d t q

def decodeLabel (d t q : Nat) :
    Fin (q ^ addressCount d t) → PaddedLabel (Fin d) t (Fin q) :=
  (paddedLabelEquiv d t q).symm

@[simp] theorem decodeLabel_encodeLabel (d t q : Nat) (a : PaddedLabel (Fin d) t (Fin q)) :
    decodeLabel d t q (encodeLabel d t q a) = a := (paddedLabelEquiv d t q).symm_apply_apply a

@[simp] theorem encodeLabel_decodeLabel (d t q : Nat) (i : Fin (q ^ addressCount d t)) :
    encodeLabel d t q (decodeLabel d t q i) = i := (paddedLabelEquiv d t q).apply_symm_apply i

@[simp] theorem decodeLabel_apply (d t q : Nat) (i : Fin (q ^ addressCount d t))
    (w : PortWords (Fin d) t) :
    decodeLabel d t q i w = decodeWord q (addressCount d t) i (encodeAddress d t w) := rfl

def encodeDart (vertices d n : Nat) :
    (Bool × (Fin vertices × (Fin (n + 1) → Fin d))) →
      Fin (2 * vertices * d ^ (n + 1)) := dartEquiv vertices d n

def decodeDart (vertices d n : Nat) :
    Fin (2 * vertices * d ^ (n + 1)) →
      (Bool × (Fin vertices × (Fin (n + 1) → Fin d))) := (dartEquiv vertices d n).symm

@[simp] theorem decodeDart_encodeDart (vertices d n : Nat)
    (e : Bool × (Fin vertices × (Fin (n + 1) → Fin d))) :
    decodeDart vertices d n (encodeDart vertices d n e) = e :=
  (dartEquiv vertices d n).symm_apply_apply e

@[simp] theorem encodeDart_decodeDart (vertices d n : Nat)
    (i : Fin (2 * vertices * d ^ (n + 1))) :
    encodeDart vertices d n (decodeDart vertices d n i) = i :=
  (dartEquiv vertices d n).apply_symm_apply i

theorem card_words (d n : Nat) : Nat.card (Fin n → Fin d) = d ^ n := by
  simpa only [Nat.card_fin] using Nat.card_congr (wordEquiv d n)

theorem card_addresses (d t : Nat) :
    Nat.card (PortWords (Fin d) t) = addressCount d t := by
  simpa only [Nat.card_fin] using Nat.card_congr (addressEquiv d t)

theorem card_labels (d t q : Nat) :
    Nat.card (PaddedLabel (Fin d) t (Fin q)) = q ^ addressCount d t := by
  simpa only [Nat.card_fin] using Nat.card_congr (paddedLabelEquiv d t q)

theorem card_darts (vertices d n : Nat) :
    Nat.card (Bool × (Fin vertices × (Fin (n + 1) → Fin d))) =
      2 * vertices * d ^ (n + 1) := by
  simpa only [Nat.card_fin] using Nat.card_congr (dartEquiv vertices d n)

theorem length_allAddresses (d t : Nat) :
    (PoweringAddresses.allAddresses d t).length = addressCount d t :=
  PoweringAddresses.length_allAddresses d t

end UniqueGames.Foundations.PCP.PoweringEnumeration

end OAI
