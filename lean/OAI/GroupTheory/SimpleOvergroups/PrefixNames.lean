import Mathlib
import OAI.GroupTheory.SimpleOvergroups.CanonicalNames
import OAI.GroupTheory.SimpleOvergroups.PrefixEffective
import OAI.GroupTheory.SimpleOvergroups.PrefixProduct

namespace OAI


namespace BinaryPrefixOperators.Arithmetic

 theorem primrec_cancel : Primrec₂ cancel := by
  unfold cancel
  exact Primrec.ite
    (Primrec.eq.comp (Primrec.list_take.comp (Primrec.list_length.comp Primrec.fst) Primrec.snd)
      Primrec.fst)
    (Primrec.option_some.comp ((Primrec.list_drop.comp
      (Primrec.list_length.comp Primrec.fst) Primrec.snd).pair (Primrec.const [])))
    (Primrec.ite
      (Primrec.eq.comp (Primrec.list_take.comp (Primrec.list_length.comp Primrec.snd) Primrec.fst)
        Primrec.snd)
      (Primrec.option_some.comp ((Primrec.const []).pair
        (Primrec.list_drop.comp (Primrec.list_length.comp Primrec.snd) Primrec.fst)))
      (Primrec.const none))

 theorem primrec_multiplyPair : Primrec₂ multiplyPair := by
  unfold multiplyPair
  exact Primrec.option_map
    (primrec_cancel.comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
    ((Primrec.list_append.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) (Primrec.fst.comp Primrec.snd)).pair
      (Primrec.list_append.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.snd.comp Primrec.snd))).to₂

namespace Lists
variable {K : Type*} [CommRing K]

def negate (p : Poly K) : Poly K := p.map (fun a => (-a.1,a.2))

@[simp] theorem value_negate (p : Poly K) : value (negate p) = -value p := by
  induction p with
  | nil => simp [negate]
  | cons a p ih =>
    rcases a with ⟨a,v⟩
    simp only [negate] at ih ⊢
    simp [ih, neg_smul, neg_add_rev, add_comm]

def oneName : Poly K := [(1,([],[]))]

@[simp] theorem value_oneName : value (oneName (K:=K)) = 1 := by
  simp [oneName, replacement]

variable [Primcodable K] [Finite K]

 theorem primrec_negate : Primrec (negate (K:=K)) :=
  Primrec.list_map Primrec.id (((Primrec.dom_finite (fun a : K => -a)).comp
    (Primrec.fst.comp Primrec.snd)).pair (Primrec.snd.comp Primrec.snd)).to₂

 theorem primrec_mulTerm : Primrec₂ (mulTerm (K:=K)) := by
  have h : Primrec₂ (fun a b : K × Pair =>
      (multiplyPair a.2 b.2).map (fun p => (a.1*b.1,p))) := by
    exact Primrec.option_map
      (primrec_multiplyPair.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
      ((((Primrec.dom_finite (fun a : K × K => a.1*a.2)).comp
        ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))).pair Primrec.snd)).to₂
  have ht : Primrec (fun x : Option (K × Pair) => x.toList) := by
    refine (Primrec.option_casesOn Primrec.id (Primrec.const [])
      (Primrec.list_cons.comp Primrec.snd (Primrec.const [])).to₂).of_eq ?_
    intro x; cases x <;> rfl
  exact ht.comp h

 theorem primrec_product : Primrec₂ (product (K:=K)) := by
  unfold product
  apply Primrec.list_flatMap Primrec.fst
  change Primrec (fun p : (Poly K × Poly K) × (K × Pair) => p.1.2.flatMap (mulTerm p.2))
  apply Primrec.list_flatMap (Primrec.snd.comp Primrec.fst)
  exact (primrec_mulTerm.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂

variable [DecidableEq K]

noncomputable section
open scoped Classical

theorem computable_value_eq : ComputablePred
    (fun p : Poly K × Poly K => value p.1 = value p.2) := by
  have hc : ComputablePred (fun p : Poly K × Poly K =>
      zeroTest (p.1 ++ negate p.2) = true) :=
    (Primrec.eq.comp (primrec_zeroTest.comp
      (Primrec.list_append.comp Primrec.fst (primrec_negate.comp Primrec.snd)))
      (Primrec.const true)).computablePred
  apply hc.of_eq
  intro p
  rw [zeroTest_iff]
  change value (p.1 ++ negate p.2) = 0 ↔ _
  rw [value_append, value_negate, ← sub_eq_add_neg, sub_eq_zero]

def coefficientKey : Poly K → ℕ := SimpleFInftyOvergroups.EffectiveNames.key value

omit [Finite K] [DecidableEq K] in
 theorem coefficientKey_eq_iff (p q : Poly K) :
    coefficientKey p = coefficientKey q ↔ value p = value q :=
  SimpleFInftyOvergroups.EffectiveNames.key_eq_iff value p q

 theorem computable_coefficientKey : Computable (coefficientKey (K:=K)) :=
  SimpleFInftyOvergroups.EffectiveNames.computable_key value computable_value_eq

end
end Lists
end BinaryPrefixOperators.Arithmetic

end OAI
