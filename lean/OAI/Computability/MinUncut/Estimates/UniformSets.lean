import Mathlib
import OAI.Computability.MinUncut.Estimates.UniformAlgebra
import OAI.Computability.MinUncut.Encoding.DerivedResolver
import OAI.Computability.MinUncut.Estimates.UniformOutput

namespace OAI

section
noncomputable section
namespace MinUncut.Preprocess
open MinUncut.Outer MinUncutGames.Foundations.Hastad.SourceOccurrences UEncoding
open scoped BigOperators
def maskEquiv (t : ℕ) : Finset (Fin t) ≃ (Fin t → Bool) where
  toFun := hiddenSet
  invFun h := Finset.univ.filter (fun i=>h i=true)
  left_inv S := by ext i; simp [hiddenSet]
  right_inv h := by funext i; simp [hiddenSet]
def setEncoding (t : ℕ) : Encoding (Finset (Fin t)) :=
  ⟨2^t,(maskEquiv t).trans (((Encoding.fin t).function Encoding.bool).code)⟩
def rawSet (t z : ℕ) : Finset (Fin t) :=
  (setEncoding t).code.symm ⟨z%(2^t),Nat.mod_lt _ (pow_pos (by decide) _)⟩
lemma rawSet_code (t : ℕ) (S : Finset (Fin t)) :
    rawSet t ((setEncoding t).code S).val=S := by
  unfold rawSet
  have hs : ((setEncoding t).code S).val<2^t := ((setEncoding t).code S).isLt
  simp only [Nat.mod_eq_of_lt hs]
  exact (setEncoding t).code.symm_apply_apply S
lemma rawSet_maskCode (t z : ℕ) :
    (((Encoding.fin t).function Encoding.bool).code (hiddenSet (rawSet t z))).val=z%(2^t) := by
  change ((setEncoding t).code ((setEncoding t).code.symm _)).val=_
  rw [Equiv.apply_symm_apply]
variable {P : Type} [Primcodable P]
def sets (t : P → ℕ) (ht : Computable t) : UEncoding P (fun p=>Finset (Fin (t p))) where
  enc p := setEncoding (t p)
  computableSize := ca_pow (ca_const 2) ht
lemma map_hidden (t : P → ℕ) (ht : Computable t) :
    (sets t ht).Map ((fin t ht).function bool) (fun _ S=>hiddenSet S) :=
  ⟨Prod.snd,Computable.snd,by intros; rfl⟩
lemma out_setCard (t : P → ℕ) (ht : Computable t) :
    (sets t ht).Out (fun _ S=>S.card) := by
  have hmask:=map_hidden t ht
  have hi := map_apply hmask.first (map_snd (sets t ht) (fin t ht))
  apply (out_sum (out_boolNat hi) Primrec.nat_add.to_comp).ofEq
  intro p S
  have he : ∀i:Fin (t p), (hiddenSet S i).toNat=if i∈S then 1 else 0 := by
    intro i
    by_cases hi:i∈S <;> simp [hiddenSet,hi]
  simp only [he]
  simp
lemma c_rawHidden (t : P → ℕ) (ht : Computable t) (z : P → ℕ) (hz : Computable z) :
    Computable (fun p=>(((Encoding.fin (t p)).function Encoding.bool).code
      (hiddenSet (rawSet (t p) (z p)))).val) :=
  (ca_mod hz (ca_pow (ca_const 2) ht)).of_eq (by intro p; exact (rawSet_maskCode _ _).symm)
end MinUncut.Preprocess

end
end

end OAI
