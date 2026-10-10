import Mathlib
import OAI.Computability.QuantumFactoring.ListTransition
import OAI.Computability.QuantumFactoring.FavorableSplit

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness RepeatedTrials

noncomputable def canonicalList {m : ℕ} (hm : m≠0) (p₀ : Component m) (K : ℕ) :
    Fin K→Basis (Nat.clog 2 m) := fun i =>
  (bitsEquiv _).symm (BitVec.ofNat (Nat.clog 2 m) (if i.val=0 then (canonicalUnit hm p₀ : ZMod m).val else 0))

lemma canonicalList_good {m n K : ℕ} (hm : m≠0) (hb : m<2^n) (hodd : Odd m)
    (p₀ p₁ : Component m) (hne : p₁≠p₀) (hK : 0<K) :
    GoodList hm hb p₀ K (canonicalList hm p₀ K) := by
  let : NeZero m := ⟨hm⟩
  refine ⟨⟨0,hK⟩,canonicalUnit hm p₀,?_,canonicalUnit_favorable hm hb hodd p₀ p₁ hne⟩
  simp only [canonicalList,bitsEquiv,Equiv.coe_fn_symm_mk,bitsValue_bits,
    BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt ((ZMod.val_lt _).trans_le (Nat.le_pow_clog (by decide : 1<2) m))).symm

end ExactQuantumFactoring


end

end OAI
