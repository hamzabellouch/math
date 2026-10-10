import Mathlib
import OAI.Computability.QuantumFactoring.TransitionEqualization
import OAI.Computability.QuantumFactoring.CanonicalTransition
import OAI.Computability.QuantumFactoring.RuntimeListPreparation

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

namespace TransitionWords

/-- K n-bit words in consecutive little-endian fields, followed by one zero
word. This fits exactly the source's W=n(K+1) output cap. -/
def encode {n K : ℕ} (a : Fin K→Basis n) : Basis (n*(K+1)) := fun i =>
  let j := finProdFinEquiv.symm (Fin.cast (Nat.mul_comm _ _) i)
  if h : j.1.val<K then a ⟨j.1.val,h⟩ j.2 else false

def read {n K : ℕ} (x : Basis (n*(K+1))) (i : Fin K) : Basis n := fun j =>
  x (Fin.cast (Nat.mul_comm _ _) (finProdFinEquiv (i.castSucc,j)))

lemma read_encode {n K : ℕ} (a : Fin K→Basis n) (i : Fin K) : read (encode a) i=a i := by
  funext j
  simp only [read,encode,Fin.cast_cast,Fin.cast_eq_self,Equiv.symm_apply_apply,Fin.val_castSucc]
  rw [dite_eq_left i.isLt]

lemma encode_injective (n K : ℕ) : Function.Injective (@encode n K) := by
  intro a b hh
  funext i
  have he := congrArg (fun x => read x i) hh
  simpa only [read_encode] using he

lemma pow_width_le (n K : ℕ) : 2^n ≤ 2^(n*(K+1)) := by
  apply Nat.pow_le_pow_right (by decide : 1≤2)
  nlinarith

end TransitionWords

namespace ListSlots

abbrev K (n : ℕ) := n^5
abbrev Ordinary (n m : ℕ) := Fin (K n)→Basis (Nat.clog 2 m)
abbrev Result (n m : ℕ) := Completion.Raw (Ordinary n m) (Completion.transitionWidth n)
  (2*n) (n*K n)

noncomputable def fresh (n m : ℕ) : Result n m→ℂ :=
  Completion.fresh (tensorState (fairState (Nat.clog 2 m)) (K n))
    (Completion.transitionWidth n) (2*n) (n*K n)

def ordinary {n m : ℕ} (hb : m < 2^n) (x : Ordinary n m) : Basis (Completion.transitionWidth n) :=
  TransitionWords.encode (fun i => padBits (Nat.clog_le_of_le_pow hb.le) (x i))

noncomputable def canonical {n m : ℕ} (hm : m ≠ 0) (hb : m < 2^n) (p₀ : Component m) :
    Basis (Completion.transitionWidth n) := ordinary hb (canonicalList hm p₀ (K n))

noncomputable def passed {n m : ℕ} (hm : m ≠ 0) (hb : m < 2^n) (p₀ : Component m) : Result n m→Prop :=
  Completion.passed (GoodList hm hb p₀ (K n)) (canonical hm hb p₀)
    (Completion.listSuccess m n (K n)) (Completion.target n)

def output {n m : ℕ} (hb : m < 2^n) : Result n m→Basis (Completion.transitionWidth n) :=
  Completion.output (ordinary hb)

noncomputable def GoodOutput {n m : ℕ} (hm : m ≠ 0) (hb : m < 2^n) (p₀ : Component m)
    (y : Basis (Completion.transitionWidth n)) : Prop :=
  ∃ (i : Fin (K n)) (u : (ZMod m)ˣ),
    (bitsValue (TransitionWords.read y i)).toNat=(u : ZMod m).val ∧ FavorableUnit hm hb p₀ u

lemma ordinary_good {n m : ℕ} (hm : m ≠ 0) (hb : m < 2^n) (p₀ : Component m)
    (x : Ordinary n m) (hh : GoodList hm hb p₀ (K n) x) :
    GoodOutput hm hb p₀ (ordinary hb x) := by
  obtain ⟨i,u,hu,hf⟩ := hh
  refine ⟨i,u,?_,hf⟩
  change (bitsValue (TransitionWords.read (TransitionWords.encode _) i)).toNat=_
  rw [TransitionWords.read_encode,padBits_value]
  exact hu.symm

lemma canonical_good {n m : ℕ} (hn : 128 ≤ n) (hm : m ≠ 0) (hb : m < 2^n) (hodd : Odd m)
    (p₀ p₁ : Component m) (hne : p₁≠p₀) : GoodOutput hm hb p₀ (canonical hm hb p₀) := by
  apply ordinary_good
  exact canonicalList_good hm hb hodd p₀ p₁ hne (pow_pos (by omega) _)

lemma fresh_normalized (n m : ℕ) : ∑ r,Complex.normSq (fresh n m r)=1 :=
  Completion.fresh_normalized _ _ _ _ (tensor_normalized _ _ (fairState_normalized _))

lemma passed_mass {n m : ℕ} (hn : 128 ≤ n) (hm : 2 ≤ m) (hb : m < 2^n) (hodd : Odd m)
    (p₀ p₁ : Component m) (hne : p₁≠p₀) :
    outcomeMass (passed (by omega : m ≠ 0) hb p₀) (fresh n m)=(Completion.target n:ℝ) :=
  Completion.list_passed_mass hn hm hb hodd p₀ p₁ hne (canonical (by omega) hb p₀)

lemma passed_good {n m : ℕ} (hn : 128 ≤ n) (hm : m ≠ 0) (hb : m < 2^n) (hodd : Odd m)
    (p₀ p₁ : Component m) (hne : p₁≠p₀) (r : Result n m) (hp : passed hm hb p₀ r) :
    GoodOutput hm hb p₀ (output hb r) := by
  rcases hp with hp | hp
  · rw [output,Completion.output,ite_eq_right hp.1]
    exact ordinary_good hm hb p₀ _ hp.2.1
  · rw [output,Completion.output,ite_eq_left hp.1,hp.2.1]
    exact canonical_good hn hm hb hodd p₀ p₁ hne

end ListSlots
end ExactQuantumFactoring


end

end OAI
