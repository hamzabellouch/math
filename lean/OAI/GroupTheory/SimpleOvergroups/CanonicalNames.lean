import Mathlib

namespace OAI

namespace SimpleFInftyOvergroups.EffectiveNames
noncomputable section
open scoped Classical
variable {A Q : Type*} [Primcodable A] (q : A → Q)

def acceptsName (a : A) (n : ℕ) : Bool :=
  (Encodable.decode (α := A) n).elim false (fun b => decide (q b = q a))

theorem acceptsName_iff (a : A) (n : ℕ) :
    acceptsName q a n = true ↔ ∃ b, Encodable.decode (α := A) n = some b ∧ q b = q a := by
  unfold acceptsName
  cases h : Encodable.decode (α := A) n <;> simp

theorem match_exists (a : A) : ∃ n, acceptsName q a n = true :=
  ⟨Encodable.encode a, (acceptsName_iff q a _).mpr ⟨a, Encodable.encodek a, rfl⟩⟩

def key (a : A) : ℕ := Nat.find (match_exists q a)

theorem key_spec (a : A) :
    ∃ b, Encodable.decode (α := A) (key q a) = some b ∧ q b = q a :=
  (acceptsName_iff q a _).mp (Nat.find_spec (match_exists q a))

theorem key_congr {a b : A} (h : q a = q b) : key q a = key q b := by
  apply Nat.le_antisymm
  · apply Nat.find_min'
    obtain ⟨c,hc,he⟩ := key_spec q b
    exact (acceptsName_iff q a _).mpr ⟨c,hc,he.trans h.symm⟩
  · apply Nat.find_min'
    obtain ⟨c,hc,he⟩ := key_spec q a
    exact (acceptsName_iff q b _).mpr ⟨c,hc,he.trans h⟩

theorem key_eq_iff (a b : A) : key q a = key q b ↔ q a = q b := by
  constructor
  · intro h
    obtain ⟨x,hx,he⟩ := key_spec q a
    obtain ⟨y,hy,hf⟩ := key_spec q b
    rw [h] at hx
    have hxy : x=y := Option.some.inj (hx.symm.trans hy)
    exact he.symm.trans (hxy ▸ hf)
  · exact key_congr q

def semanticKey (hq : Function.Surjective q) (x : Q) : ℕ :=
  key q (Classical.choose (hq x))

@[simp] theorem semanticKey_value (hq : Function.Surjective q) (a : A) :
    semanticKey q hq (q a) = key q a :=
  key_congr q (Classical.choose_spec (hq (q a)))

theorem semanticKey_injective (hq : Function.Surjective q) :
    Function.Injective (semanticKey q hq) := by
  intro x y h
  obtain ⟨a,rfl⟩ := hq x
  obtain ⟨b,rfl⟩ := hq y
  simpa only [semanticKey_value, key_eq_iff] using h

variable (heq : ComputablePred (fun p : A × A => q p.1 = q p.2))

include heq in
theorem computable_acceptsName : Computable₂ (acceptsName q) := by
  change Computable (fun p : A × ℕ =>
    (Encodable.decode (α := A) p.2).elim false (fun b => decide (q b = q p.1)))
  apply (Computable.option_casesOn (Computable.decode.comp Computable.snd)
    (Computable.const false) (heq.decide.comp
      (Computable.snd.pair (Computable.fst.comp Computable.fst))).to₂).of_eq
  intro p
  cases Encodable.decode (α := A) p.2 <;> rfl

include heq in
theorem computable_key : Computable (key q) := by
  have hb : Computable₂ (fun (a b : Bool) => decide (a=b)) := Primrec.eq.decide.to_comp
  have hc : Computable (fun p : A × ℕ => decide (acceptsName q p.1 p.2 = true)) :=
    hb.comp (computable_acceptsName q heq) (Computable.const true)
  exact Computable.find (P := fun a n => acceptsName q a n = true)
    hc.computablePred (match_exists q)

end
end SimpleFInftyOvergroups.EffectiveNames

end OAI
