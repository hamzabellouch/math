import OAI.Combinatorics.ContingencyTables.Machines.FiniteFairBits
import OAI.Combinatorics.ContingencyTables.Transport.CompletionKernelIdentification
import OAI.Combinatorics.ContingencyTables.Transport.RationalMapProducts
import Mathlib.Data.Fintype.EquivFin

namespace OAI

/-! # One Boolean word per listed proposal, with unused words giving a hold -/

namespace ContingencyTables.FairBits

open scoped BigOperators Classical
open ResidualMixture FirstSuccess

noncomputable section

variable {X : Type*} [Fintype X]

/-- A code with no preimage is an explicit hold. -/
def injectionDraw {k : ℕ} (e : X ↪ Fin (2^k)) (b : Fin (2^k)) : Option X :=
  if h : ∃ x,e x=b then some (Classical.choose h) else none

lemma injectionDraw_eq_some {k : ℕ} (e : X ↪ Fin (2^k)) (b : Fin (2^k)) (x : X) :
    injectionDraw e b=some x ↔ b=e x := by
  by_cases h : ∃ y,e y=b
  · simp only [injectionDraw,dite_eq_left h,Option.some.injEq]
    constructor
    · intro hx
      rw [←hx]
      exact (Classical.choose_spec h).symm
    · intro hx
      apply e.injective
      exact (Classical.choose_spec h).trans hx
  · have hn : b≠e x := by
      intro hx
      exact h ⟨x,hx.symm⟩
    simp only [injectionDraw,dite_eq_right h,reduceCtorEq,hn]

/-- Every listed proposal gets exactly one equally likely bit string. -/
theorem injectionDraw_mass {k : ℕ} (e : X ↪ Fin (2^k)) (x : X) :
    (mapLaw (uniformLaw (α := Fin (2^k))) (injectionDraw e)).mass (some x)=1/(2:ℚ)^k := by
  simp only [mapLaw,injectionDraw_eq_some,uniformLaw,uniformMass,Fintype.card_fin]
  simp

def proposalEmbedding (k : ℕ) (h : Fintype.card X ≤ 2^k) : X ↪ Fin (2^k) :=
  Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa using h))

def partialBitDraw (k : ℕ) (h : Fintype.card X ≤ 2^k) (bits : Fin k → Bool) : Option X :=
  injectionDraw (proposalEmbedding k h) (binaryWordEquiv k bits)

theorem partialBitDraw_mass (k : ℕ) (h : Fintype.card X ≤ 2^k) (x : X) :
    (mapLaw (uniformLaw (α := Fin k → Bool)) (partialBitDraw k h)).mass (some x)=1/(2:ℚ)^k := by
  unfold partialBitDraw
  rw [←map_equiv (binaryWordEquiv k),uniform_equiv]
  exact injectionDraw_mass _ x

variable {S : Type*} [Fintype S] [DecidableEq X]

lemma optionMap_mass_injective (p : RationalLaw (Option S)) (f : S → X)
    (hf : Function.Injective f) (s : S) :
    (mapLaw p (Option.map f)).mass (some (f s))=p.mass (some s) := by
  simp only [mapLaw,Fintype.sum_option,Option.map_none,Option.map_some,
    Option.some.injEq,reduceCtorEq,ite_false,zero_add,hf.eq_iff]
  simp

lemma optionMap_mass_outside (p : RationalLaw (Option S)) (f : S → X) (x : X)
    (hx : ∀ s,f s≠x) : (mapLaw p (Option.map f)).mass (some x)=0 := by
  simp only [mapLaw,Fintype.sum_option,Option.map_none,Option.map_some,
    Option.some.injEq,reduceCtorEq,ite_false,zero_add,hx,Finset.sum_const_zero]

def subsetBitDraw (p : X → Prop) (k : ℕ) (h : Fintype.card {x // p x} ≤ 2^k)
    (bits : Fin k → Bool) : Option X :=
  (partialBitDraw (X := {x // p x}) k h bits).map Subtype.val

/-- Distinct listed outcomes each have the advertised dyadic mass. -/
theorem subsetBitDraw_mass (p : X → Prop) (k : ℕ)
    (h : Fintype.card {x // p x} ≤ 2^k) (x : X) :
    (mapLaw (uniformLaw (α := Fin k → Bool)) (subsetBitDraw p k h)).mass (some x)=
      if p x then 1/(2:ℚ)^k else 0 := by
  let : DecidableEq {x // p x} := Classical.decEq _
  change (mapLaw (uniformLaw (α := Fin k → Bool))
    (fun bits => Option.map Subtype.val (partialBitDraw k h bits))).mass (some x)=_
  rw [←mapLaw_comp]
  by_cases hx : p x
  · rw [ite_eq_left hx]
    exact (optionMap_mass_injective _ Subtype.val Subtype.val_injective ⟨x,hx⟩).trans
      (partialBitDraw_mass k h ⟨x,hx⟩)
  · rw [ite_eq_right hx]
    exact optionMap_mass_outside _ Subtype.val x (fun s hs => hx (hs ▸ s.property))

end
end ContingencyTables.FairBits

end OAI
