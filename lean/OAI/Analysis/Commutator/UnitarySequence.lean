import Mathlib
import OAI.Analysis.Commutator.TracialDoubleCompression
import OAI.Analysis.Commutator.PartialUnitaryHom

namespace OAI

open Lean in
run_cmd modifyEnv fun env =>
  let env := Lean.LibrarySuggestions.nameDenyListExt.addEntry env "trace_sequence_power"
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "trace_sequence_word"

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder Topology BoundedContinuousFunction

open Filter

namespace Kadison.TracialSequence

open FinitePatching FinitePatching.Words

variable {A : Type} [CStarAlgebra A]

local instance unitarySequenceOrder : PartialOrder (ℕ →ᵇ A) := CStarAlgebra.spectralOrder _

local instance unitarySequenceStarOrderedRing : StarOrderedRing (ℕ →ᵇ A) :=
  CStarAlgebra.spectralOrderedRing _

def boundedUnitary (u : ℕ → unitary A) : unitary (ℕ →ᵇ A) :=
  ⟨BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun n => (u n:A)) 1
    (fun n => (PartialUnitary.ofUnitary (u n)).norm_le_one),by
    constructor <;> ext n
    · exact (u n).property.1
    · exact (u n).property.2⟩

@[simp] lemma boundedUnitary_apply (u : ℕ → unitary A) (n : ℕ) :
    ((boundedUnitary u : ℕ →ᵇ A) n)=(u n:A) := rfl

def evalSequence (n : ℕ) : (ℕ →ᵇ A) →⋆ₐ[ℂ] A where
  toFun a := a n
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

lemma eval_partialUnitary (u : ℕ → unitary A) (n : ℕ) :
    (PartialUnitary.ofUnitary (boundedUnitary u)).map (evalSequence n)=
      PartialUnitary.ofUnitary (u n) := PartialUnitary.ext rfl

lemma eval_power (u : ℕ → unitary A) (k : ℤ) (n : ℕ) :
    ((PartialUnitary.ofUnitary (boundedUnitary u)).power k) n=
      (PartialUnitary.ofUnitary (u n)).power k := by
  change evalSequence n _=_
  rw [PartialUnitary.map_power,eval_partialUnitary]

lemma eval_word {J K : Type*} (u : ℕ → unitary A) (x : J → A) (k : K → ℤ)
    (l : List (Letter J K)) (n : ℕ) :
    (word (constantSequence ∘ x) k (PartialUnitary.ofUnitary (boundedUnitary u)) l) n=
      word x k (PartialUnitary.ofUnitary (u n)) l := by
  change evalSequence n _=_
  rw [map_word,eval_partialUnitary]
  rfl

def sequenceUnitary {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ) (u : ℕ → unitary A) :
    unitary (boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω) :=
  ⟨leftRestricted τ ω (boundedUnitary u),Unitary.map_mem (leftRestricted τ ω) (boundedUnitary u).property⟩

private lemma sequence_partial_map {A : Type} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
    (u : ℕ → unitary A) :
    PartialUnitary.map (B := boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)
      (by exact leftRestricted τ ω) (PartialUnitary.ofUnitary (boundedUnitary u)) =
      PartialUnitary.ofUnitary (by exact sequenceUnitary τ ω u) := by
  apply PartialUnitary.ext
  rfl

private lemma trace_left_zero_of_tendsto {A : Type} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ atTop) (a : ℕ →ᵇ A)
    (hlim : Tendsto (fun n => τ (a n)) atTop (𝓝 0)) :
    sequenceTrace τ ω (leftRestricted τ ω a) = 0 :=
  tendsto_nhds_unique (tendsto_trace τ ω a) (hlim.mono_left hω)

private lemma sequence_power_map {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ) (u : ℕ → unitary A) (k : ℤ) :
    leftRestricted τ ω ((PartialUnitary.ofUnitary (boundedUnitary u)).power k) =
      (PartialUnitary.ofUnitary (by exact sequenceUnitary τ ω u)).power k := by
  cases k with
  | ofNat n =>
    cases n with
    | zero => exact map_one (leftRestricted τ ω)
    | succ n =>
      change leftRestricted τ ω ((boundedUnitary u : ℕ →ᵇ A) ^ (n + 1)) =
        (leftRestricted τ ω (boundedUnitary u)) ^ (n + 1)
      exact map_pow (leftRestricted τ ω) (boundedUnitary u : ℕ →ᵇ A) (n + 1)
  | negSucc n =>
    change leftRestricted τ ω (star (boundedUnitary u : ℕ →ᵇ A) ^ (n + 1)) =
      (star (leftRestricted τ ω (boundedUnitary u))) ^ (n + 1)
    exact (map_pow (leftRestricted τ ω) (star (boundedUnitary u : ℕ →ᵇ A)) (n + 1)).trans
      (congrArg (fun a : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω => a ^ (n + 1))
        (map_star (leftRestricted τ ω) (boundedUnitary u : ℕ →ᵇ A)))

private lemma sequence_word_map {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ) (u : ℕ → unitary A)
    {J K : Type*} (x : J → A) (k : K → ℤ) (l : List (Letter J K)) :
    leftRestricted τ ω (word (constantSequence ∘ x) k (PartialUnitary.ofUnitary (boundedUnitary u)) l) =
      word (((leftRestricted τ ω).comp constantSequence) ∘ x) k
        (PartialUnitary.ofUnitary (by exact sequenceUnitary τ ω u)) l := by
  have hs (s : Slot K) :
      leftRestricted τ ω (slotPower k (PartialUnitary.ofUnitary (boundedUnitary u)) s) =
        slotPower k (PartialUnitary.ofUnitary (by exact sequenceUnitary τ ω u)) s := by
    cases s with
    | none => exact map_one (leftRestricted τ ω)
    | some s =>
      cases s with
      | none => exact map_one (leftRestricted τ ω)
      | some i => exact sequence_power_map τ ω u (k i)
  have hl (i : Letter J K) :
      leftRestricted τ ω (letter (constantSequence ∘ x) k
        (PartialUnitary.ofUnitary (boundedUnitary u)) i) =
      letter (((leftRestricted τ ω).comp constantSequence) ∘ x) k
        (PartialUnitary.ofUnitary (by exact sequenceUnitary τ ω u)) i := by
    exact (map_mul (leftRestricted τ ω) (constantSequence (x i.1))
      (slotPower k (PartialUnitary.ofUnitary (boundedUnitary u)) i.2)).trans
      (congrArg (fun a : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω =>
        leftRestricted τ ω (constantSequence (x i.1)) * a) (hs i.2))
  induction l with
  | nil => exact map_one (leftRestricted τ ω)
  | cons i l ih =>
    exact (map_mul (leftRestricted τ ω)
      (letter (constantSequence ∘ x) k (PartialUnitary.ofUnitary (boundedUnitary u)) i)
      (word (constantSequence ∘ x) k (PartialUnitary.ofUnitary (boundedUnitary u)) l)).trans
      (congrArg₂ (fun a b : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω => a * b)
        (hl i) ih)

lemma trace_sequence_power {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ)≤atTop) (u : ℕ → unitary A) (k : ℤ)
    (hlim : Tendsto (fun n => τ ((PartialUnitary.ofUnitary (u n)).power k)) atTop (𝓝 0)) :
    sequenceTrace τ ω ((PartialUnitary.ofUnitary
      (by exact sequenceUnitary τ ω u)).power k)=0 := by
  have hz := trace_left_zero_of_tendsto τ ω hω
    ((PartialUnitary.ofUnitary (boundedUnitary u)).power k)
    (Filter.Tendsto.congr (fun n => congrArg τ (eval_power u k n).symm) hlim)
  have he := sequence_power_map τ ω u k
  exact (congrArg (fun T : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω =>
    sequenceTrace τ ω T) he).symm.trans hz

lemma trace_sequence_word {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
    {J K : Type*} (hω : (ω : Filter ℕ)≤atTop) (u : ℕ → unitary A)
    (x : J → A) (k : K → ℤ) (l : List (Letter J K))
    (hlim : Tendsto (fun n => τ (word x k (PartialUnitary.ofUnitary (u n)) l)) atTop (𝓝 0)) :
    sequenceTrace τ ω (word (((leftRestricted τ ω).comp constantSequence) ∘ x) k
      (PartialUnitary.ofUnitary
        (by exact sequenceUnitary τ ω u)) l)=0 := by
  have hz := trace_left_zero_of_tendsto τ ω hω
    (word (constantSequence ∘ x) k (PartialUnitary.ofUnitary (boundedUnitary u)) l)
    (Filter.Tendsto.congr (fun n => congrArg τ (eval_word u x k l n).symm) hlim)
  have he := sequence_word_map τ ω u x k l
  exact (congrArg (fun T : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω =>
    sequenceTrace τ ω T) he).symm.trans hz

end Kadison.TracialSequence

end

end OAI
