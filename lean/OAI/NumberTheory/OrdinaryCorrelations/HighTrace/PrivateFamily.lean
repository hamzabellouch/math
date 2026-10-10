import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SupportIffExtraOrLabel
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ExistsNewPrime

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h L ℓ n : ℕ}

structure PrivateFamily (w : ClosedLine h ℓ) (D : S.DivisorFamily B τ C₀) (L n : ℕ) where
  witness : Fin n → AttachedSpec w D L
  key : Fin n → S.Index
  key_mem : ∀ j, (key j:ℕ) ∈ (witness j).spec.primeSupport
  key_free : ∀ j, ¬S.IsFixed w (key j)
  key_private : ∀ i j, i≠j → (key i:ℕ) ∉ (witness j).spec.primeSupport
  ordered : Monotone (fun j => (witness j).index)

namespace PrivateFamily
variable {w : ClosedLine h ℓ} (F : PrivateFamily w D L n)

lemma key_injective : Function.Injective F.key := by
  intro i j he
  by_contra hn
  exact F.key_private i j hn (he ▸ F.key_mem j)

def Intrinsic (j : Fin n) : Prop :=
  F.key j=(F.witness j).spec.extra ∨
    ((F.key j:ℕ) ∣ (F.witness j).spec.label (F.witness j).spec.tailStart ∧
    ∀ i : Fin (F.witness j).spec.length, i < (F.witness j).spec.tailStart →
      ¬(F.key j:ℕ) ∣ (F.witness j).spec.label i)

def PreTail (j : Fin n) : Prop :=
  ∃ i : Fin (F.witness j).spec.length, i < (F.witness j).spec.tailStart ∧
    (F.key j:ℕ) ∣ (F.witness j).spec.label i

def FirstTail (r : Fin n → S.Index) (j : Fin n) : Prop :=
  ∀ i : Fin n, i < j → (r j:ℕ) ∉ (F.witness i).spec.primeSupport

def LastTail (r : Fin n → S.Index) (j : Fin n) : Prop :=
  ∀ i : Fin n, j < i → (r j:ℕ) ∉ (F.witness i).spec.primeSupport

def BeforeLine (j : Fin n) : Prop :=
  ∀ i : Fin ℓ, i.val < (F.witness j).index.val → ¬(F.key j:ℕ) ∣ w.label i

def AfterLine (j : Fin n) : Prop :=
  ∀ i : Fin ℓ, (F.witness j).index.val ≤ i.val → ¬(F.key j:ℕ) ∣ w.label i

inductive Case where
  | intrinsic | first | last | before | after
  deriving DecidableEq

instance : Fintype Case :=
  ⟨{.intrinsic,.first,.last,.before,.after},by intro c; cases c <;> simp⟩

instance : Nonempty Case := ⟨.intrinsic⟩

lemma case_card : Fintype.card Case = 5 := by decide

def CaseHolds (r : Fin n → S.Index) (c : Case) (j : Fin n) : Prop :=
  match c with
  | .intrinsic => F.Intrinsic j
  | .first => F.FirstTail r j
  | .last => F.LastTail r j
  | .before => F.PreTail j ∧ (∃ i : Fin n, i < j ∧ (r j:ℕ) ∈ (F.witness i).spec.primeSupport) ∧
      F.BeforeLine j
  | .after => F.PreTail j ∧ (∃ i : Fin n, j < i ∧ (r j:ℕ) ∈ (F.witness i).spec.primeSupport) ∧
      F.AfterLine j

lemma exists_case (r : Fin n → S.Index) (j : Fin n) : ∃ c, F.CaseHolds r c j := by
  by_cases hi : F.Intrinsic j
  · exact ⟨.intrinsic,hi⟩
  by_cases hf : F.FirstTail r j
  · exact ⟨.first,hf⟩
  by_cases hl : F.LastTail r j
  · exact ⟨.last,hl⟩
  have hp : F.PreTail j := by
    rcases (F.witness j).spec.occurs_before_or_tail (F.key j) (F.key_mem j) with he|hp|ht
    · exact (hi (Or.inl he)).elim
    · exact hp
    · exact (hi (Or.inr ht)).elim
  have hef : ∃ i : Fin n, i < j ∧ (r j:ℕ) ∈ (F.witness i).spec.primeSupport := by
    by_contra hn
    apply hf
    intro i hi hm
    exact hn ⟨i,hi,hm⟩
  have hel : ∃ i : Fin n, j < i ∧ (r j:ℕ) ∈ (F.witness i).spec.primeSupport := by
    by_contra hn
    apply hl
    intro i hi hm
    exact hn ⟨i,hi,hm⟩
  rcases free_prime_one_side w (F.key j) (F.key_free j) (F.witness j).index with hb|ha
  · exact ⟨.before,hp,hef,hb⟩
  · exact ⟨.after,hp,hel,ha⟩

theorem large_case (r : Fin n → S.Index) :
    ∃ (c : Case) (A : Finset (Fin n)), n/5 ≤ A.card ∧ ∀ j ∈ A, F.CaseHolds r c j := by
  let classify : Fin n → Case := fun j => Classical.choose (F.exists_case r j)
  have hm : Fintype.card Case*(n/5) ≤ Fintype.card (Fin n) := by
    rw [case_card,Fintype.card_fin]
    exact Nat.mul_div_le _ _
  obtain ⟨c,hc⟩ := Fintype.exists_le_card_fiber_of_mul_le_card (f:=classify) hm
  refine ⟨c,univ.filter (fun j => classify j=c),hc,?_⟩
  intro j hj
  have he := (mem_filter.mp hj).2
  rw [←he]
  exact Classical.choose_spec (F.exists_case r j)

theorem exists_tails (hh : 0 < h) (hτ : τ < 2)
    (hpp : ∀ j, h < ((F.witness j).spec.extra:ℕ))
    (hpL : ∀ j, L < ((F.witness j).spec.extra:ℕ)) :
    ∃ r : Fin n → S.Index, ∀ j,
      (r j:ℕ) ∣ (F.witness j).spec.label (F.witness j).spec.tailStart ∧
      (∀ i : Fin (F.witness j).spec.length, i < (F.witness j).spec.tailStart →
        ¬(r j:ℕ) ∣ (F.witness j).spec.label i) := by
  have hex (j : Fin n) := (F.witness j).spec.exists_tail_prime (F.witness j).primitive hh hτ
    (hpp j) (hpL j)
  exact ⟨fun j => Classical.choose (hex j),fun j => Classical.choose_spec (hex j)⟩

end PrivateFamily
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
