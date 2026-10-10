import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.IntegerResidues
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.PrivateFamily
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Test

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
namespace PrivateFamily
variable {w : ClosedLine h ℓ} (F : PrivateFamily w D L n)

def Case.Precedes (c : Case) (i j : Fin n) : Prop :=
  match c with
  | .intrinsic | .first | .before => i < j
  | .last | .after => j < i

def Case.variable (c : Case) (r : Fin n → S.Index) (j : Fin n) : S.Index :=
  match c with
  | .first | .last => r j
  | .intrinsic | .before | .after => F.key j

noncomputable def caseTest (r : Fin n → S.Index) (c : Case) (j : Fin n)
    (hj : F.CaseHolds r c j) : F.Test j := by
  cases c with
  | intrinsic =>
      exact if he : F.key j=(F.witness j).spec.extra then .extra else .tail (F.key j)
  | first => exact .tail (r j)
  | last => exact .tail (r j)
  | before =>
      exact .compare (Classical.choose hj.2.1) (F.key j) (r j) (Classical.choose_spec hj.2.1).2
  | after =>
      exact .compare (Classical.choose hj.2.1) (F.key j) (r j) (Classical.choose_spec hj.2.1).2

lemma caseTest_selected (r : Fin n → S.Index) (c : Case) (j : Fin n)
    (hj : F.CaseHolds r c j) : (F.caseTest r c j hj).selected = c.variable F r j := by
  cases c <;> simp only [caseTest,Case.variable,Test.selected]
  split_ifs with he
  · exact he.symm
  · rfl

lemma caseTest_valid (r : Fin n → S.Index)
    (hrt : ∀ j, (r j:ℕ) ∣ (F.witness j).spec.label (F.witness j).spec.tailStart)
    (hrfree : ∀ j, ∀ e : Fin (F.witness j).spec.length, e < (F.witness j).spec.tailStart →
      ¬(r j:ℕ) ∣ (F.witness j).spec.label e)
    (c : Case) (j : Fin n) (hj : F.CaseHolds r c j) : (F.caseTest r c j hj).Valid := by
  cases c with
  | intrinsic =>
      simp only [caseTest]
      split_ifs with he
      · trivial
      · exact hj.resolve_left he
  | first => exact ⟨hrt j,hrfree j⟩
  | last => exact ⟨hrt j,hrfree j⟩
  | before =>
      let i := Classical.choose hj.2.1
      have hi := Classical.choose_spec hj.2.1
      exact ⟨hrt j,hrfree j,hj.1,F.key_private j i (ne_of_gt hi.1),
        F.own_segment_absent_before i j hi.1 hj.2.2⟩
  | after =>
      let i := Classical.choose hj.2.1
      have hi := Classical.choose_spec hj.2.1
      exact ⟨hrt j,hrfree j,hj.1,F.key_private j i (ne_of_lt hi.1),
        F.own_segment_absent_after i j hi.1 hj.2.2⟩

lemma caseTest_future_absent (r : Fin n → S.Index) (c : Case) (i j : Fin n)
    (hi : F.CaseHolds r c i) (hj : F.CaseHolds r c j) (hij : c.Precedes i j) :
    (c.variable F r j:ℕ) ∉ (F.caseTest r c i hi).support := by
  cases c with
  | intrinsic =>
      simp only [Case.variable,caseTest]
      split_ifs <;> exact F.key_private j i (ne_of_gt hij)
  | first => exact hj i hij
  | last => exact hj i hij
  | before =>
      exact F.future_absent_before (Classical.choose hi.2.1) i j
        (Classical.choose_spec hi.2.1).1 hij hj.2.2
  | after =>
      exact F.future_absent_after (Classical.choose hi.2.1) i j
        (Classical.choose_spec hi.2.1).1 hij hj.2.2

lemma variable_injective_on_case (r : Fin n → S.Index)
    (hrt : ∀ j, (r j:ℕ) ∣ (F.witness j).spec.label (F.witness j).spec.tailStart)
    (c : Case) (A : Finset (Fin n)) (hA : ∀ j ∈ A, F.CaseHolds r c j) :
    Set.InjOn (c.variable F r) (A : Set (Fin n)) := by
  intro i hi j hj he
  cases c with
  | intrinsic => exact F.key_injective he
  | before => exact F.key_injective he
  | after => exact F.key_injective he
  | first =>
      change r i=r j at he
      rcases lt_trichotomy i j with hij|rfl|hji
      · exact ((hA j hj) i hij (by rw [←he]; exact (F.witness i).spec.tail_support (r i) (hrt i))).elim
      · rfl
      · exact ((hA i hi) j hji (by rw [he]; exact (F.witness j).spec.tail_support (r j) (hrt j))).elim
  | last =>
      change r i=r j at he
      rcases lt_trichotomy i j with hij|rfl|hji
      · exact ((hA i hi) j hij (by rw [he]; exact (F.witness j).spec.tail_support (r j) (hrt j))).elim
      · rfl
      · exact ((hA j hj) i hji (by rw [←he]; exact (F.witness i).spec.tail_support (r i) (hrt i))).elim

theorem triangular_tests (hh : 0 < h) (hτ : τ < 2)
    (hpp : ∀ j, h < ((F.witness j).spec.extra:ℕ))
    (hpL : ∀ j, L < ((F.witness j).spec.extra:ℕ)) :
    ∃ (c : Case) (A : Finset (Fin n)) (t : ∀ j : A, F.Test j.val),
      n/5 ≤ A.card ∧
      (∀ j, (t j).Valid) ∧
      Function.Injective (fun j : A => (t j).selected) ∧
      (∀ i j : A, c.Precedes i.val j.val → ((t j).selected:ℕ) ∉ (t i).support) ∧
      (∀ j, if (t j).Linear then ¬(((t j).modulus:ℕ):ℤ) ∣ (t j).coefficient
        else (t j).expression ≠ 0) ∧
      (∀ (x : ℤ), (∀ i, (F.witness i).spec.QualifiesAt (x+(F.witness i).vertex)) →
        ∀ j, (((t j).modulus:ℕ):ℤ) ∣ (t j).expression) := by
  obtain ⟨r,hr⟩ := F.exists_tails hh hτ hpp hpL
  obtain ⟨c,A,hcard,hA⟩ := F.large_case r
  let t : ∀ j : A, F.Test j.val := fun j => F.caseTest r c j.val (hA j.val j.property)
  have ht (j : A) : (t j).Valid := F.caseTest_valid r (fun j => (hr j).1)
    (fun j => (hr j).2) c j.val (hA j.val j.property)
  refine ⟨c,A,t,hcard,ht,?_,?_,?_,?_⟩
  · intro i j he
    apply Subtype.ext
    apply F.variable_injective_on_case r (fun j => (hr j).1) c A hA i.property j.property
    exact (F.caseTest_selected r c i.val (hA i.val i.property)).symm.trans
      (he.trans (F.caseTest_selected r c j.val (hA j.val j.property)))
  · intro i j hij
    have hm := F.caseTest_future_absent r c i.val j.val (hA i.val i.property)
      (hA j.val j.property) hij
    simpa only [t,F.caseTest_selected] using hm
  · intro j
    exact (t j).nondegenerate (ht j) hh (hpp j.val) (hpL j.val)
  · intro x hx j
    exact (t j).holds (ht j) x hx

end PrivateFamily
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
