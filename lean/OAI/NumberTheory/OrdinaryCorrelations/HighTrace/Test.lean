import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.IntegerResidues
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.PrivateFamily
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.CoefficientZeroOfNotSupport
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.PrefixCoefficientNondvd

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

inductive Test (j : Fin n) where
  | extra
  | tail (q : S.Index)
  | compare (i : Fin n) (q r : S.Index)
      (hr : (r:ℕ) ∈ (F.witness i).spec.primeSupport)

namespace Test
variable {F} {j : Fin n}

def selected : F.Test j → S.Index
  | .extra => (F.witness j).spec.extra
  | .tail q => q
  | .compare _ q _ _ => q

def modulus : F.Test j → S.Index
  | .extra => (F.witness j).spec.extra
  | .tail _ => (F.witness j).spec.extra
  | .compare _ _ r _ => r

noncomputable def support : F.Test j → Finset ℕ
  | .extra => (F.witness j).spec.primeSupport
  | .tail _ => (F.witness j).spec.primeSupport
  | .compare i _ _ _ => F.comparisonSupport i j

noncomputable def expression : F.Test j → ℤ
  | .extra => (F.witness j).spec.offset (Fin.last (F.witness j).spec.length)-
      (F.witness j).spec.offset (F.witness j).spec.suffix.castSucc
  | .tail _ => (F.witness j).spec.offset (Fin.last (F.witness j).spec.length)-
      (F.witness j).spec.offset (F.witness j).spec.suffix.castSucc
  | .compare i _ r hi => (F.witness j).vertex-(F.witness i).vertex+
      (F.witness j).spec.offset (F.witness j).spec.tailStart.castSucc-
      (F.witness i).spec.offset ((F.witness i).spec.activity r hi)

noncomputable def coefficient : F.Test j → ℤ
  | .extra => 0
  | .tail q => (F.witness j).spec.coefficient q (F.witness j).spec.suffix.val
      (F.witness j).spec.length
  | .compare i q r hi =>
      w.segmentCoefficient q (F.witness i).index (F.witness j).index+
      (F.witness j).spec.coefficient q 0 (F.witness j).spec.tailStart.val-
      (F.witness i).spec.coefficient q 0 ((F.witness i).spec.activity r hi).val

def Valid : F.Test j → Prop
  | .extra => True
  | .tail q => (q:ℕ) ∣ (F.witness j).spec.label (F.witness j).spec.tailStart ∧
      ∀ e : Fin (F.witness j).spec.length, e < (F.witness j).spec.tailStart →
        ¬(q:ℕ) ∣ (F.witness j).spec.label e
  | .compare i q r _ =>
      (r:ℕ) ∣ (F.witness j).spec.label (F.witness j).spec.tailStart ∧
      (∀ e : Fin (F.witness j).spec.length, e < (F.witness j).spec.tailStart →
        ¬(r:ℕ) ∣ (F.witness j).spec.label e) ∧
      (∃ e : Fin (F.witness j).spec.length, e < (F.witness j).spec.tailStart ∧
        (q:ℕ) ∣ (F.witness j).spec.label e) ∧
      (q:ℕ) ∉ (F.witness i).spec.primeSupport ∧
      (q:ℕ) ∉ w.segmentSupport (F.witness i).index (F.witness j).index

def Linear : F.Test j → Prop
  | .extra => False
  | .tail _ => True
  | .compare _ _ _ _ => True

lemma selected_mem (t : F.Test j) (ht : t.Valid) : (t.selected:ℕ) ∈ t.support := by
  cases t with
  | extra => exact ((F.witness j).spec.support_iff_extra_or_label _).mpr (Or.inl rfl)
  | tail q =>
      exact ((F.witness j).spec.support_iff_extra_or_label q).mpr
        (Or.inr ⟨(F.witness j).spec.tailStart,ht.1⟩)
  | compare i q r hi =>
      obtain ⟨e,he,hqe⟩ := ht.2.2.1
      exact mem_union_left _ (mem_union_right _
        (((F.witness j).spec.support_iff_extra_or_label q).mpr (Or.inr ⟨e,hqe⟩)))

lemma comparison_coefficient (i : Fin n) (q r : S.Index)
    (hi : (r:ℕ) ∈ (F.witness i).spec.primeSupport)
    (ht : (Test.compare (F:=F) (j:=j) i q r hi).Valid) :
    (Test.compare (F:=F) (j:=j) i q r hi).coefficient =
      (F.witness j).spec.coefficient q 0 (F.witness j).spec.tailStart.val := by
  change w.segmentCoefficient q (F.witness i).index (F.witness j).index+
      (F.witness j).spec.coefficient q 0 (F.witness j).spec.tailStart.val-
      (F.witness i).spec.coefficient q 0 ((F.witness i).spec.activity r hi).val = _
  rw [w.segmentCoefficient_zero q (S.prime_mem q q.property) _ _ ht.2.2.2.2,
    (F.witness i).spec.coefficient_zero_of_not_support q ht.2.2.2.1]
  ring

lemma holds (t : F.Test j) (ht : t.Valid) (x : ℤ)
    (hx : ∀ i, (F.witness i).spec.QualifiesAt (x+(F.witness i).vertex)) :
    ((t.modulus:ℕ):ℤ) ∣ t.expression := by
  cases t with
  | extra => exact (F.witness j).spec.extra_div_suffix
  | tail q => exact (F.witness j).spec.extra_div_suffix
  | compare i q r hi =>
      exact attached_activity_comparison w (F.witness i) (F.witness j) r hi ht.1 x (hx i) (hx j)

lemma nondegenerate (t : F.Test j) (ht : t.Valid) (hh : 0 < h)
    (hpp : h < ((F.witness j).spec.extra:ℕ))
    (hpL : L < ((F.witness j).spec.extra:ℕ)) :
    if t.Linear then ¬((t.modulus:ℕ):ℤ) ∣ t.coefficient else t.expression ≠ 0 := by
  cases t with
  | extra =>
      simp only [Linear,ite_false,expression,ne_eq,sub_eq_zero]
      intro he
      have hi := (F.witness j).spec.offsets_distinct he
      have hv := congrArg Fin.val hi
      have hs := (F.witness j).spec.suffix.isLt
      simp only [Fin.val_last,Fin.val_castSucc] at hv
      omega
  | tail q =>
      rw [ite_eq_left (show (Test.tail (F:=F) (j:=j) q).Linear from trivial)]
      exact (F.witness j).spec.suffix_coefficient_nondvd hh hpp hpL q ht.1 ht.2
  | compare i q r hi =>
      rw [ite_eq_left (show (Test.compare (F:=F) (j:=j) i q r hi).Linear from trivial)]
      change ¬((r:ℕ):ℤ) ∣ _
      rw [comparison_coefficient i q r hi ht]
      exact (F.witness j).spec.prefix_coefficient_nondvd (F.witness j).primitive q r
        ht.1 ht.2.1 ht.2.2.1

lemma modulus_ne_selected (t : F.Test j) (ht : t.Valid) (hl : t.Linear) :
    t.modulus ≠ t.selected := by
  cases t with
  | extra => exact hl.elim
  | tail q =>
      intro he
      change (F.witness j).spec.extra=q at he
      apply (F.witness j).spec.extra_not_div (F.witness j).spec.tailStart
      rw [he]
      exact ht.1
  | compare i q r hi =>
      intro he
      obtain ⟨e,he',hqe⟩ := ht.2.2.1
      change r=q at he
      apply ht.2.1 e he'
      rw [he]
      exact hqe

end Test
end PrivateFamily
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
