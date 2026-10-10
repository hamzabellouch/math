import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SmoothBlock

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace OrdinarySmoothRough
open Finset OrdinarySelbergWeights

def cutRectangle (S : Finset ℕ) (N A B V : ℕ) : Finset ℕ :=
  (smoothBlock S A B ×ˢ roughBlock S (N/A) V).image (fun ab => ab.1*ab.2)

lemma cutRectangle_subset (S : Finset ℕ) (N A B V : ℕ) (hV : V≤2*N/B) :
    cutRectangle S N A B V ⊆ hyperbolaRectangle S N A B := by
  apply image_subset_image
  apply product_subset_product subset_rfl
  apply filter_subset_filter
  exact Ioc_subset_Ioc_right hV

theorem slice_defect_card_cut (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    (N A B V : ℕ) (hA : 0<A) (hAB : A≤B) :
    ((smoothSlice S N A B) \ (cutRectangle S N A B V)).card ≤
      (B-A) * ((roughBlock S (N/B) (N/A)).card +
        (roughBlock S V (2*N/A)).card) := by
  let R := roughBlock S (N/B) (N/A) ∪ roughBlock S V (2*N/A)
  have hmap : Set.MapsTo (fun n => (smoothPart S n,roughPart S n))
      (↑((smoothSlice S N A B) \ cutRectangle S N A B V))
      (↑(smoothBlock S A B ×ˢ R)) := by
    intro n hn
    obtain ⟨hnsl,hnrec⟩ := mem_sdiff.mp hn
    obtain ⟨hnI,ha⟩ := mem_filter.mp hnsl
    obtain ⟨hNn,hnN⟩ := mem_Ioc.mp hnI
    have hn0 : 0<n := lt_of_le_of_lt (Nat.zero_le _) hNn
    have hp := parts_mul S hn0.ne'
    have ham : smoothPart S n ∈ smoothBlock S A B :=
      mem_filter.mpr ⟨mem_Ioc.mpr ha,smoothPart_mem S n⟩
    have hcop := roughPart_coprime_product S n hS
    have hbL : N/B < roughPart S n := by
      apply (Nat.div_lt_iff_lt_mul (hA.trans_le hAB)).mpr
      nlinarith
    have hbU : roughPart S n ≤ 2*N/A := by
      apply (Nat.le_div_iff_mul_le hA).mpr
      nlinarith
    have hout : roughPart S n ∉ roughBlock S (N/A) V := by
      intro hmem
      apply hnrec
      exact mem_image.mpr ⟨(smoothPart S n,roughPart S n),mem_product.mpr ⟨ham,hmem⟩,hp⟩
    have hor : roughPart S n ≤ N/A ∨ V < roughPart S n := by
      by_contra h
      push Not at h
      exact hout (mem_filter.mpr ⟨mem_Ioc.mpr ⟨h.1,h.2⟩,hcop⟩)
    apply mem_product.mpr
    refine ⟨ham,?_⟩
    rcases hor with hl | hu
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_Ioc.mpr ⟨hbL,hl⟩,hcop⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_Ioc.mpr ⟨hu,hbU⟩,hcop⟩)
  have hinj : Set.InjOn (fun n => (smoothPart S n,roughPart S n))
      (↑((smoothSlice S N A B) \ cutRectangle S N A B V)) := by
    intro n hn m hm he
    have hn0 : n≠0 := ne_of_gt (lt_of_le_of_lt (Nat.zero_le N)
      (mem_Ioc.mp (mem_filter.mp (Finset.mem_sdiff.mp hn).1).1).1)
    have hm0 : m≠0 := ne_of_gt (lt_of_le_of_lt (Nat.zero_le N)
      (mem_Ioc.mp (mem_filter.mp (Finset.mem_sdiff.mp hm).1).1).1)
    rw [← parts_mul S hn0, ← parts_mul S hm0]
    exact congrArg (fun ab : ℕ×ℕ => ab.1*ab.2) he
  calc
    _ ≤ (smoothBlock S A B ×ˢ R).card := card_le_card_of_injOn _ hmap hinj
    _ = (smoothBlock S A B).card * R.card := card_product _ _
    _ ≤ (B-A) * ((roughBlock S (N/B) (N/A)).card +
        (roughBlock S V (2*N/A)).card) := by
      apply Nat.mul_le_mul
      · exact (card_filter_le _ _).trans_eq (Nat.card_Ioc A B)
      · exact card_union_le _ _

end OrdinarySmoothRough

end

end OAI
