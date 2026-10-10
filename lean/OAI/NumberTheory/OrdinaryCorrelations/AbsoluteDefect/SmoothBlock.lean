import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SmoothPart
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.IntervalDivisorCard

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

def smoothBlock (S : Finset ℕ) (A B : ℕ) : Finset ℕ :=
  (Finset.Ioc A B).filter (fun a => a ∈ Nat.factoredNumbers S)

def roughBlock (S : Finset ℕ) (L U : ℕ) : Finset ℕ :=
  (Finset.Ioc L U).filter (fun b => b.Coprime (∏ p ∈ S, p))

def hyperbolaRectangle (S : Finset ℕ) (N A B : ℕ) : Finset ℕ :=
  (smoothBlock S A B ×ˢ roughBlock S (N/A) (2*N/B)).image (fun ab => ab.1*ab.2)

def smoothSlice (S : Finset ℕ) (N A B : ℕ) : Finset ℕ :=
  (Finset.Ioc N (2*N)).filter (fun n => A < smoothPart S n ∧ smoothPart S n ≤ B)

lemma rough_of_coprime_product (S : Finset ℕ) {b : ℕ}
    (hb : b.Coprime (∏ p ∈ S, p)) : ∀ p ∈ S, Nat.Prime p → ¬p∣b := by
  intro p hp hprime hpb
  have hpp : p ∣ ∏ p ∈ S, p := dvd_prod_of_mem (fun p : ℕ => p) hp
  exact hprime.not_dvd_one ((Nat.dvd_gcd hpb hpp).trans (by rw [hb.gcd_eq_one]))

lemma rectangle_subset_slice (S : Finset ℕ) (N A B : ℕ) (hA : 0<A) :
    hyperbolaRectangle S N A B ⊆ smoothSlice S N A B := by
  intro n hn
  obtain ⟨⟨a,b⟩,hab,rfl⟩ := mem_image.mp hn
  obtain ⟨ha,hb⟩ := mem_product.mp hab
  obtain ⟨haI,has⟩ := mem_filter.mp ha
  obtain ⟨hbI,hbr⟩ := mem_filter.mp hb
  obtain ⟨hAa,haB⟩ := mem_Ioc.mp haI
  obtain ⟨hNb,hbN⟩ := mem_Ioc.mp hbI
  have ha0 : 0<a := hA.trans hAa
  have hb0 : 0<b := lt_of_le_of_lt (Nat.zero_le _) hNb
  have hn0 : 0<a*b := Nat.mul_pos ha0 hb0
  have hl : N<a*b := by
    have hh := (Nat.div_lt_iff_lt_mul hA).mp hNb
    nlinarith
  have hu : a*b≤2*N := by
    have hh := (Nat.le_div_iff_mul_le (hA.trans_le (hAa.le.trans haB))).mp hbN
    nlinarith
  have he : smoothPart S (a*b) = a := factorization_unique
    (smoothPart_mem S _) has
    (fun p hp hprime => hprime.coprime_iff_not_dvd.mp
      (roughPart_coprime_prime S _ hprime hp).symm)
    (rough_of_coprime_product S hbr) (parts_mul S hn0.ne')
  exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hl,hu⟩,by simpa only [he] using And.intro hAa haB⟩

theorem slice_defect_card (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    (N A B : ℕ) (hA : 0<A) (hAB : A≤B) :
    ((smoothSlice S N A B) \ (hyperbolaRectangle S N A B)).card ≤
      (B-A) * ((roughBlock S (N/B) (N/A)).card +
        (roughBlock S (2*N/B) (2*N/A)).card) := by
  let R := roughBlock S (N/B) (N/A) ∪ roughBlock S (2*N/B) (2*N/A)
  have hmap : Set.MapsTo (fun n => (smoothPart S n,roughPart S n))
      (↑((smoothSlice S N A B) \ hyperbolaRectangle S N A B))
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
    have hout : roughPart S n ∉ roughBlock S (N/A) (2*N/B) := by
      intro hmem
      apply hnrec
      exact mem_image.mpr ⟨(smoothPart S n,roughPart S n),mem_product.mpr ⟨ham,hmem⟩,hp⟩
    have hor : roughPart S n ≤ N/A ∨ 2*N/B < roughPart S n := by
      by_contra h
      push Not at h
      exact hout (mem_filter.mpr ⟨mem_Ioc.mpr ⟨h.1,h.2⟩,hcop⟩)
    apply mem_product.mpr
    refine ⟨ham,?_⟩
    rcases hor with hl | hu
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_Ioc.mpr ⟨hbL,hl⟩,hcop⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_Ioc.mpr ⟨hu,hbU⟩,hcop⟩)
  have hinj : Set.InjOn (fun n => (smoothPart S n,roughPart S n))
      (↑((smoothSlice S N A B) \ hyperbolaRectangle S N A B)) := by
    intro n hn m hm he
    have hn0 : n≠0 := ne_of_gt (lt_of_le_of_lt (Nat.zero_le N)
      (Finset.mem_Ioc.mp (mem_filter.mp (mem_sdiff.mp hn).1).1).1)
    have hm0 : m≠0 := ne_of_gt (lt_of_le_of_lt (Nat.zero_le N)
      (Finset.mem_Ioc.mp (mem_filter.mp (mem_sdiff.mp hm).1).1).1)
    rw [← parts_mul S hn0, ← parts_mul S hm0]
    exact congrArg (fun ab : ℕ×ℕ => ab.1*ab.2) he
  calc
    _ ≤ (smoothBlock S A B ×ˢ R).card := card_le_card_of_injOn _ hmap hinj
    _ = (smoothBlock S A B).card * R.card := card_product _ _
    _ ≤ (B-A) * ((roughBlock S (N/B) (N/A)).card +
        (roughBlock S (2*N/B) (2*N/A)).card) := by
      apply Nat.mul_le_mul
      · exact (card_filter_le _ _).trans_eq (Nat.card_Ioc A B)
      · exact card_union_le _ _

theorem slice_defect_sieve (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    (N A B z : ℕ) (hA : 0<A) (hAB : A≤B) (hz : 1≤z)
    (hprime : Squarefree (∏ p ∈ S, p)) :
    (((smoothSlice S N A B) \ (hyperbolaRectangle S N A B)).card:ℝ) ≤
      ((B-A:ℕ):ℝ) *
        (((((N/A:ℕ):ℝ)-((N/B:ℕ):ℝ)) +
          (((2*N/A:ℕ):ℝ)-((2*N/B:ℕ):ℝ))) *
          (actualMass (∏ p ∈ S, p) z hprime)⁻¹ + 4*(z:ℝ)^4) := by
  have hc := slice_defect_card S hS N A B hA hAB
  have hc' : (((smoothSlice S N A B) \ (hyperbolaRectangle S N A B)).card:ℝ) ≤
      ((B-A:ℕ):ℝ) * (((roughBlock S (N/B) (N/A)).card:ℝ) +
        ((roughBlock S (2*N/B) (2*N/A)).card:ℝ)) := by exact_mod_cast hc
  have h1 := rough_interval_count (∏ p ∈ S, p) z (N/B) (N/A) hprime hz
    (Nat.div_le_div_left hAB hA)
  have h2 := rough_interval_count (∏ p ∈ S, p) z (2*N/B) (2*N/A) hprime hz
    (Nat.div_le_div_left hAB hA)
  apply hc'.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  change _ ≤ _ at h1 h2
  unfold roughBlock
  linarith

end OrdinarySmoothRough

end

end OAI
