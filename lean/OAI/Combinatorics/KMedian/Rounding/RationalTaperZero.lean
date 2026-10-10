import Mathlib
import OAI.Combinatorics.KMedian.Process.Taper

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset
variable {I : Type*} [Fintype I] [LinearOrder I]

def extend (own Z : Finset I) (Δ : ℕ) : Finset I :=
  own ∪ (((Z \ own).sort (· ≤ ·)).take (Δ-own.card)).toFinset

omit [Fintype I] in
theorem extend_spec (own Z : Finset I) (Δ : ℕ) (hsub : own ⊆ Z)
    (hown : own.card ≤ Δ) (hZ : Δ ≤ Z.card) :
    own ⊆ extend own Z Δ ∧ extend own Z Δ ⊆ Z ∧ (extend own Z Δ).card=Δ := by
  let L := (((Z \ own).sort (· ≤ ·)).take (Δ-own.card)).toFinset
  have hL : L ⊆ Z \ own := by
    intro i hi
    exact (mem_sort (· ≤ ·)).mp (List.mem_of_mem_take (List.mem_toFinset.mp hi))
  have hdis : Disjoint own L := by
    apply disjoint_left.mpr
    intro i hi hli
    exact (mem_sdiff.mp (hL hli)).2 hi
  refine ⟨subset_union_left,union_subset hsub (hL.trans sdiff_subset),?_⟩
  change (own ∪ L).card=Δ
  rw [card_union_of_disjoint hdis]
  have hc : L.card=Δ-own.card := by
    rw [List.toFinset_card_of_nodup ((sort_nodup (Z \ own) (· ≤ ·)).take),List.length_take,
      length_sort,card_sdiff_of_subset hsub,min_eq_left (Nat.sub_le_sub_right hZ _)]
  rw [hc,Nat.add_sub_of_le hown]

def zeroSources (d : I → ℚ) : Finset I := univ.filter (fun i => d i=0)

def zeroSelection (d : I → ℚ) (own : Finset I) (Δ : ℕ) : Finset I :=
  extend own (zeroSources d) Δ

def zeroMarginal (d : I → ℚ) (own : Finset I) (Δ : ℕ) (i : I) : ℚ :=
  if i ∈ zeroSelection d own Δ then 1 else 0

theorem zero_data (g : ℚ) (d : I → ℚ) (own : Finset I) (Δ : ℕ)
    (_hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hcol : 1 ≤ colocatedMass g (fun i => (d i:ℝ)))
    (hown : ∀ i ∈ own, d i=0) (howncard : own.card ≤ Δ) :
    let q := zeroMarginal d own Δ
    (∀ i, 0 ≤ q i) ∧ (∀ i, q i ≤ 1) ∧ (∑ i, g*q i=1) ∧
      (∑ i, q i=Δ) ∧ (∀ i ∈ own, q i=1) ∧ (∀ i, 0 < q i → d i=0) := by
  let Z := zeroSources d
  have hz : (Z.card:ℝ)*(g:ℝ)=colocatedMass g (fun i => (d i:ℝ)) := by
    simp only [Z,zeroSources,colocatedMass,← sum_filter,sum_const,nsmul_eq_mul,
      Rat.cast_eq_zero]
  have hzcard : Δ ≤ Z.card := by
    have hh : (Δ:ℝ) ≤ Z.card := by nlinarith only [hcol,hz,hunit]
    exact_mod_cast hh
  have hsub : own ⊆ Z := by intro i hi; exact mem_filter.mpr ⟨mem_univ _,hown i hi⟩
  obtain ⟨hownS,hSZ,hcard⟩ := extend_spec own Z Δ hsub howncard hzcard
  change (∀ i, 0 ≤ zeroMarginal d own Δ i) ∧ _
  have hsum : (∑ i, zeroMarginal d own Δ i)=(Δ:ℚ) := by
    simp only [zeroMarginal,← sum_filter,filter_univ_mem,sum_const,nsmul_eq_mul,mul_one]
    exact_mod_cast hcard
  refine ⟨?_,?_,?_,hsum,?_,?_⟩
  · intro i; unfold zeroMarginal; split_ifs <;> norm_num
  · intro i; unfold zeroMarginal; split_ifs <;> norm_num
  · rw [← mul_sum,hsum]; exact_mod_cast hunit
  · intro i hi; exact ite_eq_left (hownS hi)
  · intro i hi
    have hm : i ∈ zeroSelection d own Δ := by
      by_contra hn
      simp only [zeroMarginal,ite_eq_right hn] at hi
      exact lt_irrefl _ hi
    exact (mem_filter.mp (hSZ hm)).2

end MetricKMedian.Taper
end
end

end OAI
