import OAI.NumberTheory.Ostmann.Section07SmoothPartition

namespace OAI

noncomputable section
namespace Ostmann.Construction
open scoped BigOperators

def logBlockCenters (G h : ℝ) : Finset ℤ := Finset.Icc (⌊G⌋-1) (⌈G+h⌉+1)

lemma logBlockCenters_support (G h x : ℝ) (hx : G≤x ∧ x≤G+h) {c : ℤ}
    (hc : Ostmann.smoothPartition (x-c)≠0) : c∈logBlockCenters G h := by
  have hs := Ostmann.smoothPartition_support_subset hc
  have hfloor := Int.floor_le G
  have hceil := Int.le_ceil (G+h)
  apply Finset.mem_Icc.mpr
  constructor
  · have h : (⌊G⌋:ℝ)-1≤(c:ℝ) := by linarith [hs.2,hx.1]
    exact_mod_cast h
  · have h : (c:ℝ)≤(⌈G+h⌉:ℝ)+1 := by linarith [hs.1,hx.2]
    exact_mod_cast h

theorem logBlockCenters_partition (G h x : ℝ) (hx : G≤x ∧ x≤G+h) :
    (∑c∈logBlockCenters G h,Ostmann.smoothPartition (x-c))=1 := by
  have ht := Ostmann.smoothPartition_translate_tsum x
  rw [tsum_eq_sum (s := logBlockCenters G h) (fun c hc => by
    by_contra hn
    exact hc (logBlockCenters_support G h x hx hn))] at ht
  exact ht

lemma logBlockCenters_bounds (G h : ℝ) {c : ℤ} (hc : c∈logBlockCenters G h) :
    G-2<(c:ℝ) ∧ (c:ℝ)<G+h+2 := by
  obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hc
  have hl : (⌊G⌋:ℝ)-1≤(c:ℝ) := by exact_mod_cast hlo
  have hh : (c:ℝ)≤(⌈G+h⌉:ℝ)+1 := by exact_mod_cast hhi
  have hf := Int.lt_floor_add_one G
  have he := Int.ceil_lt_add_one (G+h)
  constructor <;> linarith

lemma logBlockCenters_card_le (G h : ℝ) (hh : 0≤h) :
    ((logBlockCenters G h).card:ℝ)≤h+5 := by
  have hle : ⌊G⌋-1≤⌈G+h⌉+1 := by
    have hf := Int.floor_le G
    have hc := Int.le_ceil (G+h)
    have he : (⌊G⌋:ℝ)-1≤(⌈G+h⌉:ℝ)+1 := by linarith
    exact_mod_cast he
  have hnonneg : 0≤(⌈G+h⌉+1)+1-(⌊G⌋-1) := by omega
  rw [logBlockCenters,Int.card_Icc]
  have hcast : (((⌈G+h⌉+1)+1-(⌊G⌋-1)).toNat:ℝ)=
      (⌈G+h⌉:ℝ)+1+1-((⌊G⌋:ℝ)-1) := by
    norm_cast
    exact Int.toNat_of_nonneg hnonneg
  rw [hcast]
  have hf := Int.lt_floor_add_one G
  have hc := Int.ceil_lt_add_one (G+h)
  linarith

theorem logBlockCenters_weighted_partition (P : Finset ℕ) (G h : ℝ)
    (F : ℕ → ℝ) (hP : ∀p∈P,G≤Real.log p ∧ Real.log p≤G+h) :
    (∑c∈logBlockCenters G h,∑p∈P,Ostmann.smoothPartition (Real.log p-c)*F p)=∑p∈P,F p := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.sum_mul,logBlockCenters_partition G h (Real.log p) (hP p hp),one_mul]

end Ostmann.Construction

end

end OAI
