import Mathlib

namespace OAI

section
section
namespace MetricKMedian.SourceBalance
open Finset
variable {I : Type*} [Fintype I]

noncomputable def positive (m : I → ℝ) : Finset I := univ.filter (fun i => m i < 1)
noncomputable def negative (m : I → ℝ) : Finset I := univ.filter (fun i => 1 < m i)
noncomputable def nonzero (m : I → ℝ) : Finset I := univ.filter (fun i => m i ≠ 1)
noncomputable def amount (m : I → ℝ) : ℝ := ∑ i, max (1-m i) 0

 theorem amount_nonneg (m : I → ℝ) : 0 ≤ amount m := sum_nonneg (fun _ _ => le_max_right _ _)

 theorem amount_eq_positive (m : I → ℝ) : amount m=∑ i ∈ positive m, (1-m i) := by
  rw [amount,positive,sum_filter]
  apply sum_congr rfl
  intro i _
  split_ifs with hi
  · exact max_eq_left (sub_nonneg.mpr hi.le)
  · exact max_eq_right (sub_nonpos.mpr (le_of_not_gt hi))

 theorem amount_eq_negative (m : I → ℝ) (hm : ∑ i, m i=Fintype.card I) :
    amount m=∑ i ∈ negative m, (m i-1) := by
  have hzero : (∑ i, (1-m i))=0 := by rw [sum_sub_distrib,hm]; simp
  have hp : ∀ i, max (1-m i) 0-max (m i-1) 0=1-m i := by
    intro i
    by_cases h : m i ≤ 1
    · rw [max_eq_left (sub_nonneg.mpr h),max_eq_right (sub_nonpos.mpr h)]
      ring
    · rw [max_eq_right (by linarith only [h]),max_eq_left (by linarith only [h])]
      ring
  have hs := congrArg (fun f : I → ℝ => ∑ i, f i) (funext hp)
  simp only [sum_sub_distrib,hzero] at hs
  rw [amount,negative,sum_filter]
  have he : (∑ i, max (m i-1) 0)=∑ i, if 1 < m i then m i-1 else 0 := by
    apply sum_congr rfl
    intro i _
    split_ifs with hi
    · exact max_eq_left (sub_nonneg.mpr hi.le)
    · exact max_eq_right (sub_nonpos.mpr (le_of_not_gt hi))
  linarith only [hs,he]

 theorem abs_sum (m : I → ℝ) (hm : ∑ i, m i=Fintype.card I) :
    (∑ i, |1-m i|)=2*amount m := by
  have hp : ∀ i, |1-m i|=max (1-m i) 0+max (m i-1) 0 := by
    intro i
    by_cases h : m i ≤ 1
    · rw [abs_of_nonneg (sub_nonneg.mpr h),max_eq_left (sub_nonneg.mpr h),
        max_eq_right (sub_nonpos.mpr h),add_zero]
    · rw [abs_of_nonpos (by linarith only [h]),max_eq_right (by linarith only [h]),
        max_eq_left (by linarith only [h]),zero_add]
      ring
  simp_rw [hp]
  rw [sum_add_distrib]
  have hn : (∑ i, max (m i-1) 0)=amount m := by
    rw [amount_eq_negative m hm,negative,sum_filter]
    apply sum_congr rfl
    intro i _
    split_ifs with hi
    · exact max_eq_left (sub_nonneg.mpr hi.le)
    · exact max_eq_right (sub_nonpos.mpr (le_of_not_gt hi))
  rw [hn]
  change amount m+amount m=2*amount m
  ring

 theorem nonzero_card (m : I → ℝ) {g : ℝ} (hm : ∑ i, m i=Fintype.card I)
    (hgrid : ∀ i, m i ≠ 1 → g ≤ |1-m i|) :
    g*((nonzero m).card:ℝ) ≤ 2*amount m := by
  have hsum := sum_le_sum (s := nonzero m) (f := fun _ => g) (g := fun i => |1-m i|)
    (fun i hi => hgrid i (mem_filter.mp hi).2)
  simp only [sum_const,nsmul_eq_mul] at hsum
  have hle := sum_le_univ_sum_of_nonneg (s := nonzero m) (fun i => abs_nonneg (1-m i))
  rw [abs_sum m hm] at hle
  simpa only [mul_comm g] using hsum.trans hle

 theorem nonzero_mass (m : I → ℝ) (hm : ∑ i, m i=Fintype.card I) :
    (∑ i ∈ nonzero m, m i)=((nonzero m).card:ℝ) := by
  have hp : ∀ i, (if m i ≠ 1 then m i else 0)-(if m i ≠ 1 then (1:ℝ) else 0)=m i-1 := by
    intro i
    split_ifs with hi
    · rfl
    · push Not at hi
      rw [hi]
      ring
  have hs := congrArg (fun f : I → ℝ => ∑ i, f i) (funext hp)
  simp only [sum_sub_distrib,hm,sum_const,card_univ,nsmul_eq_mul,mul_one,sub_self] at hs
  have hleft : (∑ i, if m i ≠ 1 then m i else 0)=∑ i ∈ nonzero m, m i := by
    rw [nonzero,sum_filter]
  have hright : (∑ i, if m i ≠ 1 then (1:ℝ) else 0)=((nonzero m).card:ℝ) := by
    rw [← sum_filter]
    simp [nonzero]
  rw [hleft,hright] at hs
  linarith only [hs]

 theorem grid_imbalance (Δ n : ℕ) {g : ℝ} (hg : 0 < g) (hunit : g*(Δ:ℝ)=1)
    (hn : g*(n:ℝ) ≠ 1) : g ≤ |1-g*(n:ℝ)| := by
  have hne : n ≠ Δ := by intro he; exact hn (he ▸ hunit)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hc : (n:ℝ)+1 ≤ Δ := by exact_mod_cast (Nat.succ_le_of_lt hlt)
    have hs := mul_le_mul_of_nonneg_left hc hg.le
    apply le_trans _ (le_abs_self _)
    nlinarith only [hs,hunit]
  · have hc : (Δ:ℝ)+1 ≤ n := by exact_mod_cast (Nat.succ_le_of_lt hgt)
    have hs := mul_le_mul_of_nonneg_left hc hg.le
    apply le_trans _ (neg_le_abs _)
    nlinarith only [hs,hunit]

theorem heavy_card (m : I → ℝ) {g b : ℝ} (hg : 0 < g) (hb : 0 < b)
    (hm0 : ∀ i, 0 ≤ m i) (hm : ∑ i, m i=Fintype.card I)
    (hgrid : ∀ i, m i ≠ 1 → g ≤ |1-m i|) :
    ((univ.filter (fun i => max 1 (b*amount m) < m i)).card:ℝ) ≤ 2/(g*b) := by
  let H := univ.filter (fun i => max 1 (b*amount m) < m i)
  have hsubset : H ⊆ nonzero m := by
    intro i hi
    have hh := (mem_filter.mp hi).2
    exact mem_filter.mpr ⟨mem_univ _,ne_of_gt ((le_max_left _ _).trans_lt hh)⟩
  have hhm : ((H.card:ℝ)*max 1 (b*amount m)) ≤ ∑ i ∈ H, m i := by
    have hh := sum_le_sum (s := H) (f := fun _ => max 1 (b*amount m))
      (fun i hi => (mem_filter.mp hi).2.le)
    simpa only [sum_const,nsmul_eq_mul] using hh
  have hmb := sum_le_sum_of_subset_of_nonneg hsubset (fun i _ _ => hm0 i)
  rw [nonzero_mass m hm] at hmb
  have hcard := nonzero_card m hm hgrid
  have hmul := mul_le_mul_of_nonneg_left (hhm.trans hmb) hg.le
  by_cases ha : 0 < amount m
  · have hbA := mul_le_mul_of_nonneg_left (le_max_right (1:ℝ) (b*amount m))
      (show 0 ≤ g*(H.card:ℝ) by positivity)
    have hfin : g*(H.card:ℝ)*b ≤ 2 := by
      apply (mul_le_mul_iff_left₀ ha).mp
      nlinarith only [hmul,hcard,hbA]
    apply (le_div_iff₀ (mul_pos hg hb)).mpr
    nlinarith only [hfin]
  · have ha0 : amount m=0 := le_antisymm (le_of_not_gt ha) (amount_nonneg m)
    have hn : (nonzero m).card=0 := by
      rw [ha0,mul_zero] at hcard
      have hle : ((nonzero m).card:ℝ) ≤ 0 := by nlinarith only [hcard,hg]
      exact_mod_cast le_antisymm hle (Nat.cast_nonneg _)
    have hH : H.card=0 := Nat.le_zero.mp ((card_le_card hsubset).trans_eq hn)
    change (H.card:ℝ) ≤ _
    rw [hH,Nat.cast_zero]
    positivity

end MetricKMedian.SourceBalance
end
end

end OAI
