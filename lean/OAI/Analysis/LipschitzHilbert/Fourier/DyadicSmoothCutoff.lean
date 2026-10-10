import OAI.Analysis.LipschitzHilbert.Fourier.AnnularSquareBound

namespace OAI

/-! A genuine binary low-pass difference for the dyadic commutator
proof, with its scale-independent Fourier square bound. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

def dyadicDifference : SchwartzMap ℝ ℂ :=
  dilatedSlopeWindow reassemblyLow (1/2) (by norm_num)-reassemblyLow

@[simp] theorem dyadicDifference_apply (x : ℝ) :
    dyadicDifference x=reassemblyLow (x/2)-reassemblyLow x := by
  simp only [dyadicDifference,sub_apply,dilatedSlopeWindow_apply]
  congr 2
  ring

theorem dyadicDifference_small (x : ℝ) (hx : |x|≤1) : dyadicDifference x=0 := by
  have hh : |x/2|≤1 := by rw [abs_div]; norm_num; linarith
  simp only [dyadicDifference_apply,reassemblyLow_one x hx,reassemblyLow_one _ hh,sub_self]

theorem dyadicDifference_large (x : ℝ) (hx : 13/6≤|x|) : dyadicDifference x=0 := by
  have hh : 13/12≤|x/2| := by rw [abs_div]; norm_num; linarith
  simp only [dyadicDifference_apply,reassemblyLow_zero x (by linarith),
    reassemblyLow_zero _ hh,sub_self]

theorem dyadicDifference_norm (x : ℝ) : ‖dyadicDifference x‖≤2 := by
  rw [dyadicDifference_apply]
  exact (norm_sub_le _ _).trans (by linarith [reassemblyLow_norm (x/2),reassemblyLow_norm x])

theorem dyadicDifference_separated (j k : ℤ) (x : ℝ) (hjk : j+2≤k) :
    dyadicDifference ((2:ℝ)^j*x)=0 ∨ dyadicDifference ((2:ℝ)^k*x)=0 := by
  by_contra hn
  have hj : dyadicDifference ((2:ℝ)^j*x)≠0 := fun h => hn (Or.inl h)
  have hk : dyadicDifference ((2:ℝ)^k*x)≠0 := fun h => hn (Or.inr h)
  have hjlo : 1 < |(2:ℝ)^j*x| := lt_of_not_ge (fun h => hj (dyadicDifference_small _ h))
  have hkhi : |(2:ℝ)^k*x|<13/6 := lt_of_not_ge (fun h => hk (dyadicDifference_large _ h))
  have hp : (2:ℝ)^j*4≤(2:ℝ)^k := by
    calc
      _ = (2:ℝ)^(j+2) := by rw [zpow_add₀ (by norm_num)]; norm_num
      _ ≤ _ := zpow_le_zpow_right₀ (by norm_num) hjk
  have hm := mul_le_mul_of_nonneg_right hp (abs_nonneg x)
  have ha (n : ℤ) : |(2:ℝ)^n*x|=(2:ℝ)^n*|x| := by
    rw [abs_mul,abs_of_pos (zpow_pos (by norm_num) _)]
  rw [ha j] at hjlo
  rw [ha k] at hkhi
  nlinarith only [hm,hjlo,hkhi]

theorem dyadicDifference_nonzero_count (I : Finset ℤ) (x : ℝ) :
    (I.filter (fun n => dyadicDifference ((2:ℝ)^n*x)≠0)).card≤3 := by
  classical
  let A := I.filter (fun n => dyadicDifference ((2:ℝ)^n*x)≠0)
  change A.card≤3
  by_cases hne : A.Nonempty
  · obtain ⟨j,hj⟩ := hne
    have hjnz := (Finset.mem_filter.mp hj).2
    have hsub : A⊆Finset.Icc (j-1) (j+1) := by
      intro k hk
      have hknz := (Finset.mem_filter.mp hk).2
      apply Finset.mem_Icc.mpr
      constructor
      · by_contra hn
        exact (dyadicDifference_separated k j x (by omega)).elim hknz hjnz
      · by_contra hn
        exact (dyadicDifference_separated j k x (by omega)).elim hjnz hknz
    apply (Finset.card_le_card hsub).trans
    rw [Int.card_Icc]
    omega
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty]
    omega

theorem dyadicDifference_square_sum (I : Finset ℤ) (x : ℝ) :
    (∑ n∈I, ‖dyadicDifference ((2:ℝ)^n*x)‖^2)≤12 := by
  classical
  let A := I.filter (fun n => dyadicDifference ((2:ℝ)^n*x)≠0)
  have he : (∑ n∈I, ‖dyadicDifference ((2:ℝ)^n*x)‖^2)=
      ∑ n∈A, ‖dyadicDifference ((2:ℝ)^n*x)‖^2 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hnA
    have hz : dyadicDifference ((2:ℝ)^n*x)=0 := by
      by_contra h
      exact hnA (Finset.mem_filter.mpr ⟨hn,h⟩)
    simp only [hz,norm_zero,zero_pow (by decide : 2≠0)]
  rw [he]
  calc
    _ ≤ ∑ _n∈A, (4:ℝ) := by
      apply Finset.sum_le_sum
      intro n _
      simpa only [show (2:ℝ)^2=4 by norm_num] using
        pow_le_pow_left₀ (norm_nonneg _) (dyadicDifference_norm ((2:ℝ)^n*x)) 2
    _ = (A.card:ℝ)*4 := by simp
    _ ≤ 12 := by
      have hc : (A.card:ℝ)≤3 := by exact_mod_cast dyadicDifference_nonzero_count I x
      linarith

theorem dyadicDifference_inverse_square_sum (I : Finset ℕ) (d eta : ℝ) :
    (∑ n∈I, ‖dyadicDifference ((d/(2:ℝ)^n)*eta)‖^2)≤12 := by
  classical
  have h := dyadicDifference_square_sum (I.image (fun n : ℕ => -(n:ℤ))) (d*eta)
  rw [Finset.sum_image] at h
  · convert h using 1
    apply Finset.sum_congr rfl
    intro n _
    rw [zpow_neg,zpow_natCast]
    have he : d/(2:ℝ)^n*eta=((2:ℝ)^n)⁻¹*(d*eta) := by ring
    rw [he]
  · intro n _ m _ hnm
    exact_mod_cast (neg_injective hnm)

end LipschitzHilbert.PacketRepresentation

end

end OAI
