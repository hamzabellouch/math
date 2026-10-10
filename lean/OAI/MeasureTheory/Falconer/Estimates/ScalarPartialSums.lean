import OAI.MeasureTheory.Falconer.Estimates.ScalarEnergyRefinement

namespace OAI

/-! Approximate arithmetic progressions from nearly equal increments. -/
namespace Falconer

noncomputable def scalarPartialSum (d : ℕ → ℝ) (j : ℕ) : ℝ := ∑ i ∈ Finset.range j, d i

 theorem scalar_partial_sum_error {ε a : ℝ} (d : ℕ → ℝ) (J j : ℕ) (hj : j ≤ J)
    (hd : ∀ i < J, |d i-a| ≤ ε) :
    |scalarPartialSum d j-(j:ℝ)*a| ≤ (j:ℝ)*ε := by
  have he : scalarPartialSum d j-(j:ℝ)*a = ∑ i ∈ Finset.range j, (d i-a) := by
    simp only [scalarPartialSum,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  rw [he]
  calc
    _ ≤ ∑ i ∈ Finset.range j, |d i-a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range j, ε := Finset.sum_le_sum (fun i hi => hd i ((Finset.mem_range.mp hi).trans_le hj))
    _ = _ := by simp

 theorem scalar_partial_sum_pair {ε a : ℝ} (d : ℕ → ℝ) (J i j : ℕ)
    (hi : i ≤ J) (hj : j ≤ J) (hd : ∀ k < J, |d k-a| ≤ ε) :
    |(i:ℝ)-(j:ℝ)| * |a| ≤ |scalarPartialSum d i-scalarPartialSum d j|+((i:ℝ)+(j:ℝ))*ε := by
  have h1 := scalar_partial_sum_error d J i hi hd
  have h2 := scalar_partial_sum_error d J j hj hd
  have ht : |(i:ℝ)*a-(j:ℝ)*a| ≤
      |scalarPartialSum d i-(i:ℝ)*a|+|scalarPartialSum d i-scalarPartialSum d j|+
      |scalarPartialSum d j-(j:ℝ)*a| := by
    calc
      _ = |((i:ℝ)*a-scalarPartialSum d i)+
          (scalarPartialSum d i-scalarPartialSum d j)+(scalarPartialSum d j-(j:ℝ)*a)| := by congr 1; ring
      _ ≤ |(i:ℝ)*a-scalarPartialSum d i|+|scalarPartialSum d i-scalarPartialSum d j|+
          |scalarPartialSum d j-(j:ℝ)*a| := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = _ := by rw [abs_sub_comm ((i:ℝ)*a) (scalarPartialSum d i)]
  rw [← sub_mul,abs_mul] at ht
  nlinarith

 theorem scalar_partial_sums_separated {ε a ρ : ℝ} (hε : 0 ≤ ε)
    (d : ℕ → ℝ) (J : ℕ) (hd : ∀ k < J, |d k-a| ≤ ε)
    (hmargin : ρ+2*(J:ℝ)*ε ≤ |a|) :
    ∀ i ≤ J, ∀ j ≤ J, i ≠ j → ρ ≤ |scalarPartialSum d i-scalarPartialSum d j| := by
  intro i hi j hj hij
  have he : (1:ℝ) ≤ |(i:ℝ)-(j:ℝ)| := by
    have hne : (i:ℤ)-(j:ℤ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hij)
    have hh : (1:ℤ) ≤ |(i:ℤ)-(j:ℤ)| := Int.one_le_abs hne
    exact_mod_cast hh
  have ht := scalar_partial_sum_pair d J i j hi hj hd
  have hia : (i:ℝ) ≤ (J:ℝ) := by exact_mod_cast hi
  have hja : (j:ℝ) ≤ (J:ℝ) := by exact_mod_cast hj
  have hbound := mul_le_mul_of_nonneg_right (show (i:ℝ)+(j:ℝ) ≤ 2*(J:ℝ) by linarith) hε
  have ha := mul_le_mul_of_nonneg_right he (abs_nonneg a)
  nlinarith

 theorem scalar_partial_sums_card {ε a ρ : ℝ} (hε : 0 ≤ ε) (hρ : 0 < ρ)
    (d : ℕ → ℝ) (J : ℕ) (hd : ∀ k < J, |d k-a| ≤ ε)
    (hmargin : ρ+2*(J:ℝ)*ε ≤ |a|) :
    ((Finset.range (J+1)).image (scalarPartialSum d)).card = J+1 := by
  rw [Finset.card_image_of_injOn,Finset.card_range]
  intro i hi j hj hij
  by_contra hne
  have h := scalar_partial_sums_separated hε d J hd hmargin i
    (by have := Finset.mem_range.mp hi; omega) j (by have := Finset.mem_range.mp hj; omega) hne
  rw [hij,sub_self,abs_zero] at h
  linarith

end Falconer

end OAI
