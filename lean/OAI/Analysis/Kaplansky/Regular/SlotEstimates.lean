import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.Regular.CStarEstimates
import OAI.Analysis.Kaplansky.Regular.FreeEstimates

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped ComplexOrder InnerProductSpace BigOperators ENNReal
attribute [local instance] Classical.propDecidable
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]

lemma small_row_norm (T : ι → H →L[ℂ] H)
    (hr : ∑ i, T i*star (T i) ≤ (1/10000:ℝ) • 1) :
    ‖∑ i, T i*star (T i)‖ ≤ (1/10000:ℝ) := by
  apply (CStarAlgebra.norm_le_norm_of_le_of_nonneg hr
    (Finset.sum_nonneg fun index _ => mul_star_self_nonneg (T index))).trans
  rw [norm_smul]
  norm_num only [Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ) < 1/10000)]
  exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (by norm_num)).trans_eq (mul_one _)

lemma small_entry_gram_norm (T : ι → H →L[ℂ] H)
    (hr : ∑ i, T i*star (T i) ≤ (1/10000:ℝ) • 1) (i : ι) :
    ‖star (T i)*T i‖ ≤ (1/10000:ℝ) := by
  rw [CStarRing.norm_star_mul_self,← CStarRing.norm_self_mul_star]
  apply (CStarAlgebra.norm_le_norm_of_le_of_nonneg
    (Finset.single_le_sum (fun index _ => mul_star_self_nonneg (T index)) (Finset.mem_univ i))
    (mul_star_self_nonneg _)).trans
  exact small_row_norm T hr

lemma creationSum_small_defect (e : ι → ℕ) (he : Function.Injective e) (T : ι → H →L[ℂ] H)
    (hc : ∑ i, star (T i)*T i = 1)
    (hr : ∑ i, T i*star (T i) ≤ (1/10000:ℝ) • 1) :
    ‖star (∑ i, diagonal (T i)*creation (e i)) * (∑ j, diagonal (T j)*creation (e j)) - 1‖
      ≤ (1/10000:ℝ) := by
  rw [creationSum_gram_self e he T hc]
  have hid (z : HilbertSum F2 H →L[ℂ] HilbertSum F2 H) : 1-z-1 = -z := by abel
  rw [hid,norm_neg]
  exact cutSum_norm_le e he _ (by norm_num) (small_entry_gram_norm T hr)

lemma creationSum_norm_le_two (e : ι → ℕ) (he : Function.Injective e) (T : ι → H →L[ℂ] H)
    (hc : ∑ i, star (T i)*T i = 1)
    (hr : ∑ i, T i*star (T i) ≤ (1/10000:ℝ) • 1) :
    ‖∑ i, diagonal (T i)*creation (e i)‖ ≤ 2 := by
  let C := ∑ i, diagonal (T i)*creation (e i)
  have hd : ‖star C*C-1‖ ≤ (1/10000:ℝ) := creationSum_small_defect e he T hc hr
  have hnorm : ‖star C*C‖ ≤ (1/10000:ℝ)+1 := by
    calc
      _ = ‖(star C*C-1)+1‖ := by rw [sub_add_cancel]
      _ ≤ ‖star C*C-1‖+‖(1 : HilbertSum F2 H →L[ℂ] HilbertSum F2 H)‖ := norm_add_le _ _
      _ ≤ _ := add_le_add hd ContinuousLinearMap.norm_id_le
  rw [CStarRing.norm_star_mul_self (x := C)] at hnorm
  change ‖C‖ ≤ 2
  nlinarith [norm_nonneg C]

lemma annihilationSum_norm_le (e : ι → ℕ) (he : Function.Injective e) (T : ι → H →L[ℂ] H)
    (hr : ∑ i, T i*star (T i) ≤ (1/10000:ℝ) • 1) :
    ‖∑ i, diagonal (T i)*annihilation (e i)‖ ≤ (1/100:ℝ) := by
  have hrow : ‖∑ i, diagonal (G:=F2) (T i)*star (diagonal (T i))‖ ≤ (1/10000:ℝ) := by
    have heq : (∑ i, diagonal (G:=F2) (T i)*star (diagonal (T i))) =
        diagonal (∑ i, T i*star (T i)) := by
      simp only [← diagonal_star,← diagonal_mul]
      exact (map_sum (diagonalHom (G:=F2) (H:=H)) _ _).symm
    rw [heq]
    exact (diagonal_norm_le _).trans (small_row_norm T hr)
  have hcol : ‖∑ i, star (annihilation (H:=H) (e i))*annihilation (e i)‖ ≤ 1 := by
    simp only [annihilation_star_mul_self]
    exact sum_negative_norm_le e he
  calc
    _ ≤ Real.sqrt ‖∑ i, diagonal (G:=F2) (T i)*star (diagonal (T i))‖ *
        Real.sqrt ‖∑ i, star (annihilation (H:=H) (e i))*annihilation (e i)‖ :=
      norm_sum_mul_le _ _
    _ ≤ Real.sqrt (1/10000:ℝ) * Real.sqrt 1 := by gcongr
    _ = 1/100 := by
      have hsqrt : Real.sqrt (10000 : ℝ) = 100 :=
        (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
      norm_num [Real.sqrt_div, hsqrt]

lemma small_gram_perturbation {A : Type*} [CStarAlgebra A] (T U S V δ : A)
    (hT : ‖T‖ ≤ 2) (hU : ‖U‖ ≤ 2) (hS : ‖S‖ ≤ (1/100:ℝ)) (hV : ‖V‖ ≤ (1/100:ℝ))
    (hδ : ‖star T*U-δ‖ ≤ (1/10000:ℝ)) :
    ‖star (T+S)*(U+V)-δ‖ ≤ (1/16:ℝ) := by
  have hid : star (T+S)*(U+V)-δ = (star T*U-δ) + star T*V + star S*U + star S*V := by
    simp only [star_add]; noncomm_ring
  rw [hid]
  calc
    _ ≤ ((‖star T*U-δ‖ + ‖T‖*‖V‖) + ‖S‖*‖U‖) + ‖S‖*‖V‖ := by
      apply (norm_add_le _ _).trans
      apply add_le_add
      · apply (norm_add_le _ _).trans
        apply add_le_add
        · apply (norm_add_le _ _).trans
          exact add_le_add le_rfl (by simpa only [norm_star] using norm_mul_le (star T) V)
        · simpa only [norm_star] using norm_mul_le (star S) U
      · simpa only [norm_star] using norm_mul_le (star S) V
    _ ≤ ((1/10000 + 2*(1/100:ℝ)) + (1/100)*2) + (1/100)*(1/100) := by gcongr
    _ ≤ 1/16 := by norm_num

lemma free_rows_near_gram (e : Fin 2 × ι → ℕ) (he : Function.Injective e) (T : ι → H →L[ℂ] H)
    (hc : ∑ i, star (T i)*T i = 1)
    (hr : ∑ i, T i*star (T i) ≤ (1/10000:ℝ) • 1) :
    ∀ r s : Fin 2,
      ‖star (∑ i, diagonal (T i)*left (freeGen (e (r,i)))) *
        (∑ j, diagonal (T j)*left (freeGen (e (s,j)))) - (if r=s then 1 else 0)‖ ≤ (1/16:ℝ) := by
  intro r s
  have hei (r : Fin 2) : Function.Injective (fun i => e (r,i)) := by
    intro i j hij
    exact (Prod.mk.inj (he hij)).2
  let C (r : Fin 2) := ∑ i, diagonal (T i)*creation (e (r,i))
  let D (r : Fin 2) := ∑ i, diagonal (T i)*annihilation (e (r,i))
  have hsplit (r : Fin 2) : (∑ i, diagonal (T i)*left (freeGen (e (r,i)))) = C r+D r := by
    simp only [left_split,mul_add,Finset.sum_add_distrib,C,D]
  rw [hsplit,hsplit]
  apply small_gram_perturbation
  · exact creationSum_norm_le_two _ (hei r) T hc hr
  · exact creationSum_norm_le_two _ (hei s) T hc hr
  · exact annihilationSum_norm_le _ (hei r) T hr
  · exact annihilationSum_norm_le _ (hei s) T hr
  · by_cases hrs : r=s
    · subst s
      simpa only [C,ite_true] using creationSum_small_defect _ (hei r) T hc hr
    · rw [ite_eq_right hrs]
      have hh : star (C r)*C s = 0 := creationSum_gram_cross _ _ (fun i j hij => hrs (Prod.mk.inj (he hij)).1) T
      rw [hh,sub_zero,norm_zero]
      norm_num


end KaplanskyConsequences.Regular

end

end OAI
