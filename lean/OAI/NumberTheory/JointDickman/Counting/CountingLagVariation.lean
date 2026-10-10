import OAI.NumberTheory.JointDickman.Counting.TruncatedCoefficientVariation

namespace OAI

/-! # Total variation of the actual cut-off counting coefficients -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem counting_lag_variation
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (d : Fin 4 →₀ ℕ)
    {m : ℕ} (hm : 0 < m) (c : ℕ → ℝ) (hc : c 0 = squarefreeLeadingConstant (1/2))
    (D : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ B : ℕ in atTop, ∀ (T H : ℕ) (σ : ℝ),
      0 < T → Real.log T ≤ (B : ℝ)/10 → η*T ≤ H → |σ| ≤ 3 → ∀ a b : Fin m,
      finiteCoefficientVariation (cutLagWeight H T
        (fun j => countingTermCoefficient P d m B j c D T σ a b/(j : ℝ))) T ≤ C/T := by
  obtain ⟨A,L,hA,hL,hreg⟩ := counting_normalized_coefficient_regular hM hMP P d hm c hc D hη
  refine ⟨2*A+L,by positivity,?_⟩
  filter_upwards [hreg] with B hB
  intro T H σ hT hlog hH hσ a b
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  let f := fun j => countingTermCoefficient P d m B j c D T σ a b
  have he (j : ℕ) : f j/(j : ℝ) = ((T : ℝ)/j*f j)/T := by field_simp
  have hj (j : ℕ) (hh : H < j) : η*(T : ℝ) ≤ j := hH.trans (by exact_mod_cast hh.le)
  apply cutLagWeight_variation H T _ hT hA hL
  · intro j hh _
    rw [he,abs_div,abs_of_pos hTr]
    exact div_le_div_of_nonneg_right (hB j j T σ hT1 hlog (hj j hh) (hj j hh) hσ a b).1 hTr.le
  · intro j hh _
    rw [he,he,← sub_div,abs_div,abs_of_pos hTr]
    have hj' : η*(T : ℝ) ≤ (j+1 : ℕ) := (hj j hh).trans (by norm_cast; omega)
    have hv := (hB j (j+1) T σ hT1 hlog (hj j hh) hj' hσ a b).2
    have habs : |(j : ℝ)-(j+1 : ℕ)| = 1 := by push_cast; ring_nf; norm_num
    rw [habs,mul_one] at hv
    exact (div_le_div_of_nonneg_right hv hTr.le).trans_eq (by ring)

theorem counting_lag_weight_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (d : Fin 4 →₀ ℕ)
    {m : ℕ} (hm : 0 < m) (c : ℕ → ℝ) (hc : c 0 = squarefreeLeadingConstant (1/2))
    (D : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ B : ℕ in atTop, ∀ (T H : ℕ) (σ : ℝ),
      0 < T → Real.log T ≤ (B : ℝ)/10 → η*T ≤ H → |σ| ≤ 3 → ∀ (a b : Fin m) (j : ℕ),
      |cutLagWeight H T (fun k => countingTermCoefficient P d m B k c D T σ a b/(k : ℝ)) j| ≤ A/T := by
  obtain ⟨A,hA,hbound⟩ := countingTermCoefficient_bounded hM hMP P d hm c hc D
  refine ⟨A/η,by positivity,?_⟩
  filter_upwards [hbound] with B hB
  intro T H σ hT hlog hH hσ a b j
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  unfold cutLagWeight
  split_ifs with hj
  · have hjr : η*(T : ℝ) ≤ j := hH.trans (by exact_mod_cast hj.1.le)
    have hj0 : (0 : ℝ) < j := (mul_pos hη hTr).trans_le hjr
    rw [abs_div,abs_of_pos hj0]
    calc
      _ ≤ A/(j : ℝ) := div_le_div_of_nonneg_right (hB j T σ hT1 hlog hσ a b) hj0.le
      _ ≤ A/(η*T) := div_le_div_of_nonneg_left hA (mul_pos hη hTr) hjr
      _ = _ := by ring
  · rw [abs_zero]
    positivity

end JointDickman

end OAI
