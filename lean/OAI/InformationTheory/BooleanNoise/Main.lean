import OAI.InformationTheory.BooleanNoise.Attainment
import OAI.InformationTheory.BooleanNoise.Rearrangement
import OAI.InformationTheory.BooleanNoise.Comparison

namespace OAI

noncomputable section

namespace LeanBlast.CourtadeKumar

theorem informationDeficit_noise_le_psi_of_increasing_case {n : ℕ}
    (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (hcase : 0 < u → u < 1 →
      ∀ G : Cube n → ℝ, IsSignValued G → IsIncreasing G →
        (∃ x y, G x ≠ G y) →
          informationDeficit (noiseOperator u G) ≤ psi u)
    (F : Cube n → ℝ) (hF : IsSignValued F) :
    informationDeficit (noiseOperator u F) ≤ psi u := by
  classical
  by_cases hu0 : u = 0
  · subst u
    simp
  by_cases hu1 : u = 1
  · subst u
    exact informationDeficit_noise_one_le F hF
  have hupos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
  have hult : u < 1 := lt_of_le_of_ne hu.2 hu1
  obtain ⟨G, hG, hinc, _, hdom⟩ := exists_increasing_informationDeficit_ge u hu F hF
  apply hdom.trans
  by_cases hnc : ∃ x y, G x ≠ G y
  · exact hcase hupos hult G hG hinc hnc
  · have hconstant : G = fun _ => G (fun _ => false) := by
      funext x
      by_contra hx
      exact hnc ⟨x, (fun _ => false), hx⟩
    rw [hconstant, informationDeficit_noise_const]
    exact psi_nonneg u

theorem informationDeficit_noise_le_psi {n : ℕ}
    (F : Cube n → ℝ) (hF : IsSignValued F)
    (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    informationDeficit (noiseOperator u F) ≤ psi u := by
  apply informationDeficit_noise_le_psi_of_increasing_case u hu _ F hF
  intro hu0 hu1 G hG hinc hnc
  exact informationDeficit_noise_le_psi_of_increasing G hG hinc hnc u hu0 hu1

theorem courtadeKumar_bound {n : ℕ} (ε : ℝ)
    (hε0 : 0 ≤ ε) (hεhalf : ε ≤ (1 : ℝ) / 2) (f : Cube n → Bool) :
    mutualInformation ε f ≤ 1 - binaryEntropy ε := by
  rw [mutualInformation_eq_informationDeficit ε f hε0 hεhalf,
    one_sub_binaryEntropy_eq_psi]
  apply div_le_div_of_nonneg_right _ ell_pos.le
  apply informationDeficit_noise_le_psi (signEncoding f) (isSignValued_signEncoding f)
  constructor <;> linarith

theorem courtadeKumar : CourtadeKumarStatement := by
  intro n _ ε hε0 hεhalf f
  exact courtadeKumar_bound ε hε0 hεhalf f

theorem courtadeKumarAndAttainment : FullStatement :=
  ⟨courtadeKumar, dictatorAttainment⟩

end LeanBlast.CourtadeKumar

end

end OAI
