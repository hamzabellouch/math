import Mathlib
import OAI.Analysis.FreeWords.FlipNorm

namespace OAI

noncomputable section

namespace KKFreeLiftDiagnostic

open scoped BigOperators Matrix.Norms.L2Operator Kronecker

noncomputable section

theorem mixedWord_centeredFlip_close {d : ℕ} (hd : 0 < d)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    ‖mixedWord (U : Matrix (Fin d) (Fin d) ℂ) (centeredFlip d)-1‖ ≤ 15*(d : ℝ)⁻¹ := by
  let V := left (U : Matrix (Fin d) (Fin d) ℂ)
  let X := centeredFlip d
  let F := flip d
  have hV : ‖V‖=1 := left_norm hd U
  have hVs : ‖star V‖=1 := by rw [norm_star,hV]
  have hX : ‖X‖≤2 := centeredFlip_norm_le hd
  have hF : ‖F‖=1 := flip_norm hd
  have ht : 0 ≤ (d : ℝ)⁻¹ := by positivity
  have hAX (A : Block d) (hA : ‖A‖=1) : ‖A*X‖≤2 := by
    calc
      _ ≤ ‖A‖*‖X‖ := norm_mul_le _ _
      _ ≤ 1*2 := by rw [hA]; gcongr
      _ = _ := by norm_num
  have hAF (A : Block d) (hA : ‖A‖=1) : ‖A*F‖≤1 := by
    calc
      _ ≤ ‖A‖*‖F‖ := norm_mul_le _ _
      _ = 1 := by rw [hA,hF]; norm_num
  have hAD (A : Block d) (hA : ‖A‖=1) : ‖A*X-A*F‖≤(d : ℝ)⁻¹ := by
    rw [← mul_sub]
    calc
      _ ≤ ‖A‖*‖X-F‖ := norm_mul_le _ _
      _ = _ := by rw [hA,centeredFlip_close hd,one_mul]
  have hh := four_product_difference (V*X) (V*X) (star V*X) (star V*X)
    (V*F) (V*F) (star V*F) (star V*F) (d : ℝ)⁻¹ ht
    (hAX V hV) (hAX V hV) (hAX (star V) hVs) (hAX (star V) hVs)
    (hAF V hV) (hAF V hV) (hAF (star V) hVs) (hAF (star V) hVs)
    (hAD V hV) (hAD V hV) (hAD (star V) hVs) (hAD (star V) hVs)
  have he : V*F*(V*F)*(star V*F)*(star V*F)=1 := by
    simpa only [V,F,mixedWord,mul_assoc] using mixedWord_flip U
  rw [he] at hh
  simpa only [V,X,mixedWord,mul_assoc] using hh

theorem flip_obstruction (d : ℕ) (hd : 64 ≤ d) :
    normalizedTrace (centeredFlip d)=0 ∧ partialTrace (centeredFlip d)=0 ∧
    ‖centeredFlip d‖ ≤ 2 ∧
    ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
      (1/2 : ℝ) ≤ ‖normalizedTrace (mixedWord (U : Matrix (Fin d) (Fin d) ℂ) (centeredFlip d))‖ := by
  have hdp : 0 < d := by omega
  refine ⟨normalizedTrace_centeredFlip hdp,partialTrace_centeredFlip hdp,
    centeredFlip_norm_le hdp,fun U => ?_⟩
  have hh := (normalizedTrace_norm_le hdp
    (mixedWord (U : Matrix (Fin d) (Fin d) ℂ) (centeredFlip d)-1)).trans
    (mixedWord_centeredFlip_close hdp U)
  rw [normalizedTrace_sub,normalizedTrace_one hdp] at hh
  have hn := norm_sub_norm_le (1 : ℂ)
    (normalizedTrace (mixedWord (U : Matrix (Fin d) (Fin d) ℂ) (centeredFlip d)))
  rw [norm_one,norm_sub_rev] at hn
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdp
  have hd64 : (64 : ℝ) ≤ d := by exact_mod_cast hd
  have hb : 15*(d : ℝ)⁻¹ ≤ 1/2 := by
    rw [← div_eq_mul_inv,div_le_iff₀ hdR]
    linarith
  linarith

end

end KKFreeLiftDiagnostic
end

end OAI
