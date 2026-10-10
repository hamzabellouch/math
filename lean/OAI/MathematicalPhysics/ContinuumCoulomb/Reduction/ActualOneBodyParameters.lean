import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.ActualOneBodyScale
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FiniteBoxScale
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ScalarScaleBudgets

namespace OAI

/-! A fixed exponent closes the actual one-body matrix error, including
finite slab, nuclear quadrature, counterterms and orthonormalization. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem exists_actual_oneBody_parameters {rho freq a E : ℝ}
    (hrho : 0 ≤ rho) (hf : 0 < freq) (ha : 0 < a) (hE : 0 ≤ E) :
    ∃ k₀ : ℕ, 1 ≤ k₀ ∧ ∀ r s p k : ℕ, k₀+5*r+72*s+p ≤ k →
    ∀ N H S D : ℝ, 2 ≤ N →
      (N^k)^50 ≤ H → H ≤ 2*(N^k)^50 →
      (N^k)^5 ≤ S → S ≤ 2*(N^k)^5 → 25*(k:ℝ)*Real.log N ≤ D →
    ∀ (m : ℕ) (u : Fin m → PlanarPosition), (m:ℝ) ≤ N^r →
      (∀ j, ‖u j‖ ≤ N^s) → (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
    ∀ F : Position → ℝ,
      (∀ i j, Integrable (fun x => F x*continuumLocalizedMode freq (u i) x*
        continuumLocalizedMode freq (u j) x)) →
      (∀ i j, |∫ x, F x*continuumLocalizedMode freq (u i) x*continuumLocalizedMode freq (u j) x| ≤
        E*((m:ℝ)+1)/(N^k)^32) → ∀ i j,
      |(a*(N^k)^30)*correctedNuclearOneBodyMatrix rho H S freq (a*(N^k)^30) u F i j-
        localizedOneBodyTarget (a*(N^k)^30) freq u i j| ≤ (N^p)⁻¹ := by
  let d := localizedCountertermBound freq
  let P := planarWellMatrixConstant
  let O := planarOverlapConstant
  let W := PlanarSobolev.wellBound
  let C := 4*a+8*a*E+8*a*W*O^2+8*a*O*P+8*d*O*P+a*P+d*P+d*W*O
  have hd : 0 ≤ d := localizedCountertermBound_nonnegative freq
  have hP : 0 ≤ P := planarWellMatrixConstant_nonnegative
  have hO : 0 ≤ O := planarOverlapConstant_nonnegative
  have hW : 0 ≤ W := PlanarSobolev.wellBound_nonnegative
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨qB,hqB,hbox⟩ := exists_finiteBoxResidual_parameter_offset hf hrho
  obtain ⟨qδ,hqδ,hδbound⟩ := exists_polynomial_ratio_offset (d/a) (by norm_num : (0:ℝ)<1)
  obtain ⟨qG,hqG,hgram⟩ := exists_polynomial_ratio_offset O (by norm_num : (0:ℝ)<1/2)
  obtain ⟨qE,hqE,herr⟩ := exists_polynomial_ratio_offset (32*C) (by norm_num : (0:ℝ)<1)
  refine ⟨qB+qδ+qG+qE+1,by omega,?_⟩
  intro r s p k hk N H S D hN hHlo hHhi hSlo hShi hD m u hm hu hsep F hI hF i j
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hR : 2 ≤ N^k := hN.trans (le_self_pow₀ hN1 (by omega))
  have hR0 : 0 < N^k := by positivity
  have hR1 : 1 ≤ N^k := one_le_pow₀ hN1
  have hH : 0 < H := (pow_pos hR0 50).trans_le hHlo
  have hS : 0 < S := (pow_pos hR0 5).trans_le hSlo
  have hD0 : 0 ≤ D := (mul_nonneg (by positivity : 0 ≤ 25*(k:ℝ))
    (Real.log_nonneg hN1)).trans hD
  have hscale : 0 < a*(N^k)^30 := by positivity
  let δ := d*(m:ℝ)/(a*(N^k)^30)
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    calc
      _ ≤ (d/a)*N^r/(N^k)^2 := by
        dsimp [δ]
        calc
          _ = (d/a)*(m:ℝ)/(N^k)^30 := by ring
          _ ≤ (d/a)*N^r/(N^k)^2 := by
            gcongr
            decide
      _ ≤ 1 := by simpa only [pow_zero,div_one] using hδbound r 0 k (by omega) N hN
  have hcoeff (i : Fin m) : 0 ≤ localizedCounterterm freq u i/(a*(N^k)^30) ∧
      localizedCounterterm freq u i/(a*(N^k)^30) ≤ δ := by
    refine ⟨div_nonneg (localizedCounterterm_nonnegative freq u i) hscale.le,?_⟩
    apply div_le_div_of_nonneg_right _ hscale.le
    simpa only [d,mul_comm] using localizedCounterterm_bound hf u i
  have h19 : Real.exp (-(19/10:ℝ)*D) ≤ 1/(N^k)^40 :=
    by simpa only [one_div] using logarithmic_separation_residual hN k hD
  have h9 : Real.exp (-(9/10:ℝ)*D) ≤ 1/(N^k)^22 :=
    by simpa only [one_div] using logarithmic_separation_overlap hN k hD
  have hs : (m:ℝ)*localizedOverlapBound D ≤ 1/2 := by
    calc
      _ ≤ O*N^r/(N^k)^22 := by
        unfold localizedOverlapBound
        calc
          _ ≤ (m:ℝ)*(O*(1/(N^k)^22)) := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h9 hO) (Nat.cast_nonneg m)
          _ = O*(m:ℝ)/(N^k)^22 := by ring
          _ ≤ _ := by gcongr
      _ ≤ O*N^r/(N^k)^2 := div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_right₀ hR1 (by decide : 2 ≤ 22))
      _ ≤ 1/2 := by simpa only [pow_zero,div_one] using hgram r 0 k (by omega) N hN
  have hhalf : (N^k)^5 ≤ H/2 := by
    have h2 : 2*(N^k)^5 ≤ (N^k)^50 := by
      calc
        _ ≤ (N^k)*(N^k)^5 := mul_le_mul_of_nonneg_right hR (by positivity)
        _ = (N^k)^6 := by ring
        _ ≤ _ := pow_le_pow_right₀ hR1 (by decide)
    linarith [h2.trans hHlo]
  have hb (j : Fin m) :
      (∫ x, finiteBoxOrbitalResidual rho H S freq (a*(N^k)^30) u j x^2) ≤ (1/(N^k)^32)^2 := by
    apply (finiteBoxOrbitalResidual_square_bound hrho hH hS hf
      (pow_pos hR0 5) hhalf hSlo (a*(N^k)^30) u hδ hcoeff j).trans
    simpa only [one_div] using hbox r s k (by omega) N H S δ hN
      hHlo hHhi hSlo hShi hδ hδ1 m u hm hu j
  have hmat := correctedNuclearOneBodyMatrix_physical_scale hrho hH hS hf hD0 hR ha hE
    u hsep hs h19 h9 hcoeff hb F hI hF i j
  change _ ≤ C*((m:ℝ)+1)^5/(N^k)^2 at hmat
  apply hmat.trans
  have hm1 : (m:ℝ)+1 ≤ 2*N^r := by linarith [one_le_pow₀ hN1 (n := r)]
  calc
    C*((m:ℝ)+1)^5/(N^k)^2 ≤ C*(2*N^r)^5/(N^k)^2 := by gcongr
    _ = (32*C)*N^(5*r)/(N^k)^2 := by ring
    _ ≤ _ := by simpa only [one_div,one_mul] using herr (5*r) p k (by omega) N hN

end ContinuumCoulomb

end

end OAI
