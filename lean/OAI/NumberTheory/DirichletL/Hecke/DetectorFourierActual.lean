import OAI.NumberTheory.DirichletL.Hecke.DetectorFourierSeparation
import OAI.NumberTheory.DirichletL.Hecke.DetectorPartition

namespace OAI

namespace SevenEighths.HeckeDetectorFourier
open MeasureTheory
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
open HeckeFamily HeckeDetectorProfiles
noncomputable section

def inverseCoefficient (χ : Character) (V W : ℝ → ℂ) (Dstar D : ℝ) (s : ℂ) (I : Ideal O) : ℂ :=
  (UniqueFactorizationMonoid.moebius I : ℂ)*IdealEuler.weighted (idealCoeff χ) s I*
    V ((Ideal.absNorm I : ℝ)/Dstar)*W ((Ideal.absNorm I : ℝ)/D)

def plainCoefficient (χ : Character) (W : ℝ → ℂ) (N : ℝ) (s : ℂ) (I : Ideal O) : ℂ :=
  IdealEuler.weighted (idealCoeff χ) s I*W ((Ideal.absNorm I : ℝ)/N)

lemma scaled_exp_log_product (x y D N R : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hD : 0 < D) (hN : 0 < N) :
    (D*N/R)*Real.exp (Real.log (x/D)+Real.log (y/N)) = x*y/R := by
  rw [Real.exp_add, Real.exp_log (div_pos hx hD), Real.exp_log (div_pos hy hN)]
  field_simp

theorem actual_pair_profile (χ : Character) (Ω V T W₁ W₂ : ℝ → ℂ)
    (Dstar D N Y U : ℝ) (hD : 0 < D) (hN : 0 < N) (s : ℂ)
    (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0)
    (hΩ : W₁ ((Ideal.absNorm I : ℝ)/D) ≠ 0 → W₂ ((Ideal.absNorm J : ℝ)/N) ≠ 0 →
      Ω (Real.log ((Ideal.absNorm I : ℝ)/D)+Real.log ((Ideal.absNorm J : ℝ)/N)) = 1) :
    HeckeDetectorPartition.pairCoefficient χ V T Dstar Y U s (I,J)*
      W₁ ((Ideal.absNorm I : ℝ)/D)*W₂ ((Ideal.absNorm J : ℝ)/N) =
      inverseCoefficient χ V W₁ Dstar D s I*plainCoefficient χ W₂ N s J*
        logSourceFun Ω V T (2*D*N/Dstar) (D*N/Y) (D*N/U)
          (Real.log ((Ideal.absNorm I : ℝ)/D)+Real.log ((Ideal.absNorm J : ℝ)/N)) := by
  by_cases hW₁ : W₁ ((Ideal.absNorm I : ℝ)/D) = 0
  · simp [hW₁, inverseCoefficient]
  by_cases hW₂ : W₂ ((Ideal.absNorm J : ℝ)/N) = 0
  · simp [hW₂, plainCoefficient]
  have hx : 0 < (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hy : 0 < (Ideal.absNorm J : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  have hscale (R : ℝ) := scaled_exp_log_product (Ideal.absNorm I) (Ideal.absNorm J) D N R hx hy hD hN
  have htwo : (2*D*N/Dstar)*Real.exp
      (Real.log ((Ideal.absNorm I : ℝ)/D)+Real.log ((Ideal.absNorm J : ℝ)/N)) =
        2*((Ideal.absNorm I : ℝ)*(Ideal.absNorm J : ℝ))/Dstar := by
    calc
      _ = 2*((D*N/Dstar)*Real.exp
        (Real.log ((Ideal.absNorm I : ℝ)/D)+Real.log ((Ideal.absNorm J : ℝ)/N))) := by ring
      _ = _ := by rw [hscale]; ring
  unfold HeckeDetectorPartition.pairCoefficient inverseCoefficient plainCoefficient logSourceFun
  rw [hΩ hW₁ hW₂, one_mul, htwo, hscale Y, hscale U, map_mul]
  simp only [map_mul, Nat.cast_mul, expNeg]
  push_cast
  ring_nf

theorem actual_finite_pair_separation (χ : Character) (Ω V T W₁ W₂ : ℝ → ℂ)
    (hΩc : HasCompactSupport Ω) (hΩs : ContDiff ℝ ∞ Ω)
    (hVs : ContDiff ℝ ∞ V) (hTs : ContDiff ℝ ∞ T)
    (Dstar D N Y U : ℝ) (hD : 0 < D) (hN : 0 < N) (s : ℂ)
    (S R : Finset (Ideal O)) (hS : ∀ I ∈ S, I ≠ 0) (hR : ∀ J ∈ R, J ≠ 0)
    (hΩ : ∀ I ∈ S, ∀ J ∈ R,
      W₁ ((Ideal.absNorm I : ℝ)/D) ≠ 0 → W₂ ((Ideal.absNorm J : ℝ)/N) ≠ 0 →
      Ω (Real.log ((Ideal.absNorm I : ℝ)/D)+Real.log ((Ideal.absNorm J : ℝ)/N)) = 1) :
    (∑ I ∈ S, ∑ J ∈ R, HeckeDetectorPartition.pairCoefficient χ V T Dstar Y U s (I,J)*
      W₁ ((Ideal.absNorm I : ℝ)/D)*W₂ ((Ideal.absNorm J : ℝ)/N)) =
      ∫ t : ℝ,
        (𝓕 (logSource Ω V T hΩc hΩs hVs hTs (2*D*N/Dstar) (D*N/Y) (D*N/U))) t*
        phasePolynomial S (inverseCoefficient χ V W₁ Dstar D s)
          (fun I => Real.log ((Ideal.absNorm I : ℝ)/D)) t*
        phasePolynomial R (plainCoefficient χ W₂ N s)
          (fun J => Real.log ((Ideal.absNorm J : ℝ)/N)) t := by
  rw [← finite_pair_separation]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  exact actual_pair_profile χ Ω V T W₁ W₂ Dstar D N Y U hD hN s I J
    (hS I hI) (hR J hJ) (hΩ I hI J hJ)

end
end SevenEighths.HeckeDetectorFourier

end OAI
