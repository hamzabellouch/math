import OAI.NumberTheory.CubicMoment.Estimates.ResidueGaussianPoisson
import OAI.NumberTheory.CubicMoment.Estimates.PublishedPrimitiveHecke
import OAI.NumberTheory.CubicMoment.Estimates.SchwartzLattice

namespace OAI

/-! Exact self-dual normalization of the finite-character Gaussian. -/
noncomputable section
namespace CubicFirstMoment

lemma residueHeckeScale_squared (q : Eisenstein) :
    4*Real.pi^2*(residueHeckeScale q)^2 = 3*norm q := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold residueHeckeScale
  rw [div_pow,Real.sq_sqrt (mul_nonneg (by norm_num) (norm_nonneg q))]
  field_simp
  ring

lemma residueGaussian_prefactor {q : Eisenstein} (hq : q ≠ 0)
    {t : ℝ} (ht : 0 < t) :
    (2/(Real.sqrt 3*norm q))*(Real.pi/(t/residueHeckeScale q)) =
      1/(Real.sqrt (norm q)*t) := by
  have hN := norm_pos_of_ne_zero hq
  have hsN : Real.sqrt (norm q) ≠ 0 := (Real.sqrt_pos.mpr hN).ne'
  have hs3 : Real.sqrt (3:ℝ) ≠ 0 := by positivity
  unfold residueHeckeScale
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]
  field_simp [ht.ne',hsN,hs3,Real.pi_ne_zero]
  nlinarith [Real.sq_sqrt hN.le]

lemma residueGaussian_exponent {q : Eisenstein} (hq : q ≠ 0)
    {t : ℝ} (ht : 0 < t) (h : Eisenstein) :
    -4*Real.pi^2/(t/residueHeckeScale q)*Complex.normSq ((h:ℂ)/((q:ℂ)*traceLambda)) =
      -norm h/(residueHeckeScale q*t) := by
  have hN := (norm_pos_of_ne_zero hq).ne'
  have hA := (residueHeckeScale_pos hq).ne'
  have hs := residueHeckeScale_squared q
  rw [Complex.normSq_div,Complex.normSq_mul,traceLambda_normSq]
  change -4*Real.pi^2/(t/residueHeckeScale q)*(norm h/(norm q*3)) = _
  field_simp
  nlinarith [congrArg (fun x : ℝ => x*norm h) hs]

lemma residueGaussian_selfDual {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) {t : ℝ} (ht : 0 < t) :
    residueLatticeTheta q χ (residueHeckeScale q) t =
      (1/(Real.sqrt (norm q)*t):ℝ) *
        ∑' h : Eisenstein, residueFiniteFourier q χ h *
          (Real.exp (-norm h/(residueHeckeScale q*t)):ℝ) := by
  rw [residueGaussian_poisson hq χ (residueHeckeScale_pos hq) ht]
  simp_rw [residueGaussian_exponent hq ht]
  have he (h : Eisenstein) : residueFiniteFourier q χ h *
      ((Real.pi/(t/residueHeckeScale q):ℝ)*(Real.exp (-norm h/(residueHeckeScale q*t)):ℝ)) =
      (Real.pi/(t/residueHeckeScale q):ℝ)*
        (residueFiniteFourier q χ h*(Real.exp (-norm h/(residueHeckeScale q*t)):ℝ)) := by ring
  simp_rw [he]
  rw [tsum_mul_left,Complex.real_smul,← mul_assoc,← Complex.ofReal_mul,
    residueGaussian_prefactor hq ht]

end CubicFirstMoment

end

end OAI
