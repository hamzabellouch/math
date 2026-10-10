import OAI.NumberTheory.CubicMoment.Transform.MetaplecticCriticalFinite
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticBlockCoefficient
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticDualFinite

namespace OAI

/-! The actual finite retained Voronoi sum on the critical line, with
its coefficients normalized for ordinary free-variable mean value. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticRawDualCoefficient
    (a : Eisenstein → MetaplecticDualArgument → ℂ) (r : Eisenstein) (ℓ : ℤ)
    (nd : MetaplecticDualArgument × PrimaryArgument) : ℂ :=
  if IsCoprime (nd.2:Eisenstein) r then
    a r nd.1*metaplecticLocalCoefficient r nd.1 /
      ((Complex.normSq (metaplecticFrequency nd.1)*norm nd.2^(5/2:ℝ):ℝ):ℂ)*
      complexAngular (-ℓ) ((nd.2:Eisenstein)^3*metaplecticFrequency nd.1)
  else 0

lemma metaplectic_sqrt_quotient {D N : ℝ} (hD : 0 < D) (hN : 0 < N) :
    Real.sqrt (D^3*N)/(N*D^(5/2:ℝ)) = 1/(Real.sqrt N*D) := by
  have hsD : Real.sqrt (D^3) = D*Real.sqrt D := by
    rw [show D^3 = D^2*D by ring,Real.sqrt_mul (sq_nonneg D),Real.sqrt_sq_eq_abs,
      abs_of_pos hD]
  have hpD : D^(5/2:ℝ) = D^2*Real.sqrt D := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_natCast,←Real.rpow_add hD]
    congr 1
    norm_num
  have he : Real.sqrt (D^3*N)*(Real.sqrt N*D) = N*D^(5/2:ℝ) := by
    rw [Real.sqrt_mul (by positivity),hsD,hpD]
    calc
      _ = D^2*Real.sqrt D*(Real.sqrt N)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt hN.le]; ring
  apply (div_eq_div_iff (mul_ne_zero hN.ne' (Real.rpow_pos_of_pos hD _).ne')
    (mul_ne_zero (Real.sqrt_pos.mpr hN).ne' hD.ne')).mpr
  simpa only [one_mul] using he

lemma metaplecticRawDualCoefficient_normalize
    (a : Eisenstein → MetaplecticDualArgument → ℂ) (r : Eisenstein) (ℓ : ℤ)
    (nd : MetaplecticDualArgument × PrimaryArgument) :
    metaplecticRawDualCoefficient a r ℓ nd*(Real.sqrt (metaplecticDualNorm nd):ℂ) =
      metaplecticNormalizedDualCoefficient a r ℓ nd := by
  have hD := norm_pos_of_ne_zero (primary_ne_zero nd.2.property)
  have hN := Complex.normSq_pos.mpr (metaplecticFrequency_ne_zero nd.1)
  have he := metaplectic_sqrt_quotient hD hN
  unfold metaplecticDualNorm
  have hec : ((Real.sqrt (norm nd.2^3*Complex.normSq (metaplecticFrequency nd.1)):ℝ):ℂ)/
      ((Complex.normSq (metaplecticFrequency nd.1)*norm nd.2^(5/2:ℝ):ℝ):ℂ) =
      1/((Real.sqrt (Complex.normSq (metaplecticFrequency nd.1))*norm nd.2:ℝ):ℂ) := by
    exact_mod_cast he
  unfold metaplecticRawDualCoefficient metaplecticNormalizedDualCoefficient
  split_ifs
  · calc
      _ = (a r nd.1*metaplecticLocalCoefficient r nd.1)*
          complexAngular (-ℓ) ((nd.2:Eisenstein)^3*metaplecticFrequency nd.1)*
          (((Real.sqrt (norm nd.2^3*Complex.normSq (metaplecticFrequency nd.1)):ℝ):ℂ)/
            ((Complex.normSq (metaplecticFrequency nd.1)*norm nd.2^(5/2:ℝ):ℝ):ℂ)) := by ring
      _ = _ := by rw [hec]; ring
  · simp only [zero_mul]

lemma metaplecticDualTerm_factor
    (a : Eisenstein → MetaplecticDualArgument → ℂ) (r : Eisenstein) (ℓ : ℤ)
    (W : ℝ → ℂ) (A X : ℝ) (nd : MetaplecticDualArgument × PrimaryArgument) :
    metaplecticDualTerm a r ℓ W A X nd =
      metaplecticRawDualCoefficient a r ℓ nd *
        metaplecticTransform ℓ W A
          (((2*Real.pi)^4*X/norm r^2)*metaplecticDualNorm nd) := by
  unfold metaplecticDualTerm metaplecticRawDualCoefficient
  rw [metaplecticDualNorm_eq]
  have he : (2*Real.pi)^4*metaplecticDualNorm nd*X/norm r^2 =
      ((2*Real.pi)^4*X/norm r^2)*metaplecticDualNorm nd := by ring
  rw [he]
  split_ifs <;> ring

/-- The cutoff is arbitrary and independent of height. This is an exact
identity for the original retained Voronoi terms. -/
theorem metaplectic_retained_critical
    (a : Eisenstein → MetaplecticDualArgument → ℂ) {r : Eisenstein} (hr : primary r)
    (ℓ : ℤ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {A X : ℝ} (hA : 0 ≤ A) (hX : 0 < X) (J t : ℝ)
    (hm : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-A))
    (hp : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-A)) :
    (∑ nd ∈ metaplecticDualBall J,
      metaplecticDualTerm a r ℓ (fun x => W x*mellinPhase t x) A X nd) =
      (Real.sqrt ((2*Real.pi)^4*X/norm r^2):ℂ)*((1/(2*Real.pi):ℝ):ℂ)*
        ∫ τ : ℝ, metaplecticCriticalKernel ℓ W ((2*Real.pi)^4*X/norm r^2)
          (fun u => ∑ nd ∈ metaplecticDualBall J,
            metaplecticNormalizedDualCoefficient a r ℓ nd*mellinPhase u (metaplecticDualNorm nd)) τ t := by
  have hR := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hc : 0 < (2*Real.pi)^4*X/norm r^2 := by positivity
  simp_rw [metaplecticDualTerm_factor]
  rw [metaplectic_finite_transform_critical _ _ _
    (fun nd _ => metaplecticDualNorm_pos nd) ℓ W hW hpos hsm hA hc hm hp t]
  simp_rw [metaplecticRawDualCoefficient_normalize]

end CubicFirstMoment

end

end OAI
