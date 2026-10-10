import OAI.NumberTheory.CubicMoment.Transform.MetaplecticCommonBound
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticFreeBlock
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticDualScaling

namespace OAI

/-! The actual critical-line coefficients of a retained Voronoi block.
The free-variable inverse-square-root bound follows from the published
coefficient support and the two proved common-divisor bounds. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticNormalizedDualCoefficient
    (a : Eisenstein → MetaplecticDualArgument → ℂ) (r : Eisenstein) (ℓ : ℤ)
    (nd : MetaplecticDualArgument × PrimaryArgument) : ℂ :=
  if IsCoprime (nd.2:Eisenstein) r then
    a r nd.1*metaplecticLocalCoefficient r nd.1 /
      ((Real.sqrt (Complex.normSq (metaplecticFrequency nd.1))*norm nd.2:ℝ):ℂ)*
      complexAngular (-ℓ) ((nd.2:Eisenstein)^3*metaplecticFrequency nd.1)
  else 0

lemma norm_metaplecticNormalizedDualCoefficient_le
    (a : Eisenstein → MetaplecticDualArgument → ℂ) (r : Eisenstein) (ℓ : ℤ)
    (nd : MetaplecticDualArgument × PrimaryArgument) :
    ‖metaplecticNormalizedDualCoefficient a r ℓ nd‖ ≤
      ‖a r nd.1*metaplecticLocalCoefficient r nd.1‖/
        (Real.sqrt (Complex.normSq (metaplecticFrequency nd.1))*norm nd.2) := by
  have hD := norm_pos_of_ne_zero (primary_ne_zero nd.2.property)
  have hz : ((nd.2:Eisenstein)^3:ℂ)*metaplecticFrequency nd.1 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (fun h => primary_ne_zero nd.2.property (Subtype.ext h)))
      (metaplecticFrequency_ne_zero nd.1)
  unfold metaplecticNormalizedDualCoefficient
  split_ifs
  · rw [norm_mul,norm_div,norm_complexAngular hz, mul_one,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  · rw [norm_zero]
    positivity

lemma metaplectic_free_coefficient_sq {A c B D : ℝ}
    (_hA : 0 ≤ A) (hc : 0 < c) (hB : 0 < B) (_hD : 0 < D)
    {z : ℂ} (hz : ‖z‖ ≤ A/(Real.sqrt (c*B)*D)) :
    ‖z‖^2 ≤ (A/(Real.sqrt c*D))^2/B := by
  apply (pow_le_pow_left₀ (_root_.norm_nonneg _) hz 2).trans_eq
  rw [div_pow,mul_pow,Real.sq_sqrt (by positivity),div_pow,mul_pow,
    Real.sq_sqrt hc.le]
  ring

/-- All dependence on the free primary element has been extracted as
its inverse square root. The coefficient is the actual Voronoi one. -/
lemma metaplectic_actual_free_coefficient_sq
    {a : Eisenstein → MetaplecticDualArgument → ℂ} {C : ℝ} (hC : 0 ≤ C)
    {r : Eisenstein} (hr : primary r) (d : PrimaryArgument) (ℓ : ℤ)
    (n : MetaplecticDualArgument) {j : ℤ} (hj : -1 ≤ j) (ζ : Eisensteinˣ)
    {h h' w : Eisenstein} (hh : primary h) (hh' : primary h') (hw : primary w)
    (hwr : IsCoprime w r)
    (he : metaplecticFrequency n = traceLambda^j*(ζ.val:ℂ)*(h:ℂ)*(w:ℂ)*(h':ℂ)^3)
    (ha : ‖a r n‖ ≤ C*3^((max j 0:ℤ)/3:ℝ)*Real.sqrt (norm h')) :
    ‖metaplecticNormalizedDualCoefficient a r ℓ (n,d)‖^2 ≤
      (C*3^((max j 0:ℤ)/3:ℝ)*Real.sqrt (norm h')*
        min (norm r) (norm h*norm h') /
        (Real.sqrt ((3:ℝ)^((j+1).toNat-1:ℝ)*norm h*norm h'^3)*norm d))^2/norm w := by
  have hR := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hH := norm_pos_of_ne_zero (primary_ne_zero hh)
  have hP := norm_pos_of_ne_zero (primary_ne_zero hh')
  have hW := norm_pos_of_ne_zero (primary_ne_zero hw)
  have hD := norm_pos_of_ne_zero (primary_ne_zero d.property)
  have hg := le_min (metaplecticCommonNorm_le_level hr n)
    (metaplecticCommonNorm_le_supported hr n (j+1).toNat ζ hh hh' hwr
      (metaplectic_numerator_of_frequency n hj ζ h h' w he))
  have hc := metaplectic_actual_coefficient_common_bound hC hr n ha
  have hb : ‖a r n*metaplecticLocalCoefficient r n‖ ≤
      C*3^((max j 0:ℤ)/3:ℝ)*Real.sqrt (norm h')*min (norm r) (norm h*norm h') :=
    hc.trans (mul_le_mul_of_nonneg_left hg (by positivity))
  have hn := metaplectic_frequency_norm n (j+1).toNat ζ h h' w
    (metaplectic_numerator_of_frequency n hj ζ h h' w he)
  have hn' : Complex.normSq (metaplecticFrequency n) =
      ((3:ℝ)^((j+1).toNat-1:ℝ)*norm h*norm h'^3)*norm w := by
    rw [hn]
    ring
  apply metaplectic_free_coefficient_sq (by positivity) (by positivity) hW hD
  apply (norm_metaplecticNormalizedDualCoefficient_le a r ℓ (n,d)).trans
  rw [hn']
  exact div_le_div_of_nonneg_right hb (by positivity)

end CubicFirstMoment

end

end OAI
