import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGaussExpansion
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaMellin

namespace OAI

/-! Mellin transform of the literal primary Gauss expansion. All terms
are identified before applying the already proved absolute interchange. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaPrimarySupport_ne_zero {n : Eisenstein} (hn : cubicThetaPrimarySupport n) : n ≠ 0 := by
  obtain ⟨R,_⟩ := hn
  exact R.ne_zero

lemma cubicThetaPrimaryFrequency_sq (cd : CubicThetaPrimaryPair) :
    ‖cubicThetaFrequency (cubicThetaPrimaryNumerator cd)‖^2 =
      norm cd.val.1*norm cd.val.2^3/27 := by
  rw [cubicThetaFrequency_sq]
  unfold cubicThetaPrimaryNumerator norm
  simp only [Subalgebra.coe_mul,Subalgebra.coe_pow,Complex.normSq_mul,map_pow,
    lambdaE_coe,traceLambda_normSq]
  ring

/-- Conversion between the normalized Whittaker coefficient and the
unnormalized source coefficient in its squared-frequency Dirichlet series. -/
lemma cubicThetaPrimary_mellin_term (cd : CubicThetaPrimaryPair) (s : ℂ) :
    cubicThetaConjugateCoefficient (cubicThetaPrimaryNumerator cd)*
      (‖cubicThetaFrequency (cubicThetaPrimaryNumerator cd)‖:ℂ)^(-(2*s-1)) =
      ((3^(5/2:ℝ):ℝ):ℂ)*(Real.sqrt (norm cd.val.2):ℂ)*gauss cd.val.1*
        ((norm cd.val.1*norm cd.val.2^3/27:ℝ):ℂ)^(-s) := by
  let r := ‖cubicThetaFrequency (cubicThetaPrimaryNumerator cd)‖
  have hr : 0 < r := cubicThetaFrequency_pos (cubicThetaPrimaryNumerator_ne_zero cd)
  have hrC : (r:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr
  have hp : (r:ℂ)^(-(2*s-1)) = (r:ℂ)*((r^2:ℝ):ℂ)^(-s) := by
    have h := Complex.cpow_mul_ofReal_nonneg hr.le 2 (-s)
    simp only [Real.rpow_two,Complex.ofReal_ofNat] at h
    rw [←h]
    rw [show -(2*s-1) = (1:ℂ)+2*(-s) by ring,Complex.cpow_add _ _ hrC,Complex.cpow_one]
  have he := cubicThetaTau_primary_conj cd.property.1 cd.property.2.1 cd.property.2.2
  change star ((r:ℂ)*cubicThetaArithmeticCoefficient (cubicThetaPrimaryNumerator cd)) = _ at he
  simp only [star_mul,Complex.star_def,Complex.conj_ofReal] at he
  have he' : cubicThetaConjugateCoefficient (cubicThetaPrimaryNumerator cd)*(r:ℂ) =
      ((3^(5/2:ℝ):ℝ):ℂ)*(Real.sqrt (norm cd.val.2):ℂ)*gauss cd.val.1 := by
    simpa only [cubicThetaConjugateCoefficient,←Complex.star_def,Complex.ofReal_mul] using he
  change cubicThetaConjugateCoefficient (cubicThetaPrimaryNumerator cd)*(r:ℂ)^(-(2*s-1)) = _
  rw [hp,←mul_assoc,he']
  change _*((‖cubicThetaFrequency (cubicThetaPrimaryNumerator cd)‖^2:ℝ):ℂ)^(-s) = _
  rw [cubicThetaPrimaryFrequency_sq]

lemma cubicThetaSelected_dirichlet_reindex (u : ℂ) :
    cubicThetaDirichlet cubicThetaSelectedCoefficient u =
      ∑' cd : CubicThetaPrimaryPair,
        cubicThetaConjugateCoefficient (cubicThetaPrimaryNumerator cd)*
          (‖cubicThetaFrequency (cubicThetaPrimaryNumerator cd)‖:ℂ)^(-u) := by
  unfold cubicThetaDirichlet
  calc
    _ = ∑' n : Eisenstein, if cubicThetaPrimarySupport n then
        cubicThetaConjugateCoefficient n*(‖cubicThetaFrequency n‖:ℂ)^(-u) else 0 := by
      apply tsum_congr
      intro n
      by_cases hn : cubicThetaPrimarySupport n
      · simp only [cubicThetaPrimarySupport_ne_zero hn,ite_false,cubicThetaSelectedCoefficient,hn,ite_true]
      · simp only [cubicThetaSelectedCoefficient,hn,ite_false,zero_mul]
        split_ifs <;> rfl
    _ = _ := cubicThetaPrimary_tsum _

def cubicThetaGaussDirichlet (s : ℂ) : ℂ :=
  ∑' cd : CubicThetaPrimaryPair,
    (Real.sqrt (norm cd.val.2):ℂ)*gauss cd.val.1*
      ((norm cd.val.1*norm cd.val.2^3/27:ℝ):ℂ)^(-s)

lemma cubicThetaSelected_dirichlet (s : ℂ) :
    cubicThetaDirichlet cubicThetaSelectedCoefficient (2*s-1) =
      ((3^(5/2:ℝ):ℝ):ℂ)*cubicThetaGaussDirichlet s := by
  rw [cubicThetaSelected_dirichlet_reindex,cubicThetaGaussDirichlet,←tsum_mul_left]
  apply tsum_congr
  intro cd
  rw [cubicThetaPrimary_mellin_term]
  ring

/-- The primary cubic Gauss expansion with its exact archimedean and
constant factors, on the initial half-plane of absolute convergence. -/
theorem cubicThetaSelected_gauss_mellin {s : ℂ} (hs : 3/2 < s.re) :
    mellin (fun v : ℝ => cubicThetaNonconstant cubicThetaSelectedCoefficient (0,v)) (2*s-1) =
      (1/4:ℂ)*((2*Real.pi:ℝ):ℂ)^(-2*s)*Complex.Gamma (s+1/6)*Complex.Gamma (s-1/6)*
        ((3^(5/2:ℝ):ℝ):ℂ)*cubicThetaGaussDirichlet s := by
  have hu : 2 < (2*s-1).re := by norm_num [Complex.mul_re,Complex.sub_re]; linarith
  rw [cubicThetaNonconstant_mellin (by norm_num : (0:ℝ) ≤ 81)
      cubicThetaSelectedCoefficient_norm hu,
    cubicThetaWhittaker_mellin (by linarith : 1/6 < s.re),cubicThetaSelected_dirichlet]
  ring

end CubicFirstMoment

end

end OAI
