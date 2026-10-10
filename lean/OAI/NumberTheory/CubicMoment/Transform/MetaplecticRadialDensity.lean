import OAI.NumberTheory.CubicMoment.Transform.MetaplecticTotient
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticRadialCentered

namespace OAI

/-! Identification of the radial lattice density with the literal
metaplectic residue constant. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma integral_radial_model_weight (W : ℝ → ℂ) :
    (∫ x in Ioi (0:ℝ), ((x^(-1/6:ℝ):ℝ):ℂ)*W x) = mellin W (5/6) := by
  unfold mellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [Complex.ofReal_cpow hx.le]
  norm_num

lemma primaryCoprimeRadialMain_eq {r : Eisenstein} (hr : primary r) (hsr : Squarefree r)
    (W : ℝ → ℂ) (Y : ℝ) :
    primaryCoprimeRadialMain r W Y =
      (((2*Real.pi*Y/(9*Real.sqrt 3))*(metaplecticTotient r/norm r):ℝ):ℂ)*
        (∫ x in Ioi (0:ℝ), W x) := by
  have hsum : (∑ s ∈ (primaryPrimeFactors r).powerset,
      ((idealMoebius (∏ p ∈ s,p):ℝ)/norm (∏ p ∈ s,p):ℝ)) =
      metaplecticTotient r/norm r := primary_moebius_density hr hsr
  unfold primaryCoprimeRadialMain primaryRadialMain
  calc
    _ = (∑ s ∈ (primaryPrimeFactors r).powerset,
        (((idealMoebius (∏ p ∈ s,p):ℝ)/norm (∏ p ∈ s,p):ℝ):ℂ))*
          (((2*Real.pi*Y/(9*Real.sqrt 3)):ℝ):ℂ)*(∫ x in Ioi (0:ℝ), W x) := by
      rw [Finset.sum_mul,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _
      push_cast
      ring
    _ = _ := by rw [←Complex.ofReal_sum,hsum,Complex.ofReal_mul]; ring

lemma cStar_primary_area_constant :
    cStar*(2*Real.pi/(9*Real.sqrt 3)) = metaplecticA0 := by
  have hg : Real.Gamma (2/3:ℝ) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have hs : Real.sqrt (3:ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have h3 : (3:ℝ)^(7/2:ℝ) = 27*Real.sqrt 3 := by
    rw [show (7/2:ℝ) = 3+1/2 by norm_num,Real.rpow_add (by norm_num),
      Real.rpow_ofNat,←Real.sqrt_eq_rpow]
    norm_num
  have hp : (2*Real.pi)^(5/3:ℝ) = (2*Real.pi)^(2/3:ℝ)*(2*Real.pi) := by
    rw [show (5/3:ℝ) = 2/3+1 by norm_num,Real.rpow_add (by positivity),Real.rpow_one]
  rw [cStar,metaplecticA0,h3,hp]
  field_simp
  ring

lemma metaplectic_radial_density_scale {N U : ℝ} (hN : 0 < N) (hU : 0 < U)
    (φ : ℝ) :
    cStar*(N*U)^(-1/6:ℝ)*(2*Real.pi*U/(9*Real.sqrt 3))*(φ/N) =
      metaplecticA0*U^(5/6:ℝ)*φ*N^(-7/6:ℝ) := by
  have hUpow : U^(-1/6:ℝ)*U = U^(5/6:ℝ) := by
    calc
      _ = U^(-1/6:ℝ)*U^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_add hU]; norm_num
  have hNpow : N^(-1/6:ℝ)/N = N^(-7/6:ℝ) := by
    calc
      _ = N^(-1/6:ℝ)/N^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_sub hN]; norm_num
  calc
    _ = (cStar*(2*Real.pi/(9*Real.sqrt 3)))*(U^(-1/6:ℝ)*U)*φ*(N^(-1/6:ℝ)/N) := by
      rw [Real.mul_rpow hN.le hU.le]
      ring
    _ = _ := by rw [cStar_primary_area_constant,hUpow,hNpow]

end CubicFirstMoment

end

end OAI
