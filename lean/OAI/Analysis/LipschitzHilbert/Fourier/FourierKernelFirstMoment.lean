import OAI.Analysis.LipschitzHilbert.Fourier.SignedAnnularSymbol
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace OAI

/-! A quantitative first absolute moment from the zeroth and third
L1 derivatives of a Schwartz multiplier. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

def schwartzDerivative : ℕ → SchwartzMap ℝ ℂ → SchwartzMap ℝ ℂ
  | 0, q => q
  | r+1, q => SchwartzMap.derivCLM ℂ ℂ (schwartzDerivative r q)

theorem schwartzDerivative_apply (r : ℕ) (q : SchwartzMap ℝ ℂ) :
    (schwartzDerivative r q : ℝ → ℂ)=iteratedDeriv r q := by
  induction r with
  | zero => rfl
  | succ r ih =>
    funext x
    change deriv (schwartzDerivative r q) x=iteratedDeriv (r+1) q x
    rw [ih,iteratedDeriv_succ]

theorem fourier_schwartzDerivative (r : ℕ) (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    (𝓕 (schwartzDerivative r q)) x=
      ((2*Real.pi*Complex.I*(x:ℂ))^r)*(𝓕 q) x := by
  induction r with
  | zero => simp only [schwartzDerivative,pow_zero,one_mul]
  | succ r ih =>
    have hd := congrFun (Real.fourier_deriv (schwartzDerivative r q).integrable
      (schwartzDerivative r q).differentiable
      (SchwartzMap.derivCLM ℂ ℂ (schwartzDerivative r q)).integrable) x
    change (𝓕 (SchwartzMap.derivCLM ℂ ℂ (schwartzDerivative r q))) x=
      (2*Real.pi*Complex.I*(x:ℂ))* (𝓕 (schwartzDerivative r q)) x at hd
    rw [schwartzDerivative,hd,ih]
    ring

theorem schwartz_fourier_norm_le_l1 (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    ‖(𝓕 q) x‖≤∫ y, ‖q y‖ := by
  change ‖𝓕 (q : ℝ → ℂ) x‖≤_
  exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

theorem schwartz_fourier_weighted_norm (r : ℕ) (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    (2*Real.pi)^r*|x|^r*‖(𝓕 q) x‖≤∫ y, ‖schwartzDerivative r q y‖ := by
  have hb := schwartz_fourier_norm_le_l1 (schwartzDerivative r q) x
  rw [fourier_schwartzDerivative,norm_mul,norm_pow] at hb
  have hn : ‖2*Real.pi*Complex.I*(x:ℂ)‖=2*Real.pi*|x| := by
    simp only [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos Real.pi_pos,Complex.norm_I,mul_one]
  rw [hn,mul_pow] at hb
  exact hb

theorem firstMoment_bound_of_decay (K : ℝ → ℂ) (hK : Measurable K)
    (B C : ℝ) (hB : 0≤B) (hC : 0≤C)
    (hzero : ∀ x, ‖K x‖≤B) (hthree : ∀ x, |x|^3*‖K x‖≤C) :
    Integrable (fun x => |x| *‖K x‖) ∧
      (∫ x, |x| *‖K x‖)≤2*(B+C)*Real.pi := by
  have hdom (x : ℝ) : |x| *‖K x‖≤2*(B+C)*(1+x^2)⁻¹ := by
    have hp : 0<1+x^2 := by positivity
    rw [←div_eq_mul_inv,le_div_iff₀ hp]
    have hx2 : x^2=|x|^2 := (sq_abs x).symm
    rw [hx2]
    by_cases hx : |x|≤1
    · have ha : |x| *‖K x‖≤B :=
        (mul_le_mul_of_nonneg_right hx (norm_nonneg _)).trans (by simpa using hzero x)
      have hs : |x|^2≤1 := by nlinarith [abs_nonneg x]
      calc
        _ ≤ B*(1+|x|^2) := mul_le_mul_of_nonneg_right ha (by positivity)
        _ ≤ 2*B := by nlinarith
        _ ≤ _ := by linarith
    · have hx' : 1≤|x| := le_of_not_ge hx
      have hcube : |x|≤|x|^3 := by nlinarith [sq_nonneg (|x|-1)]
      have ha : |x| *‖K x‖≤C :=
        (mul_le_mul_of_nonneg_right hcube (norm_nonneg _)).trans (hthree x)
      nlinarith only [ha,hthree x,hB]
  have hint : Integrable (fun x : ℝ => 2*(B+C)*(1+x^2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul (2*(B+C))
  have hmeas : AEStronglyMeasurable (fun x => |x| *‖K x‖) :=
    (show Measurable (fun x : ℝ => |x| *‖K x‖) from
      continuous_abs.measurable.mul hK.norm).aestronglyMeasurable
  have hi : Integrable (fun x => |x| *‖K x‖) := hint.mono' hmeas
    (Filter.Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (abs_nonneg x) (norm_nonneg _))] using hdom x))
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ x : ℝ, 2*(B+C)*(1+x^2)⁻¹ := integral_mono hi hint hdom
    _ = _ := by rw [integral_const_mul,integral_univ_inv_one_add_sq]

theorem schwartz_fourier_firstMoment_bound (q : SchwartzMap ℝ ℂ) :
    (∫ x, |x| *‖(𝓕 q) x‖)≤
      2*((∫ y, ‖q y‖)+(∫ y, ‖schwartzDerivative 3 q y‖)/(2*Real.pi)^3)*Real.pi := by
  have hp : 0<(2*Real.pi)^3 := by positivity
  apply (firstMoment_bound_of_decay (𝓕 q : SchwartzMap ℝ ℂ) (𝓕 q : SchwartzMap ℝ ℂ).continuous.measurable
    (∫ y, ‖q y‖) ((∫ y, ‖schwartzDerivative 3 q y‖)/(2*Real.pi)^3)
    (integral_nonneg (fun _ => norm_nonneg _)) (by positivity)
    (schwartz_fourier_norm_le_l1 q) (fun x => ?_)).2
  apply (le_div_iff₀ hp).2
  have h := schwartz_fourier_weighted_norm 3 q x
  nlinarith only [h]

end LipschitzHilbert.PacketRepresentation

end

end OAI
