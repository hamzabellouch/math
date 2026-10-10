import OAI.NumberTheory.CubicMoment.Estimates.HuxleyGaussianPoisson
import OAI.NumberTheory.CubicMoment.Estimates.HuxleyCoordinateGeometry

namespace OAI

/-! Absolute convergence and the two-coordinate theta identity. -/
noncomputable section
namespace CubicFirstMoment

def huxleyCoordinateEquiv : (ℤ × ℤ) ≃ Eisenstein :=
  Equiv.ofBijective (fun p => ofCoords p.1 p.2)
    ⟨ofCoords_injective,ofCoords_surjective⟩

def huxleyDualCoordinateEquiv : (ℤ × ℤ) ≃ Eisenstein :=
  Equiv.ofBijective (fun p => ofCoords (p.1+p.2) p.1) (by
    constructor
    · intro p q hpq
      have h : (p.1+p.2,p.1) = (q.1+q.2,q.1) := ofCoords_injective hpq
      have h1 : p.1+p.2 = q.1+q.2 := congrArg Prod.fst h
      have h2 : p.1 = q.1 := congrArg Prod.snd h
      apply Prod.ext h2
      omega
    · intro z
      obtain ⟨⟨a,b⟩,h⟩ := ofCoords_surjective z
      exact ⟨(b,a-b),by simpa using h⟩)

lemma summable_real_gaussian_shift {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    Summable (fun n : ℤ => Real.exp (-Real.pi*a*((n:ℝ)-ξ)^2)) := by
  have h := summable_integer_quadratic_exp
    ((-Real.pi*a:ℝ):ℂ) ((2*Real.pi*a*ξ:ℝ):ℂ) ((-Real.pi*a*ξ^2:ℝ):ℂ)
    (by simp only [Complex.ofReal_re]; exact mul_neg_of_neg_of_pos (by linarith [Real.pi_pos]) ha)
  convert (Complex.hasSum_re h.hasSum).summable using 1
  ext n
  rw [← Complex.ofReal_intCast]
  norm_cast
  congr 1
  push_cast
  ring

def huxleyGaussianFactor (a ξ : ℝ) (n : ℤ) : ℂ :=
  Complex.exp ((-Real.pi*a*(n:ℝ)^2:ℝ):ℂ)*
    Complex.exp (((2*Real.pi*ξ*(n:ℝ):ℝ):ℂ)*Complex.I)

lemma norm_huxleyGaussianFactor (a ξ : ℝ) (n : ℤ) :
    ‖huxleyGaussianFactor a ξ n‖ = Real.exp (-Real.pi*a*(n:ℝ)^2) := by
  simp only [huxleyGaussianFactor,norm_mul,Complex.norm_exp,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,
    sub_zero,Real.exp_zero,mul_one]

lemma summable_norm_huxleyGaussianFactor {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    Summable (fun n => ‖huxleyGaussianFactor a ξ n‖) := by
  simp only [norm_huxleyGaussianFactor]
  simpa using summable_real_gaussian_shift ha 0

lemma huxley_gaussian_two_coordinate_poisson {a : ℝ} (ha : 0 < a) (ξ η : ℝ) :
    (∑' p : ℤ × ℤ, huxleyGaussianFactor a ξ p.1*huxleyGaussianFactor a η p.2) =
      ((1/a:ℝ):ℂ)*∑' p : ℤ × ℤ,
        ((Real.exp (-Real.pi/a*((p.1:ℝ)-ξ)^2)*
          Real.exp (-Real.pi/a*((p.2:ℝ)-η)^2):ℝ):ℂ) := by
  rw [← tsum_mul_tsum_of_summable_norm
    (summable_norm_huxleyGaussianFactor ha ξ) (summable_norm_huxleyGaussianFactor ha η)]
  change (∑' n, huxleyGaussianFactor a ξ n)*(∑' n, huxleyGaussianFactor a η n) = _
  rw [show (∑' n, huxleyGaussianFactor a ξ n) = _ from gaussian_coordinate_poisson ha ξ,
    show (∑' n, huxleyGaussianFactor a η n) = _ from gaussian_coordinate_poisson ha η]
  have hs (x : ℝ) : Summable (fun n : ℤ =>
      ‖Complex.exp ((-Real.pi/a*((n:ℝ)-x)^2:ℝ):ℂ)‖) := by
    simp only [Complex.norm_exp,Complex.ofReal_re]
    simpa only [div_eq_mul_inv,mul_assoc] using summable_real_gaussian_shift (inv_pos.mpr ha) x
  have hprod := tsum_mul_tsum_of_summable_norm (hs ξ) (hs η)
  have hc : ((1/Real.sqrt a:ℝ):ℂ)*((1/Real.sqrt a:ℝ):ℂ) = ((1/a:ℝ):ℂ) := by
    norm_cast
    rw [← pow_two,div_pow,Real.sq_sqrt ha.le]
    norm_num
  calc
    _ = (((1/Real.sqrt a:ℝ):ℂ)*((1/Real.sqrt a:ℝ):ℂ))*
        ((∑' n : ℤ, Complex.exp ((-Real.pi/a*((n:ℝ)-ξ)^2:ℝ):ℂ)) *
        (∑' n : ℤ, Complex.exp ((-Real.pi/a*((n:ℝ)-η)^2:ℝ):ℂ))) := by ring
    _ = _ := by
      rw [hc,hprod]
      congr 1
      apply tsum_congr
      intro p
      simp only [Complex.ofReal_mul,Complex.ofReal_exp]

end CubicFirstMoment

end

end OAI
