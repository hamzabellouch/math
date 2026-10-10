import Mathlib
import OAI.NumberTheory.CubicGauss.Eisenstein
import OAI.NumberTheory.CubicGauss.GaussianPoisson

namespace OAI

/-! Eisenstein lattice coordinates, dual trace phases and Gaussian Poisson summation. -/

noncomputable section
open scoped BigOperators
open Module Complex UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment.HeckeTheta
def latticeEquiv : ℤ × ℤ ≃ Eisenstein :=
  Equiv.ofBijective (fun p => ofCoords p.2 p.1)
    ⟨fun _ _ h => Prod.swap_injective (ofCoords_injective h),
      fun z => by obtain ⟨⟨a,b⟩, h⟩ := ofCoords_surjective z; exact ⟨(b,a), h⟩⟩

@[simp] lemma latticeEquiv_apply (n m : ℤ) : latticeEquiv (n, m) = ofCoords m n := rfl

lemma translated_coordinates_norm (m n : ℤ) (x y : ℝ) :
    Complex.normSq ((ofCoords m n : ℂ) + ((x : ℂ) + y * omega)) =
      hexQ ((m : ℝ) + x) ((n : ℝ) + y) := by
  have heq : (ofCoords m n : ℂ) + ((x : ℂ) + y * omega) =
      (((m : ℝ) + x : ℝ) : ℂ) + (((n : ℝ) + y : ℝ) : ℂ) * omega := by
    simp only [ofCoords_coe]
    push_cast
    ring
  rw [heq, real_coordinates_norm]
  rfl

lemma lattice_gaussian_summable (t : ℝ) (z : ℂ) (ht : 0 < t) :
    Summable (fun a : Eisenstein => Complex.exp (-(Real.pi : ℂ) * t *
      (Complex.normSq ((a : ℂ) + z) : ℂ))) := by
  rw [← latticeEquiv.summable_iff]
  convert hex_gaussian_summable t (z.re + z.im / Real.sqrt 3) (2*z.im/Real.sqrt 3) ht using 1
  ext nm
  change Complex.exp (-(Real.pi : ℂ) * t *
    (Complex.normSq ((ofCoords nm.2 nm.1 : ℂ) + z) : ℂ)) = _
  conv_lhs => rw [complex_coordinates z, translated_coordinates_norm]

 
def lambda : ℂ := (Real.sqrt 3 : ℂ) * Complex.I

lemma lambda_eq : lambda = 1 + 2 * omega := by
  rw [omega_eq]
  dsimp [lambda]
  push_cast
  ring

lemma lambda_sq : lambda ^ 2 = -3 := by
  simp only [lambda, mul_pow, Complex.I_sq, ← Complex.ofReal_pow]
  norm_num [Real.sq_sqrt]

lemma trace_div_lambda_coordinates (a b : ℝ) :
    (((a : ℂ) + b * omega) / lambda) +
        star (((a : ℂ) + b * omega) / lambda) = (b : ℂ) := by
  apply Complex.ext
  · simp [lambda, Complex.div_re, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring_nf
    norm_num [Real.sq_sqrt]
    ring
  · simp only [Complex.add_im, Complex.star_def, Complex.conj_im, Complex.ofReal_im,
      add_neg_cancel]

 
def tracePhase (b z : ℂ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * I * (b * z / lambda + star (b * z / lambda)))

lemma norm_tracePhase (b z : ℂ) : ‖tracePhase b z‖ = 1 := by
  have hi : (b * z / lambda + star (b * z / lambda)).im = 0 := by
    simp only [Complex.add_im, Complex.star_def, Complex.conj_im, add_neg_cancel]
  rw [tracePhase, Complex.norm_exp, Complex.mul_re, hi]
  simp [Complex.mul_re]

lemma dual_phase (h k : ℤ) (x y : ℝ) :
    tracePhase (ofCoords (h+k) h) ((x : ℂ) + y * omega) =
      Complex.exp (2 * (Real.pi : ℂ) * I * ((h : ℂ) * x + (k : ℂ) * y)) := by
  have hmul : (ofCoords (h+k) h : ℂ) * ((x : ℂ) + y * omega) =
      (((h+k : ℤ) : ℝ) * x - (h : ℝ) * y : ℝ) +
        (((h : ℝ) * x + (k : ℝ) * y : ℝ) : ℂ) * omega := by
    simp only [ofCoords_coe]
    push_cast
    have hw : omega ^ 2 = -omega - 1 := by linear_combination omega_quadratic
    ring_nf
    rw [hw]
    ring
  simp only [ofCoords_coe] at hmul
  simp only [tracePhase, ofCoords_coe]
  rw [hmul, trace_div_lambda_coordinates]
  push_cast
  rfl

 
def dualEquiv : ℤ × ℤ ≃ Eisenstein :=
  Equiv.ofBijective (fun p => ofCoords (p.1 + p.2) p.1)
    ⟨fun ⟨h,k⟩ ⟨h',k'⟩ he => by
      obtain ⟨ha,hb⟩ := coordinates_unique (congrArg (fun a : Eisenstein => (a : ℂ)) he)
      exact Prod.ext hb (by omega),
    fun z => by
      obtain ⟨⟨a,b⟩, hz⟩ := ofCoords_surjective z
      exact ⟨(b,a-b), by simpa using hz⟩⟩

@[simp] lemma dualEquiv_apply (h k : ℤ) : dualEquiv (h,k) = ofCoords (h+k) h := rfl

lemma dual_norm (h k : ℤ) :
    norm (dualEquiv (h,k)) = (h : ℝ)^2 + (h : ℝ) * k + (k : ℝ)^2 := by
  simp only [norm, dualEquiv_apply, ofCoords_coe, coordinates_norm]
  push_cast
  ring

lemma lattice_gaussian_phase_summable (a : ℝ) (z : ℂ) (ha : 0 < a) :
    Summable (fun b : Eisenstein => Complex.exp (-(Real.pi : ℂ) * a * (norm b : ℂ)) *
      tracePhase b z) := by
  have hf := (lattice_gaussian_summable a 0 ha).norm
  simp only [add_zero] at hf
  refine hf.of_norm_bounded fun b => le_of_eq ?_
  rw [norm_mul, norm_tracePhase, mul_one]
  rfl

lemma lattice_gaussian_poisson_coords (t x y : ℝ) (ht : 0 < t) :
    (∑' a : Eisenstein, Complex.exp (-(Real.pi : ℂ) * t *
      (Complex.normSq ((a : ℂ) + ((x : ℂ) + y * omega)) : ℂ))) =
    (2 / ((Real.sqrt 3 : ℂ) * t)) * ∑' b : Eisenstein,
      Complex.exp (-(4 * (Real.pi : ℂ)) / (3 * t) * (norm b : ℂ)) *
        tracePhase b ((x : ℂ) + y * omega) := by
  have hp := lattice_gaussian_summable t ((x : ℂ) + y * omega) ht
  have hd : Summable (fun b : Eisenstein =>
      Complex.exp (-(4 * (Real.pi : ℂ)) / (3 * t) * (norm b : ℂ)) *
        tracePhase b ((x : ℂ) + y * omega)) := by
    convert lattice_gaussian_phase_summable (4 / (3*t)) ((x : ℂ) + y * omega)
      (by positivity) using 1
    ext b
    congr 1
    congr 1
    push_cast
    ring
  rw [← latticeEquiv.tsum_eq (fun a : Eisenstein =>
    Complex.exp (-(Real.pi : ℂ) * t *
      (Complex.normSq ((a : ℂ) + ((x : ℂ) + y * omega)) : ℂ)))]
  have hpsum := ((latticeEquiv.summable_iff).mpr hp).tsum_prod
  simp only [Function.comp_apply] at hpsum
  rw [hpsum]
  simp only [latticeEquiv_apply, translated_coordinates_norm]
  rw [eisenstein_gaussian_poisson t x y ht]
  congr 1
  rw [← dualEquiv.tsum_eq (fun b : Eisenstein =>
      Complex.exp (-(4 * (Real.pi : ℂ)) / (3 * t) * (norm b : ℂ)) *
        tracePhase b ((x : ℂ) + y * omega))]
  have hdsum := ((dualEquiv.summable_iff).mpr hd).tsum_prod
  simp only [Function.comp_apply] at hdsum
  rw [hdsum]
  apply tsum_congr
  intro h
  apply tsum_congr
  intro k
  rw [dual_norm]
  simp only [dualEquiv_apply, dual_phase]
  push_cast
  rfl

 

theorem lattice_gaussian_poisson (t : ℝ) (z : ℂ) (ht : 0 < t) :
    (∑' a : Eisenstein, Complex.exp (-(Real.pi : ℂ) * t *
      (Complex.normSq ((a : ℂ) + z) : ℂ))) =
    (2 / ((Real.sqrt 3 : ℂ) * t)) * ∑' b : Eisenstein,
      Complex.exp (-(4 * (Real.pi : ℂ)) / (3 * t) * (norm b : ℂ)) * tracePhase b z := by
  have h := lattice_gaussian_poisson_coords t (z.re + z.im / Real.sqrt 3)
    (2 * z.im / Real.sqrt 3) ht
  rw [← complex_coordinates z] at h
  exact h
end CubicFirstMoment.HeckeTheta
end

end OAI
