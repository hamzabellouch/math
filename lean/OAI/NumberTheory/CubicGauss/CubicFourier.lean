import Mathlib
import OAI.NumberTheory.CubicGauss.FiniteOperators
import OAI.NumberTheory.CubicGauss.Reciprocity
import OAI.NumberTheory.CubicGram.PeriodicPoisson

namespace OAI

/-! Composite character primitivity and Fourier transforms of cubic correlations. -/

noncomputable section
open scoped BigOperators
open Module Complex UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment
open HeckeTheta

lemma cubicSymbol_one_upper {b : Eisenstein} (hb : primary b) : cubicSymbol b 1 = 1 := by
  refine primary_induction (P := fun b => cubicSymbol b 1 = 1) ?_ ?_ hb
  · exact cubicSymbol_one_lower 1
  · intro p c hp hc ih
    rw [cubicSymbol_mul_lower hp.2.ne_zero (primary_ne_zero hc),
      cubicSymbol_prime hp, cubicSymbolAtPrime_one hp, ih, one_mul]

def compositeCubicChar (b : Eisenstein) (hb : primary b) : MulChar (Residues b) ℂ where
  toFun x := cubicSymbol b (residueRepresentative b x)
  map_one' := by
    rw [cubicSymbol_congr (show Ideal.Quotient.mk (modulus b) (residueRepresentative b 1) =
      Ideal.Quotient.mk (modulus b) 1 by rw [residueRepresentative_spec, map_one])]
    exact cubicSymbol_one_upper hb
  map_mul' x y := by
    rw [cubicSymbol_congr (show
      Ideal.Quotient.mk (modulus b) (residueRepresentative b (x*y)) =
        Ideal.Quotient.mk (modulus b) (residueRepresentative b x * residueRepresentative b y) by
          rw [map_mul, residueRepresentative_spec, residueRepresentative_spec,
            residueRepresentative_spec])]
    exact cubicSymbol_mul_upper hb _ _
  map_nonunit' x hx := by
    apply cubicSymbol_eq_zero_of_not_isCoprime hb
    intro hc
    have hu := residue_isUnit_of_isCoprime hc
    rw [residueRepresentative_spec] at hu
    exact hx hu

@[simp] lemma compositeCubicChar_mk (b : Eisenstein) (hb : primary b) (v : Eisenstein) :
    compositeCubicChar b hb (Ideal.Quotient.mk (modulus b) v) = cubicSymbol b v :=
  cubicSymbol_congr (residueRepresentative_spec _ _)

lemma isCoprime_of_residue_isUnit {b v : Eisenstein}
    (h : IsUnit (Ideal.Quotient.mk (modulus b) v)) : IsCoprime b v := by
  obtain ⟨y,hy⟩ := isUnit_iff_exists_inv.mp h
  obtain ⟨w,rfl⟩ := Ideal.Quotient.mk_surjective y
  have heq : Ideal.Quotient.mk (modulus b) (v*w) = Ideal.Quotient.mk (modulus b) 1 := by
    simpa only [map_mul, map_one] using hy
  have he : b ∣ v*w-1 := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp heq)
  obtain ⟨c,hc⟩ := he
  refine ⟨-c,w,?_⟩
  linear_combination hc

lemma residue_isUnit_iff_isCoprime (b v : Eisenstein) :
    IsUnit (Ideal.Quotient.mk (modulus b) v) ↔ IsCoprime b v :=
  ⟨isCoprime_of_residue_isUnit, residue_isUnit_of_isCoprime⟩

@[simp] lemma lambdaE_coe_lambda : (lambdaE : ℂ) = lambda := by
  change (1 : ℂ) + 2 * omega = lambda
  exact lambda_eq.symm

lemma primary_isCoprime_three {b : Eisenstein} (hb : primary b) : IsCoprime b 3 := by
  obtain ⟨c,hc⟩ := hb
  refine ⟨1,-c,?_⟩
  linear_combination hc

lemma primary_isCoprime_lambda {b : Eisenstein} (hb : primary b) : IsCoprime b lambdaE := by
  apply (IsCoprime.pow_right_iff (by omega : 0 < 2)).mp
  rw [lambdaE_sq]
  exact (primary_isCoprime_three hb).neg_right

lemma residueTraceChar_lambda_shift (b : Eisenstein) (hb : b ≠ 0) :
    (residueTraceChar b hb).mulShift (Ideal.Quotient.mk (modulus b) lambdaE) =
      residueAddChar b hb := by
  ext v
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective v
  rw [AddChar.mulShift_apply, ← map_mul, residueTraceChar_mk, residueAddChar_mk]
  simp only [tracePhase, Subalgebra.coe_mul, lambdaE_coe_lambda, additivePhase]
  congr 1
  have hl : lambda ≠ 0 := by
    intro h
    have hs := lambda_sq
    rw [h] at hs
    norm_num at hs
  have he : (lambda*x/(b : ℂ))/lambda = (x : ℂ)/(b : ℂ) := by
    field_simp
  simp only [one_mul,he]

lemma composite_gauss_exact (b : Eisenstein) (hb : primary b) [Fintype (Residues b)] :
    gaussSum (compositeCubicChar b hb) (residueAddChar b (primary_ne_zero hb)) =
      (Real.sqrt (norm b) : ℂ) * gauss b := by
  rw [gauss_eq_finite_sum]
  rw [mul_inv_cancel_left₀ (show (Real.sqrt (norm b) : ℂ) ≠ 0 by
    exact_mod_cast (Real.sqrt_pos.mpr (norm_pos (primary_ne_zero hb))).ne')]
  rfl

lemma composite_gauss_norm (b : Eisenstein) (hb : primary b) (hs : Squarefree b) :
    ‖heckeGauss b (primary_ne_zero hb) (compositeCubicChar b hb)‖ =
      Real.sqrt (norm b) := by
  let : Finite (Residues b) := finite_residues (primary_ne_zero hb)
  let : Fintype (Residues b) := Fintype.ofFinite _
  have hu := residue_isUnit_of_isCoprime (primary_isCoprime_lambda hb)
  have he := gaussSum_mulShift (compositeCubicChar b hb)
    (residueTraceChar b (primary_ne_zero hb)) hu.unit
  rw [hu.unit_spec, residueTraceChar_lambda_shift, composite_gauss_exact] at he
  have hn := congrArg (fun z : ℂ => ‖z‖) he
  have hc : ‖compositeCubicChar b hb (Ideal.Quotient.mk (modulus b) lambdaE)‖ = 1 := by
    rw [compositeCubicChar_mk]
    exact norm_cubicSymbol_of_isCoprime hb (primary_isCoprime_lambda hb)
  simp only [norm_mul, hc, one_mul, norm_gauss_of_squarefree hb hs, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at hn
  simpa only [heckeGauss, tsum_fintype, gaussSum] using hn.symm

end CubicFirstMoment

namespace CubicFirstMoment
open HeckeTheta SieveFourier

lemma composite_gauss_norm_sq (b : Eisenstein) (hb : primary b) (hs : Squarefree b)
    [Fintype (Residues b)] :
    ‖gaussSum (compositeCubicChar b hb) (residueTraceChar b (primary_ne_zero hb))‖^2 =
      (Fintype.card (Residues b) : ℝ) := by
  have he : gaussSum (compositeCubicChar b hb) (residueTraceChar b (primary_ne_zero hb)) =
      heckeGauss b (primary_ne_zero hb) (compositeCubicChar b hb) := by
    simp only [gaussSum, heckeGauss, tsum_fintype]
  rw [he, composite_gauss_norm b hb hs, Real.sq_sqrt (norm_nonneg b),
    ← Nat.card_eq_fintype_card, residues_card (primary_ne_zero hb), normNat_cast]

lemma composite_fourier (b : Eisenstein) (hb : primary b) (hs : Squarefree b)
    (h : Eisenstein) :
    residueFourier b (compositeCubicChar b hb) h =
      star (cubicSymbol b h) * heckeGauss b (primary_ne_zero hb) (compositeCubicChar b hb) := by
  let : Finite (Residues b) := finite_residues (primary_ne_zero hb)
  let : Fintype (Residues b) := Fintype.ofFinite _
  have he := saturated_gauss_mulShift (compositeCubicChar b hb)
    (residueTraceChar b (primary_ne_zero hb)) (residueTraceChar_primitive b (primary_ne_zero hb))
    (composite_gauss_norm_sq b hb hs) (Ideal.Quotient.mk (modulus b) h)
  rw [← MulChar.star_apply', compositeCubicChar_mk] at he
  simpa only [residueFourier, heckeGauss, ← residueTraceChar_mul_mk b (primary_ne_zero hb),
    tsum_fintype, gaussSum, AddChar.mulShift_apply, mul_comm] using he

lemma composite_fourier_neg (b : Eisenstein) (hb : primary b) (hs : Squarefree b)
    (h : Eisenstein) :
    residueFourier b (compositeCubicChar b hb) (-h) =
      residueFourier b (compositeCubicChar b hb) h := by
  simp only [composite_fourier b hb hs, cubicSymbol_neg hb]

lemma tracePhase_neg_left (h z : ℂ) : tracePhase (-h) z = star (tracePhase h z) := by
  simp only [tracePhase, neg_mul, neg_div, star_neg]
  simp only [Complex.star_def]
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_add, Complex.conj_conj, Complex.conj_I, map_ofNat,
    Complex.conj_ofReal]
  ring

lemma residueFourier_conj (b : Eisenstein) (w : Residues b → ℂ) (h : Eisenstein) :
    residueFourier b (fun v => star (w v)) h = star (residueFourier b w (-h)) := by
  rw [residueFourier, residueFourier, tsum_star]
  congr 1
  funext v
  simp only [star_mul, Subalgebra.coe_neg, tracePhase_neg_left, star_star, mul_comm]

lemma composite_fourier_conj (b : Eisenstein) (hb : primary b) (hs : Squarefree b)
    (h : Eisenstein) :
    residueFourier b (fun v => star (compositeCubicChar b hb v)) h =
      cubicSymbol b h * star (heckeGauss b (primary_ne_zero hb) (compositeCubicChar b hb)) := by
  rw [residueFourier_conj, composite_fourier_neg b hb hs, composite_fourier b hb hs]
  simp only [star_mul, star_star, mul_comm]

end CubicFirstMoment

namespace CubicFirstMoment
open HeckeTheta

lemma cubicSymbol_congr_of_dvd {q a : Eisenstein} (ha : a ∣ q) {v w : Eisenstein}
    (h : Ideal.Quotient.mk (modulus q) v = Ideal.Quotient.mk (modulus q) w) :
    cubicSymbol a v = cubicSymbol a w := by
  exact cubicSymbol_congr (residue_eq_of_dvd_sub
    (dvd_trans ha (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h))))

def correlationResidue (a b : Eisenstein) (v : Residues (a*b)) : ℂ :=
  cubicSymbol a (residueRepresentative (a*b) v) *
    star (cubicSymbol b (residueRepresentative (a*b) v))

lemma correlationResidue_mk (a b v : Eisenstein) :
    correlationResidue a b (Ideal.Quotient.mk (modulus (a*b)) v) =
      cubicSymbol a v * star (cubicSymbol b v) := by
  simp only [correlationResidue]
  rw [cubicSymbol_congr_of_dvd (dvd_mul_right a b) (residueRepresentative_spec _ _),
    cubicSymbol_congr_of_dvd (dvd_mul_left b a) (residueRepresentative_spec _ _)]

lemma tracePhase_mix (a b : Eisenstein) (ha : a ≠ 0) (hb : b ≠ 0)
    (h v w : Eisenstein) :
    tracePhase h (((b*v+a*w : Eisenstein) : ℂ)/(a*b : Eisenstein)) =
      tracePhase h ((v : ℂ)/a) * tracePhase h ((w : ℂ)/b) := by
  have he : (((b*v+a*w : Eisenstein) : ℂ)/(a*b : Eisenstein)) =
      (v : ℂ)/a + (w : ℂ)/b := by
    simp only [Subalgebra.coe_add, Subalgebra.coe_mul]
    field_simp [coe_ne_zero ha, coe_ne_zero hb]
  rw [he, tracePhase_add_right]

lemma cubic_correlation_mix {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (hab : IsCoprime a b) (v w : Eisenstein) :
    cubicSymbol a (b*v+a*w) * star (cubicSymbol b (b*v+a*w)) =
      cubicSymbol a v * star (cubicSymbol b w) := by
  have hea : Ideal.Quotient.mk (modulus a) (b*v+a*w) =
      Ideal.Quotient.mk (modulus a) (b*v) := by
    apply residue_eq_of_dvd_sub
    simpa only [add_sub_cancel_left] using dvd_mul_right a w
  have heb : Ideal.Quotient.mk (modulus b) (b*v+a*w) =
      Ideal.Quotient.mk (modulus b) (a*w) := by
    apply residue_eq_of_dvd_sub
    simpa only [add_sub_cancel_right] using dvd_mul_right b v
  rw [cubicSymbol_congr hea, cubicSymbol_congr heb, cubicSymbol_mul_upper ha,
    cubicSymbol_mul_upper hb, cubic_reciprocity hb ha, star_mul]
  have hu : cubicSymbol a b * star (cubicSymbol a b) = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      norm_cubicSymbol_of_isCoprime ha hab]
    norm_num
  calc
    _ = (cubicSymbol a b * star (cubicSymbol a b)) *
      (cubicSymbol a v * star (cubicSymbol b w)) := by ring
    _ = _ := by rw [hu, one_mul]

lemma correlation_fourier_factor {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (hab : IsCoprime a b) (h : Eisenstein) :
    residueFourier (a*b) (correlationResidue a b) h =
      residueFourier a (compositeCubicChar a ha) h *
        residueFourier b (fun v => star (compositeCubicChar b hb v)) h := by
  have ha0 := primary_ne_zero ha
  have hb0 := primary_ne_zero hb
  let : Finite (Residues a) := finite_residues ha0
  let : Finite (Residues b) := finite_residues hb0
  let : Finite (Residues (a*b)) := finite_residues (mul_ne_zero ha0 hb0)
  let : Fintype (Residues a) := Fintype.ofFinite _
  let : Fintype (Residues b) := Fintype.ofFinite _
  let : Fintype (Residues (a*b)) := Fintype.ofFinite _
  let e := Equiv.ofBijective (residueMix a b) (residueMix_bijective ha0 hb0 hab)
  let f (v : Residues (a*b)) : ℂ := correlationResidue a b v *
    tracePhase h ((residueRepresentative (a*b) v : ℂ)/(a*b : Eisenstein))
  have he (v : Residues a × Residues b) :
      f (e v) =
        (compositeCubicChar a ha v.1 * tracePhase h ((residueRepresentative a v.1 : ℂ)/a)) *
        (star (compositeCubicChar b hb v.2) * tracePhase h ((residueRepresentative b v.2 : ℂ)/b)) := by
    have hrep : Ideal.Quotient.mk (modulus (a*b)) (residueRepresentative (a*b) (e v)) =
      Ideal.Quotient.mk (modulus (a*b))
        (b*residueRepresentative a v.1+a*residueRepresentative b v.2) :=
      residueRepresentative_spec _ _
    dsimp only [f, correlationResidue]
    rw [cubicSymbol_congr_of_dvd (dvd_mul_right a b) hrep,
      cubicSymbol_congr_of_dvd (dvd_mul_left b a) hrep,
      tracePhase_modulus_congr (a*b) (mul_ne_zero ha0 hb0) _ _ hrep,
      tracePhase_mix a b ha0 hb0,
      cubic_correlation_mix ha hb hab]
    simp only [compositeCubicChar, MulChar.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    ring
  change (∑' v, f v) = _
  rw [← e.tsum_eq f]
  simp_rw [he]
  simp only [residueFourier, tsum_fintype, Fintype.sum_prod_type,
    Finset.sum_mul_sum]

theorem cubic_correlation_fourier {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (hsa : Squarefree a) (hsb : Squarefree b) (hab : IsCoprime a b) (h : Eisenstein) :
    residueFourier (a*b) (correlationResidue a b) h =
      (heckeGauss a (primary_ne_zero ha) (compositeCubicChar a ha) *
        star (heckeGauss b (primary_ne_zero hb) (compositeCubicChar b hb))) *
      (star (cubicSymbol a h) * cubicSymbol b h) := by
  rw [correlation_fourier_factor ha hb hab, composite_fourier a ha hsa,
    composite_fourier_conj b hb hsb]
  ring

theorem cubic_correlation_poisson {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (hsa : Squarefree a) (hsb : Squarefree b) (hab : IsCoprime a b)
    (t : ℝ) (ht : 0 < t) :
    (∑' m : Eisenstein, (cubicSymbol a m * star (cubicSymbol b m)) *
      Complex.exp (-(Real.pi : ℂ) * t * (norm m : ℂ))) =
    (2 * (heckeGauss a (primary_ne_zero ha) (compositeCubicChar a ha) *
      star (heckeGauss b (primary_ne_zero hb) (compositeCubicChar b hb))) /
        ((Real.sqrt 3 : ℂ) * t * norm (a*b))) *
      ∑' h : Eisenstein,
        Complex.exp (-(4 * (Real.pi : ℂ)) / (3 * t * norm (a*b)) * (norm h : ℂ)) *
          (star (cubicSymbol a h) * cubicSymbol b h) := by
  have he := residue_theta_poisson (a*b) (mul_ne_zero (primary_ne_zero ha) (primary_ne_zero hb))
    (correlationResidue a b) t ht
  simp only [residueTheta, correlationResidue_mk] at he
  rw [he]
  simp_rw [cubic_correlation_fourier ha hb hsa hsb hab,
    mul_left_comm (Complex.exp _) (heckeGauss a _ _ * star (heckeGauss b _ _))]
  rw [tsum_mul_left]
  ring

end CubicFirstMoment
end

end OAI
