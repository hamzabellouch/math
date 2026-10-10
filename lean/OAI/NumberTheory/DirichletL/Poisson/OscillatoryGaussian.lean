import OAI.NumberTheory.DirichletL.Poisson.GaussianMoments

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic

namespace OscSpecial

theorem oscillatory_gaussian_poisson {η a b : ℝ}
    (hη : 0 < η) (hq : 0 < q a b) :
    (∑' z : ℤ × ℤ, RankTwoComplex.binaryGaussian (A η a b) (B η a b) (D η a b) z) =
      (1 / ((R η a b : ℂ) ^ (1 / 2 : ℂ))) *
        ∑' z : ℤ × ℤ,
          RankTwoComplex.dualGaussian (A η a b) (B η a b) (D η a b) z := by
  have hq0 : q a b ≠ 0 := hq.ne'
  have ha : 0 < (A η a b).re := by
    rw [(coefficient_re η a b hq0).1]
    exact hη
  have hR : 0 < R η a b := by
    unfold R
    positivity
  exact binary_gaussian_poisson_real_det ha hR
    (oscillatory_determinant η a b hq0)
    (real_positive_definite hη hq0)

noncomputable def r (η a b : ℝ) : ℝ := 1 + 3 * q a b * η ^ 2 / 16

theorem r_pos {η a b : ℝ} (hη : 0 < η) (hq : 0 < q a b) :
    0 < r η a b := by
  unfold r
  positivity

private theorem inverseForm_explicit {η a b : ℝ} (hη : 0 < η) (hq : 0 < q a b)
    (z : ℤ × ℤ) :
    inverseForm (A η a b) (B η a b) (D η a b) (R η a b) z =
      ((η : ℂ) * (q a b : ℂ) / (4 * (r η a b : ℂ))) *
        ((z.1 : ℂ) ^ 2 + (z.1 : ℂ) * (z.2 : ℂ) + (z.2 : ℂ) ^ 2) +
      Complex.I / (2 * (r η a b : ℂ)) *
        (((a-b : ℝ) : ℂ) * (z.1 : ℂ) ^ 2 +
          2 * (a : ℂ) * (z.1 : ℂ) * (z.2 : ℂ) +
          (b : ℂ) * (z.2 : ℂ) ^ 2) := by
  have hq0 : q a b ≠ 0 := hq.ne'
  have hqc : (q a b : ℂ) ≠ 0 := by exact_mod_cast hq0
  have hr0 : r η a b ≠ 0 := (r_pos hη hq).ne'
  have hrc : (r η a b : ℂ) ≠ 0 := by exact_mod_cast hr0
  have hR : 0 < R η a b := by unfold R; positivity
  have hRc : (R η a b : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hRexpr : (R η a b : ℂ) = 4 * (r η a b : ℂ) / (q a b : ℂ) := by
    simp [R, r]
    field_simp [hqc]
    ring
  have hqexpr : (q a b : ℂ) = (a : ℂ) ^ 2 - (a : ℂ) * (b : ℂ) + (b : ℂ) ^ 2 := by
    simp [q]
  have hrexpr : (r η a b : ℂ) = 1 + 3 * (q a b : ℂ) * (η : ℂ) ^ 2 / 16 := by
    simp [r]
  dsimp [inverseForm, A, B, D]
  rw [hRexpr]
  field_simp [hqc, hrc]
  push_cast
  ring

theorem dualGaussian_explicit {η a b : ℝ} (hη : 0 < η) (hq : 0 < q a b)
    (z : ℤ × ℤ) :
    RankTwoComplex.dualGaussian (A η a b) (B η a b) (D η a b) z =
      Complex.exp (-(Real.pi : ℂ) *
        (((η : ℂ) * (q a b : ℂ) / (4 * (r η a b : ℂ))) *
          ((z.1 : ℂ) ^ 2 + (z.1 : ℂ) * (z.2 : ℂ) + (z.2 : ℂ) ^ 2) +
         Complex.I / (2 * (r η a b : ℂ)) *
          (((a-b : ℝ) : ℂ) * (z.1 : ℂ) ^ 2 +
            2 * (a : ℂ) * (z.1 : ℂ) * (z.2 : ℂ) +
            (b : ℂ) * (z.2 : ℂ) ^ 2))) := by
  have hq0 : q a b ≠ 0 := hq.ne'
  have hA0 : A η a b ≠ 0 := by
    intro h
    have hAr : (A η a b).re = η := (coefficient_re η a b hq0).1
    simp [h] at hAr
    linarith
  have hR : 0 < R η a b := by unfold R; positivity
  rw [dualGaussian_inverseForm hA0 hR.ne'
    (oscillatory_determinant η a b hq0) z,
    inverseForm_explicit hη hq z]

end OscSpecial

namespace ActualEisensteinCubic

section

open EisensteinEmbedding ConcreteTraceCRT Complex

theorem dual_quadratic_trace_coeff (a b k l : ℤ) :
    (ActualEisensteinCoordinates.coords
      (ActualEisensteinCoordinates.eval a b *
        (ActualEisensteinCoordinates.eval (k+l) k)^2)).2 =
      (a-b)*k^2+2*a*k*l+b*l^2 := by
  rw [pow_two, ActualEisensteinCoordinates.eval_mul (k+l) k (k+l) k]
  rw [ActualEisensteinCoordinates.eval_mul]
  rw [ShortDraftLatticeCount.coords_eval]
  ring

private theorem coords_neg_second (z : O) :
    (ActualEisensteinCoordinates.coords (-z)).2 =
      -(ActualEisensteinCoordinates.coords z).2 := by
  let a := (ActualEisensteinCoordinates.coords z).1
  let b := (ActualEisensteinCoordinates.coords z).2
  have hz : z = ActualEisensteinCoordinates.eval a b :=
    (ActualEisensteinCoordinates.eval_coords z).symm
  rw [hz]
  have hneg : -ActualEisensteinCoordinates.eval a b =
      ActualEisensteinCoordinates.eval (-a) (-b) := by
    simp only [ActualEisensteinCoordinates.eval]
    push_cast
    ring
  rw [hneg, ShortDraftLatticeCount.coords_eval,
    ShortDraftLatticeCount.coords_eval]

theorem breveE_dual_quadratic_real_scale
    (r : ℝ) (a b k l : ℤ) :
    ShortDraftTrace.breveE
      (eisEmbedding (-(ActualEisensteinCoordinates.eval a b *
        (ActualEisensteinCoordinates.eval (k+l) k)^2)) /
        eisLam / ((4*r : ℝ) : ℂ)) =
      Complex.exp (-(2 * Real.pi * Complex.I *
        (((a-b)*k^2+2*a*k*l+b*l^2 : ℤ) : ℂ)) /
        ((4*r : ℝ) : ℂ)) := by
  rw [breveE_real_trace_of_O]
  have hneg : (ActualEisensteinCoordinates.coords
      (-(ActualEisensteinCoordinates.eval a b *
        (ActualEisensteinCoordinates.eval (k+l) k)^2))).2 =
      -((a-b)*k^2+2*a*k*l+b*l^2) := by
    have hp := dual_quadratic_trace_coeff a b k l
    rw [coords_neg_second]
    simpa using congrArg Neg.neg hp
  rw [hneg]
  congr 1
  push_cast
  ring_nf

end

section

open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex

theorem original_abel_gamma_limit (c : O) (hc : c ≠ 0) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    Tendsto (fun η : ℝ => (η : ℂ) *
      (∑' z : O,
        (eisTraceModChar ShortDraftTrace.breveE
          ConcreteBreveE.breveE_period_coordinates c hc)
          (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
        Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
          (‖eisEmbedding z‖ ^ 2 : ℂ))))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((((2 / (Real.sqrt 3 * ‖eisEmbedding c‖) : ℝ) : ℂ) *
        quadraticGammaO c hc))) := by
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let a := (ActualEisensteinCoordinates.coords c).1
  let b := (ActualEisensteinCoordinates.coords c).2
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc
  let S : ℂ := ∑ r : O ⧸ Ideal.span {c}, ψ (r ^ 2)
  have hceq : c = ActualEisensteinCoordinates.eval a b :=
    (ActualEisensteinCoordinates.eval_coords c).symm
  have hq : (((a*a-a*b+b*b : ℤ) : ℝ)) = ‖eisEmbedding c‖ ^ 2 := by
    calc
      (((a*a-a*b+b*b : ℤ) : ℝ)) =
          ‖eisEmbedding (ActualEisensteinCoordinates.eval a b)‖ ^ 2 :=
        (eisEmbedding_eval_norm_sq a b).symm
      _ = ‖eisEmbedding c‖ ^ 2 := by rw [← hceq]
  have hn : ‖eisEmbedding c‖ ≠ 0 :=
    ne_of_gt (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero hc))
  have hnC : (‖eisEmbedding c‖ : ℂ) ≠ 0 := by exact_mod_cast hn
  have hsqrtC : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 3)))
  have hgamma : quadraticGammaO c hc = S / (‖eisEmbedding c‖ : ℂ) := rfl
  have h := original_abel_gauss_limit c hc
  convert h using 1
  rw [hgamma, hq]
  push_cast
  field_simp [hnC, hsqrtC]
  dsimp only [S]

end

open EisensteinEmbedding ConcreteTraceCRT Complex

theorem actual_oscillatory_binary_coordinate
    (a b m n : ℤ) (hc : ActualEisensteinCoordinates.eval a b ≠ 0)
    (η : ℝ) :
    let c : O := ActualEisensteinCoordinates.eval a b
    let z : O := ActualEisensteinCoordinates.eval m n
    (eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates c hc)
        (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
      Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
        (‖eisEmbedding z‖ ^ 2 : ℂ)) =
      RankTwoComplex.binaryGaussian
        (OscSpecial.A η (a : ℝ) (b : ℝ))
        (OscSpecial.B η (a : ℝ) (b : ℝ))
        (OscSpecial.D η (a : ℝ) (b : ℝ)) (m,n) := by
  have hqZ : a*a-a*b+b*b ≠ 0 :=
    (coordinate_norm_pos_of_nonzero a b hc).ne'
  have hqC : (((a*a-a*b+b*b : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast hqZ
  dsimp only
  rw [actual_oscillatory_gaussian_coordinate a b m n hc η]
  unfold RankTwoComplex.binaryGaussian OscSpecial.A OscSpecial.B
    OscSpecial.D OscSpecial.q
  congr 1
  push_cast
  field_simp [hqC]
  ring

theorem actual_oscillatory_sum_eq_binary
    (a b : ℤ) (hc : ActualEisensteinCoordinates.eval a b ≠ 0)
    (η : ℝ) :
    let c : O := ActualEisensteinCoordinates.eval a b
    (∑' z : O,
      (eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates c hc)
        (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
      Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
        (‖eisEmbedding z‖ ^ 2 : ℂ))) =
      ∑' p : ℤ × ℤ,
        RankTwoComplex.binaryGaussian
          (OscSpecial.A η (a : ℝ) (b : ℝ))
          (OscSpecial.B η (a : ℝ) (b : ℝ))
          (OscSpecial.D η (a : ℝ) (b : ℝ)) p := by
  let W : O → ℂ := fun z =>
    (eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates
        (ActualEisensteinCoordinates.eval a b) hc)
      (Ideal.Quotient.mk (Ideal.span {ActualEisensteinCoordinates.eval a b}) z ^ 2) *
    Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
      (‖eisEmbedding z‖ ^ 2 : ℂ))
  have h := (latticeCoordEquiv.symm.tsum_eq W).symm
  simpa only [W, latticeCoordEquiv] using
    (show (∑' z : O, W z) =
      ∑' p : ℤ × ℤ,
        RankTwoComplex.binaryGaussian
          (OscSpecial.A η (a : ℝ) (b : ℝ))
          (OscSpecial.B η (a : ℝ) (b : ℝ))
          (OscSpecial.D η (a : ℝ) (b : ℝ)) p from by
      calc
        (∑' z : O, W z) = ∑' p : ℤ × ℤ, W (latticeCoordEquiv.symm p) := h
        _ = _ := by
          apply tsum_congr
          intro p
          have hp : latticeCoordEquiv.symm p =
              ActualEisensteinCoordinates.eval p.1 p.2 := rfl
          rw [hp]
          exact actual_oscillatory_binary_coordinate a b p.1 p.2 hc η)

def dualFrequencyEquiv : (ℤ × ℤ) ≃ O where
  toFun p := ActualEisensteinCoordinates.eval (p.1 + p.2) p.1
  invFun y := ((ActualEisensteinCoordinates.coords y).2,
    (ActualEisensteinCoordinates.coords y).1 -
      (ActualEisensteinCoordinates.coords y).2)
  left_inv p := by
    rcases p with ⟨k,l⟩
    simp only [  ShortDraftLatticeCount.coords_eval]
    ext <;> ring
  right_inv y := by
    change ActualEisensteinCoordinates.eval
      ((ActualEisensteinCoordinates.coords y).2 +
        ((ActualEisensteinCoordinates.coords y).1 -
          (ActualEisensteinCoordinates.coords y).2))
      (ActualEisensteinCoordinates.coords y).2 = y
    convert ActualEisensteinCoordinates.eval_coords y using 1 ; ring_nf

theorem dualFrequencyEquiv_norm_sq (k l : ℤ) :
    ‖eisEmbedding (dualFrequencyEquiv (k,l))‖ ^ 2 =
      (((k^2+k*l+l^2 : ℤ) : ℝ)) := by
  change ‖eisEmbedding (ActualEisensteinCoordinates.eval (k+l) k)‖ ^ 2 = _
  rw [eisEmbedding_eval_norm_sq]
  ring_nf

theorem dualFrequencyEquiv_trace_phase (r : ℝ) (a b k l : ℤ) :
    ShortDraftTrace.breveE
      (eisEmbedding (-(ActualEisensteinCoordinates.eval a b *
        (dualFrequencyEquiv (k,l))^2)) /
        eisLam / ((4*r : ℝ) : ℂ)) =
      Complex.exp (-(2 * Real.pi * Complex.I *
        (((a-b)*k^2+2*a*k*l+b*l^2 : ℤ) : ℂ)) /
        ((4*r : ℝ) : ℂ)) := by
  exact breveE_dual_quadratic_real_scale r a b k l

end ActualEisensteinCubic

namespace GaussianMoment

open scoped Topology
open Filter

noncomputable def realGauss (t : ℝ) (z : ℤ × ℤ) : ℝ :=
  Real.exp (-Real.pi * t * RankTwoPoisson.eisQ z)

theorem realGauss_nonneg (t : ℝ) (z : ℤ × ℤ) :
    0 ≤ realGauss t z := (Real.exp_pos _).le

theorem realGauss_summable {t : ℝ} (ht : 0 < t) :
    Summable (realGauss t) := by
  have h := (RankTwoPoisson.eis_gauss_summable ht).norm
  convert h using 1
  funext z
  dsimp [realGauss, RankTwoPoisson.eisGauss]
  rw [Complex.norm_exp]
  simp

theorem realGauss_cast (t : ℝ) (z : ℤ × ℤ) :
    (realGauss t z : ℂ) = RankTwoEisShift.shifted t 0 0 z := by
  dsimp [realGauss, RankTwoPoisson.eisQ,
    RankTwoEisShift.shifted, RankTwoEisShift.Q]
  rw [← Complex.ofReal_exp]
  congr 1
  ring_nf

theorem real_gaussian_mass :
    Tendsto (fun t : ℝ => t * (∑' z : ℤ × ℤ, realGauss t z))
      (𝓝[>] (0 : ℝ)) (𝓝 (2 / Real.sqrt 3)) := by
  have hC := EisensteinAbelFiber.shifted_gaussian_mass 0 0
  have hRe := (Complex.continuous_re.tendsto
    (((2 / Real.sqrt 3 : ℝ) : ℂ))).comp hC
  have hsum (t : ℝ) :
      (∑' z : ℤ × ℤ, RankTwoEisShift.shifted t 0 0 z) =
        (((∑' z : ℤ × ℤ, realGauss t z) : ℝ) : ℂ) := by
    calc
      (∑' z : ℤ × ℤ, RankTwoEisShift.shifted t 0 0 z) =
          ∑' z : ℤ × ℤ, (realGauss t z : ℂ) := by
            apply tsum_congr
            intro z
            exact (realGauss_cast t z).symm
      _ = (((∑' z : ℤ × ℤ, realGauss t z) : ℝ) : ℂ) :=
        (Complex.ofReal_tsum (realGauss t)).symm
  have hfun (t : ℝ) :
      t * (∑' z : ℤ × ℤ, realGauss t z) =
        (((t : ℂ) * (∑' z : ℤ × ℤ, RankTwoEisShift.shifted t 0 0 z)).re) := by
    rw [hsum]
    norm_cast
  have hEq :
      (fun t : ℝ => t * (∑' z : ℤ × ℤ, realGauss t z)) =
        (Complex.re ∘
          (fun t : ℝ => (t : ℂ) *
            (∑' z : ℤ × ℤ, RankTwoEisShift.shifted t 0 0 z))) := by
    funext t
    exact hfun t
  rw [← hEq] at hRe
  simpa only [Complex.ofReal_re] using hRe

end GaussianMoment

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT Complex

theorem dual_gaussian_is_actual_trace_phase
    (a b k l : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0)
    (η : ℝ) (hη : 0 < η) :
    let c : O := ActualEisensteinCoordinates.eval a b
    let y : O := dualFrequencyEquiv (k,l)
    let q : ℝ := OscSpecial.q (a : ℝ) (b : ℝ)
    let r : ℝ := OscSpecial.r η (a : ℝ) (b : ℝ)
    RankTwoComplex.dualGaussian
        (OscSpecial.A η (a : ℝ) (b : ℝ))
        (OscSpecial.B η (a : ℝ) (b : ℝ))
        (OscSpecial.D η (a : ℝ) (b : ℝ)) (k,l) =
      Complex.exp (-(Real.pi : ℂ) *
        ((η : ℂ) * (q : ℂ) / (4 * (r : ℂ))) *
        (‖eisEmbedding y‖ ^ 2 : ℂ)) *
      ShortDraftTrace.breveE
        (eisEmbedding (-(c * y^2)) / eisLam / ((4*r : ℝ) : ℂ)) := by
  have hqZ := coordinate_norm_pos_of_nonzero a b hc
  have hq : 0 < OscSpecial.q (a : ℝ) (b : ℝ) := by
    change 0 < (a : ℝ)^2 - (a : ℝ)*(b : ℝ)+(b : ℝ)^2
    exact_mod_cast (show 0 < a^2-a*b+b^2 by simpa only [pow_two] using hqZ)
  dsimp only
  rw [OscSpecial.dualGaussian_explicit hη hq (k,l)]
  rw [dualFrequencyEquiv_trace_phase (OscSpecial.r η (a : ℝ) (b : ℝ)) a b k l]
  have hnormC : ((‖eisEmbedding (dualFrequencyEquiv (k,l))‖ : ℂ)^2) =
      (((k^2+k*l+l^2 : ℤ) : ℂ)) := by
    exact_mod_cast dualFrequencyEquiv_norm_sq k l
  rw [hnormC]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem actual_oscillatory_poisson
    (a b : ℤ) (hc : ActualEisensteinCoordinates.eval a b ≠ 0)
    (η : ℝ) (hη : 0 < η) :
    let c : O := ActualEisensteinCoordinates.eval a b
    let q : ℝ := OscSpecial.q (a : ℝ) (b : ℝ)
    let r : ℝ := OscSpecial.r η (a : ℝ) (b : ℝ)
    (∑' z : O,
      (eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates c hc)
        (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
      Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
        (‖eisEmbedding z‖ ^ 2 : ℂ))) =
      (1 / ((OscSpecial.R η (a : ℝ) (b : ℝ) : ℂ) ^ (1 / 2 : ℂ))) *
        ∑' y : O,
          Complex.exp (-(Real.pi : ℂ) *
            ((η : ℂ) * (q : ℂ) / (4 * (r : ℂ))) *
            (‖eisEmbedding y‖ ^ 2 : ℂ)) *
          ShortDraftTrace.breveE
            (eisEmbedding (-(c * y^2)) / eisLam / ((4*r : ℝ) : ℂ)) := by
  have hqZ := coordinate_norm_pos_of_nonzero a b hc
  have hq : 0 < OscSpecial.q (a : ℝ) (b : ℝ) := by
    change 0 < (a : ℝ)^2 - (a : ℝ)*(b : ℝ)+(b : ℝ)^2
    exact_mod_cast (show 0 < a^2-a*b+b^2 by simpa only [pow_two] using hqZ)
  dsimp only
  rw [actual_oscillatory_sum_eq_binary a b hc η,
    OscSpecial.oscillatory_gaussian_poisson hη hq]
  congr 1
  let W : O → ℂ := fun y =>
    Complex.exp (-(Real.pi : ℂ) *
      ((η : ℂ) * (OscSpecial.q (a : ℝ) (b : ℝ) : ℂ) /
        (4 * (OscSpecial.r η (a : ℝ) (b : ℝ) : ℂ))) *
      (‖eisEmbedding y‖ ^ 2 : ℂ)) *
    ShortDraftTrace.breveE
      (eisEmbedding (-(ActualEisensteinCoordinates.eval a b * y^2)) /
        eisLam /
        ((4 * OscSpecial.r η (a : ℝ) (b : ℝ) : ℝ) : ℂ))
  calc
    (∑' p : ℤ × ℤ,
      RankTwoComplex.dualGaussian
        (OscSpecial.A η (a : ℝ) (b : ℝ))
        (OscSpecial.B η (a : ℝ) (b : ℝ))
        (OscSpecial.D η (a : ℝ) (b : ℝ)) p) =
        ∑' p : ℤ × ℤ, W (dualFrequencyEquiv p) := by
      apply tsum_congr
      intro p
      simpa only [W] using
        dual_gaussian_is_actual_trace_phase a b p.1 p.2 hc η hη
    _ = ∑' y : O, W y := dualFrequencyEquiv.tsum_eq W

end ActualEisensteinCubic

namespace OscSpecial

private theorem R_eq_four_r_div_q {η a b : ℝ} (hq : q a b ≠ 0) :
    R η a b = 4 * r η a b / q a b := by
  unfold R r
  field_simp [hq]
  ring

private theorem sqrt_R_eq {η a b : ℝ} (_hη : 0 < η) (hq : 0 < q a b) :
    Real.sqrt (R η a b) = 2 * Real.sqrt (r η a b) / Real.sqrt (q a b) := by
  rw [R_eq_four_r_div_q hq.ne']
  rw [Real.sqrt_div' (4 * r η a b) hq.le]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  have hs4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hs4]

theorem prefactor_eq_real_sqrt {η a b : ℝ} (hη : 0 < η) (hq : 0 < q a b) :
    (1 / ((R η a b : ℂ) ^ (1 / 2 : ℂ))) =
      ((Real.sqrt (q a b) / (2 * Real.sqrt (r η a b)) : ℝ) : ℂ) := by
  have hR : 0 ≤ R η a b := by unfold R; positivity
  have hqS : Real.sqrt (q a b) ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  have hrS : Real.sqrt (r η a b) ≠ 0 :=
    (Real.sqrt_pos.mpr (r_pos hη hq)).ne'
  have hcpow : (R η a b : ℂ) ^ (1 / 2 : ℂ) =
      ((R η a b) ^ (1 / 2 : ℝ) : ℝ) := by
    simpa using (Complex.ofReal_cpow hR (1 / 2 : ℝ)).symm
  rw [hcpow]
  simp only [Complex.ofReal_div]
  rw [← Real.sqrt_eq_rpow, sqrt_R_eq hη hq]
  push_cast
  field_simp [hqS, hrS]

open scoped Topology
open Filter

theorem prefactor_tendsto {a b : ℝ} (hq : 0 < q a b) :
    Tendsto (fun η : ℝ => 1 / ((R η a b : ℂ) ^ (1 / 2 : ℂ)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((Real.sqrt (q a b) / 2 : ℝ) : ℂ))) := by
  have hrcont : Continuous (fun η : ℝ => r η a b) := by
    unfold r
    fun_prop
  have hr : Tendsto (fun η : ℝ => r η a b) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    simpa [r] using (hrcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hs : Tendsto (fun η : ℝ => Real.sqrt (r η a b))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    simpa only [Function.comp_def, Real.sqrt_one] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hr
  have hd : Tendsto (fun η : ℝ => Real.sqrt (q a b) /
      (2 * Real.sqrt (r η a b))) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.sqrt (q a b) / 2)) := by
    convert tendsto_const_nhds.div (tendsto_const_nhds.mul hs)
      (by norm_num : (2 : ℝ) * 1 ≠ 0) using 1 ; simp
  have hc : Tendsto (fun η : ℝ =>
      ((Real.sqrt (q a b) / (2 * Real.sqrt (r η a b)) : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (((Real.sqrt (q a b) / 2 : ℝ) : ℂ))) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hd
  have heq : (fun η : ℝ => 1 / ((R η a b : ℂ) ^ (1 / 2 : ℂ))) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun η : ℝ => ((Real.sqrt (q a b) / (2 * Real.sqrt (r η a b)) : ℝ) : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact prefactor_eq_real_sqrt hη hq
  exact hc.congr' heq.symm

end OscSpecial

namespace GaussianMoment

open scoped Topology
open Filter

private theorem eisQ_nonneg (z : ℤ × ℤ) : 0 ≤ RankTwoPoisson.eisQ z := by
  have h := RankTwoPoisson.eisQ_lower z
  nlinarith [sq_nonneg (z.1 : ℝ), sq_nonneg (z.2 : ℝ)]

private theorem moment_term_bound {t : ℝ} (ht : 0 < t) (z : ℤ × ℤ) :
    RankTwoPoisson.eisQ z * realGauss t z ≤
      (2 / (Real.pi * t)) * realGauss (t / 2) z := by
  have h := gaussian_moment_term_bound (RankTwoPoisson.eisQ z) (Real.pi * t)
    (eisQ_nonneg z) (mul_pos Real.pi_pos ht)
  convert h using 1 <;> dsimp [realGauss] <;> ring_nf

private theorem moment_summable {t : ℝ} (ht : 0 < t) :
    Summable (fun z : ℤ × ℤ => RankTwoPoisson.eisQ z * realGauss t z) := by
  have hmajor : Summable (fun z : ℤ × ℤ =>
      (2 / (Real.pi * t)) * realGauss (t / 2) z) :=
    (realGauss_summable (t := t / 2) (half_pos ht)).mul_left _
  exact hmajor.of_nonneg_of_le
    (fun z => mul_nonneg (eisQ_nonneg z) (realGauss_nonneg t z))
    (moment_term_bound ht)

private theorem moment_tsum_bound {t : ℝ} (ht : 0 < t) :
    (∑' z : ℤ × ℤ, RankTwoPoisson.eisQ z * realGauss t z) ≤
      (2 / (Real.pi * t)) *
        (∑' z : ℤ × ℤ, realGauss (t / 2) z) := by
  have hmajor : Summable (fun z : ℤ × ℤ =>
      (2 / (Real.pi * t)) * realGauss (t / 2) z) :=
    (realGauss_summable (t := t / 2) (half_pos ht)).mul_left _
  have h := Summable.tsum_le_tsum (moment_term_bound ht)
    (moment_summable ht) hmajor
  simpa only [tsum_mul_left] using h

private theorem moment_tsum_nonneg (t : ℝ) :
    0 ≤ (∑' z : ℤ × ℤ, RankTwoPoisson.eisQ z * realGauss t z) := by
  exact tsum_nonneg fun z => mul_nonneg (eisQ_nonneg z) (realGauss_nonneg t z)

private theorem half_tendsto_within :
    Tendsto (fun t : ℝ => t / 2) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc : ContinuousAt (fun t : ℝ => t / 2) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    exact half_pos ht

private theorem t_tendsto_zero :
    Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
  tendsto_id.mono_left nhdsWithin_le_nhds

private theorem scaled_half_mass_tendsto :
    Tendsto
      (fun t : ℝ => (t / 2) *
        (∑' z : ℤ × ℤ, realGauss (t / 2) z))
      (𝓝[>] (0 : ℝ)) (𝓝 (2 / Real.sqrt 3)) := by
  simpa only [Function.comp_def] using real_gaussian_mass.comp half_tendsto_within

theorem scaled_moment_vanishes :
    Tendsto
      (fun t : ℝ => t ^ 3 *
        (∑' z : ℤ × ℤ, RankTwoPoisson.eisQ z * realGauss t z))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hright : Tendsto
      (fun t : ℝ => (4 / Real.pi) * t *
        ((t / 2) * (∑' z : ℤ × ℤ, realGauss (t / 2) z)))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h := (t_tendsto_zero.mul scaled_half_mass_tendsto).const_mul (4 / Real.pi)
    simpa only [zero_mul, mul_zero, Function.comp_def, mul_assoc] using h
  have hleft : Tendsto (fun _ : ℝ => (0 : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := tendsto_const_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hleft hright
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    exact mul_nonneg (pow_nonneg ht.le _) (moment_tsum_nonneg t)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    have h := moment_tsum_bound ht
    have ht3 : 0 ≤ t ^ 3 := pow_nonneg ht.le _
    have hmul := mul_le_mul_of_nonneg_left h ht3
    calc
      t ^ 3 * (∑' z : ℤ × ℤ, RankTwoPoisson.eisQ z * realGauss t z) ≤
          t ^ 3 * ((2 / (Real.pi * t)) *
            (∑' z : ℤ × ℤ, realGauss (t / 2) z)) := hmul
      _ = (4 / Real.pi) * t *
          ((t / 2) * (∑' z : ℤ × ℤ, realGauss (t / 2) z)) := by
        field_simp [ht.ne']
        ring

end GaussianMoment

end

end OAI
