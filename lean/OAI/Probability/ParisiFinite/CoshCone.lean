import Mathlib
import OAI.Probability.ParisiFinite.ParisiFiniteTransport

namespace OAI

/-! Cosh Cone. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Function Set
open MeasureTheory Set Real Matrix
open scoped BigOperators
open MeasureTheory Filter Set Real Finset Polynomial
open scoped Topology BigOperators
namespace ParisiSpectral

lemma multichoose_nonneg {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    0 ≤ Ring.multichoose r n := by
  have hP : ∀ n : ℕ, 0 ≤ (ascPochhammer ℕ n).smeval r := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [ascPochhammer_succ_right, Polynomial.smeval_mul]
      simp only [Polynomial.smeval_add, Polynomial.smeval_X, Polynomial.smeval_natCast,
        pow_one, pow_zero, nsmul_eq_mul, mul_one]
      exact mul_nonneg ih (add_nonneg hr (Nat.cast_nonneg _))
  have he := Ring.factorial_nsmul_multichoose_eq_ascPochhammer r n
  simp only [nsmul_eq_mul] at he
  exact (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℝ) < n.factorial)).mp (he.symm ▸ hP n)

lemma PositiveDefinite.sum {ι : Type*} {f : ι → ℝ → ℝ} (s : Finset ι)
    (hf : ∀ i ∈ s, PositiveDefinite (f i)) :
    PositiveDefinite (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [sum_empty] using PositiveDefinite.constant (by norm_num : (0 : ℝ) ≤ 0)
  | @insert a s ha ih =>
    simp only [sum_insert ha]
    exact (hf a (mem_insert_self _ _)).add (ih fun i hi => hf i (mem_insert_of_mem hi))

lemma hasSum_one_sub_neg_rpow {r z : ℝ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => Ring.choose (r + n - 1) n * z^n) ((1-z)^(-r)) := by
  have he : z ∈ Metric.eball (0 : ℝ) 1 := by
    simp only [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_lt_one_iff]
    exact_mod_cast hz
  have hs := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero r).hasSum he
  have hp : 0 ≤ 1-z := by have := le_abs_self z; rw [Real.norm_eq_abs] at hz; linarith
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add,
    Real.rpow_neg hp, one_div] using hs

lemma PositiveDefinite.one_sub_neg_rpow {g : ℝ → ℝ} (hg : PositiveDefinite g)
    (hg0 : g 0 < 1) {r : ℝ} (hr : 0 ≤ r) :
    PositiveDefinite (fun x => (1-g x)^(-r)) := by
  refine PositiveDefinite.limit (l := atTop)
    (g := fun n : ℕ => fun x => ∑ i ∈ Finset.range n, Ring.choose (r+i-1) i * (g x)^i) ?_ ?_
  · intro n
    apply PositiveDefinite.sum
    intro i hi
    apply (hg.pow i).smul
    rw [← Ring.multichoose_eq]
    exact multichoose_nonneg hr i
  · intro x
    exact (hasSum_one_sub_neg_rpow ((hg.norm_le x).trans_lt hg0)).tendsto_sum_nat

 

structure CoshCone (a : ℝ) (h : ℝ → ℝ) : Prop where
  representation : ∃ (K : ℝ) (g : ℝ → ℝ),
    0 < K ∧ PositiveDefinite g ∧ g 0 < K ∧
    ∀ x, h x = K*cosh (a*x)-g x

lemma cosh_neg_rpow_positiveDefinite {r : ℝ} (hr : 0 < r) (a : ℝ) :
    PositiveDefinite (fun x => (cosh (a*x))^(-r)) :=
  (show PositiveDefinite (fun x => (cosh x)^(-r)) from cosh_neg_rpow_posSemidef hr).comp_linear a

lemma CoshCone.pos {a : ℝ} {h : ℝ → ℝ} (hh : CoshCone a h) (x : ℝ) : 0 < h x := by
  obtain ⟨K, g, hK, hg, hg0, he⟩ := hh.representation
  rw [he]
  have hx : g x ≤ g 0 := (le_abs_self _).trans (hg.norm_le x)
  have hc := mul_le_mul_of_nonneg_left (one_le_cosh (a*x)) hK.le
  nlinarith

 

lemma CoshCone.neg_rpow_positiveDefinite {a : ℝ} {h : ℝ → ℝ}
    (hh : CoshCone a h) {r : ℝ} (hr : 0 < r) :
    PositiveDefinite (fun x => (h x)^(-r)) := by
  obtain ⟨K, g, hK, hg, hg0, he⟩ := hh.representation
  let u : ℝ → ℝ := fun x => K⁻¹ * (g x * (cosh (a*x))^(-1 : ℝ))
  have hu : PositiveDefinite u :=
    (hg.mul (cosh_neg_rpow_positiveDefinite (by norm_num : (0 : ℝ) < 1) a)).smul
      (inv_nonneg.mpr hK.le)
  have hu0 : u 0 < 1 := by
    simp only [u, mul_zero, cosh_zero, one_rpow, mul_one]
    rw [← div_eq_inv_mul, div_lt_one hK]
    exact hg0
  have hv := hu.one_sub_neg_rpow hu0 hr.le
  have hc := (cosh_neg_rpow_positiveDefinite hr a).smul (rpow_nonneg hK.le (-r))
  have heq (x : ℝ) : h x = (K*cosh (a*x)) * (1-u x) := by
    rw [he]
    dsimp [u]
    rw [rpow_neg_one]
    field_simp
  have hhx (x : ℝ) : 0 ≤ 1-u x := by
    have hx := (le_abs_self (u x)).trans (hu.norm_le x)
    linarith
  have hp := hc.mul hv
  convert hp using 1
  funext x
  rw [heq, mul_rpow (by positivity) (hhx x), mul_rpow hK.le (cosh_pos _).le]

end ParisiSpectral

 

open MeasureTheory Set Real Matrix Filter InnerProductSpace
open scoped BigOperators Topology RealInnerProductSpace
namespace ParisiSpectral

lemma posSemidef_integral {A Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (K : Ω → Matrix A A ℝ)
    (hK : ∀ᵐ z ∂μ, (K z).PosSemidef)
    (hi : ∀ a b, Integrable (fun z => K z a b) μ) :
    Matrix.PosSemidef (fun a b => ∫ z, K z a b ∂μ) := by
  classical
  refine ⟨Matrix.IsHermitian.ext (fun a b => ?_), fun c => ?_⟩
  · simp only [star_trivial]
    apply integral_congr_ae
    filter_upwards [hK] with z hz
    exact hz.1.apply a b
  · simp only [Finsupp.sum, star_trivial]
    have hij (a b : A) : Integrable (fun z => c a * K z a b * c b) μ :=
      ((hi a b).const_mul _).mul_const _
    simp_rw [← integral_const_mul, ← integral_mul_const]
    simp_rw [← integral_finsetSum _ (fun b hb => hij _ b)]
    rw [← integral_finsetSum _ (fun a ha => integrable_finsetSum _ (fun b hb => hij a b))]
    apply integral_nonneg_of_ae
    filter_upwards [hK] with z hz
    exact hz.2 c

lemma posSemidef_cauchy {A : Type*} (u : A → ℝ) (hu : ∀ a, 0 < u a)
    {t : ℝ} (ht : 0 ≤ t) :
    Matrix.PosSemidef (fun a b => (t+u a+u b)⁻¹) := by
  have he (a b : A) (z : ℝ) : exp (-t*z) * (exp (-u a*z)*exp (-u b*z)) =
      exp (-(t+u a+u b)*z) := by
    simp only [← exp_add]
    congr 1
    ring
  have hi (a b : A) : IntegrableOn
      (fun z => exp (-t*z) * (exp (-u a*z)*exp (-u b*z))) (Ioi 0) := by
    simp_rw [he]
    exact integrableOn_exp_mul_Ioi (by linarith [hu a, hu b]) 0
  have hp := posSemidef_integral_gram (volume.restrict (Ioi (0 : ℝ)))
    (fun a z => exp (-u a*z)) (fun z => exp (-t*z))
    (ae_of_all _ fun z => (exp_pos _).le) hi
  have heq : (fun a b : A => ∫ z in Ioi (0 : ℝ),
      exp (-t*z) * (exp (-u a*z)*exp (-u b*z))) =
      (fun a b : A => (t+u a+u b)⁻¹) := by
    funext a b
    simp_rw [he]
    rw [integral_exp_mul_Ioi (by linarith [hu a, hu b])]
    simp only [mul_zero, exp_zero, neg_div_neg_eq, one_div]
  exact (congrArg Matrix.PosSemidef heq).mp hp

lemma fractional_integrand_gram {p t u v : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (ht : 0 < t) (hu : 0 < u) (hv : 0 < v) :
    rpowIntegrand₀₁ p t u + rpowIntegrand₀₁ p t v - rpowIntegrand₀₁ p t (u+v) =
      t^(p-1) * (u/(t+u)*(v/(t+v))) * (1+t*(t+u+v)⁻¹) := by
  rw [rpowIntegrand₀₁_eq_pow_div hp ht.le hu.le,
    rpowIntegrand₀₁_eq_pow_div hp ht.le hv.le,
    rpowIntegrand₀₁_eq_pow_div hp ht.le (add_pos hu hv).le]
  have h1 : t+u ≠ 0 := (add_pos ht hu).ne'
  have h2 : t+v ≠ 0 := (add_pos ht hv).ne'
  have h3 : t+(u+v) ≠ 0 := (add_pos ht (add_pos hu hv)).ne'
  have h4 : t+u+v ≠ 0 := by positivity
  field_simp
  ring

 

lemma posSemidef_fractional_gap {A : Type*} (u : A → ℝ) (hu : ∀ a, 0 < u a)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) :
    Matrix.PosSemidef (fun a b => (u a)^p+(u b)^p-(u a+u b)^p) := by
  obtain ⟨μ, hμ⟩ := exists_measure_rpow_eq_integral_rpowIntegrand₀₁ hp
  let K : ℝ → Matrix A A ℝ := fun t a b =>
    rpowIntegrand₀₁ p t (u a) + rpowIntegrand₀₁ p t (u b) -
      rpowIntegrand₀₁ p t (u a+u b)
  have hi (a b : A) : Integrable (fun t => K t a b) (μ.restrict (Ioi 0)) :=
    ((hμ _ (hu a).le).1.add (hμ _ (hu b).le).1).sub
      (hμ _ (add_pos (hu a) (hu b)).le).1
  have hK : ∀ᵐ t ∂μ.restrict (Ioi 0), (K t).PosSemidef := by
    apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro t (ht : 0 < t)
    have hc := (posSemidef_cauchy u hu ht.le).smul ht.le
    have hone : Matrix.PosSemidef (fun a b : A => (1 : ℝ)) := by
      simpa only [RCLike.inner_apply, map_one, mul_one, star_trivial] using
        (posSemidef_inner (fun _ : A => (1 : ℝ)))
    have hgr := posSemidef_inner (fun a : A => u a / (t+u a))
    have hh := (hgr.hadamard (hone.add hc)).smul (rpow_nonneg ht.le (p-1))
    have heq : (t^(p-1) • ((fun a b : A => ⟪u a/(t+u a), u b/(t+u b)⟫_ℝ) ⊙
        ((fun a b : A => (1:ℝ))+t • (fun a b : A => (t+u a+u b)⁻¹))) : Matrix A A ℝ) = K t := by
      funext a b
      change t^(p-1) * ((u b/(t+u b) * (u a/(t+u a))) *
        (1+t*(t+u a+u b)⁻¹)) =
        rpowIntegrand₀₁ p t (u a) + rpowIntegrand₀₁ p t (u b) -
          rpowIntegrand₀₁ p t (u a+u b)
      rw [fractional_integrand_gram hp ht (hu a) (hu b)]
      ring
    exact (congrArg Matrix.PosSemidef heq).mp hh
  have hp' := posSemidef_integral (μ.restrict (Ioi 0)) K hK hi
  have heq : (fun a b : A => ∫ t in Ioi 0, K t a b ∂μ) =
      (fun a b : A => (u a)^p+(u b)^p-(u a+u b)^p) := by
    funext a b
    simp only [K]
    have hab : Integrable (fun t => rpowIntegrand₀₁ p t (u a) +
        rpowIntegrand₀₁ p t (u b)) (μ.restrict (Ioi 0)) :=
      (hμ _ (hu a).le).1.add (hμ _ (hu b).le).1
    rw [integral_sub hab (hμ _ (add_pos (hu a) (hu b)).le).1,
      integral_add (hμ _ (hu a).le).1 (hμ _ (hu b).le).1,
      ← (hμ _ (hu a).le).2, ← (hμ _ (hu b).le).2,
      ← (hμ _ (add_pos (hu a) (hu b)).le).2]
  exact (congrArg Matrix.PosSemidef heq).mp hp'

lemma fractional_cosh_gap_identity (p x y : ℝ) :
    (2:ℝ)^(-p) * (exp (-p*x)*exp (-p*y)) *
      ((exp (2*x))^p+(exp (2*y))^p-(exp (2*x)+exp (2*y))^p) =
    2^(1-p)*cosh (p*(x-y))-(cosh (x-y))^p := by
  have hsum := exp_sum_cosh x y
  rw [hsum, mul_rpow (by positivity) (cosh_pos _).le,
    mul_rpow (by norm_num : (0:ℝ) ≤ 2) (exp_pos _).le]
  simp only [rpow_def_of_pos (exp_pos _), log_exp]
  have h1 : (exp (-p*x)*exp (-p*y))*exp (2*x*p) = exp (p*(x-y)) := by
    simp only [← exp_add]
    congr 1
    ring
  have h2 : (exp (-p*x)*exp (-p*y))*exp (2*y*p) = exp (-(p*(x-y))) := by
    simp only [← exp_add]
    congr 1
    ring
  have h3 : (exp (-p*x)*exp (-p*y))*exp ((x+y)*p) = 1 := by
    simp only [← exp_add]
    rw [show -p*x+ -p*y+(x+y)*p = 0 by ring, exp_zero]
  have h4 : (2:ℝ)^(-p) * 2^p = 1 := by
    rw [← rpow_add (by norm_num : (0:ℝ)<2), neg_add_cancel, rpow_zero]
  have h5 : (2:ℝ)^(1-p) = 2*2^(-p) := by
    rw [sub_eq_add_neg, rpow_add (by norm_num : (0:ℝ)<2), rpow_one]
  rw [h5]
  calc
    _ = 2^(-p)*(exp (p*(x-y))+exp (-(p*(x-y)))) - (cosh (x-y))^p := by
      calc
        _ = 2^(-p)*((exp (-p*x)*exp (-p*y))*exp (2*x*p)) +
            2^(-p)*((exp (-p*x)*exp (-p*y))*exp (2*y*p)) -
            (2^(-p)*2^p)*((exp (-p*x)*exp (-p*y))*exp ((x+y)*p))*
              (cosh (x-y))^p := by ring
        _ = _ := by rw [h1, h2, h3, h4]; ring
    _ = _ := by rw [show cosh (p*(x-y)) =
      (exp (p*(x-y))+exp (-(p*(x-y))))/2 from Real.cosh_eq _]; ring

 
lemma cosh_fractional_gap_positiveDefinite {p : ℝ} (hp : p ∈ Set.Ioo 0 1) :
    PositiveDefinite (fun x => (2:ℝ)^(1-p)*cosh (p*x)-(cosh x)^p) := by
  have hb := posSemidef_fractional_gap (fun x : ℝ => exp (2*x))
    (fun x => exp_pos _) hp
  have hg := posSemidef_inner (fun x : ℝ => exp (-p*x))
  have hh := (hg.hadamard hb).smul (rpow_nonneg (by norm_num : (0:ℝ)≤2) (-p))
  have heq : (((2:ℝ)^(-p)) • ((fun x y : ℝ => ⟪exp (-p*x),exp (-p*y)⟫_ℝ) ⊙
      (fun x y : ℝ => (exp (2*x))^p+(exp (2*y))^p-(exp (2*x)+exp (2*y))^p)) :
      Matrix ℝ ℝ ℝ) =
      (fun x y : ℝ => 2^(1-p)*cosh (p*(x-y))-(cosh (x-y))^p) := by
    funext x y
    change 2^(-p) * ((exp (-p*y)*exp (-p*x)) *
      ((exp (2*x))^p+(exp (2*y))^p-(exp (2*x)+exp (2*y))^p)) = _
    rw [mul_comm (exp (-p*y)) (exp (-p*x)), ← mul_assoc]
    exact fractional_cosh_gap_identity p x y
  exact (congrArg Matrix.PosSemidef heq).mp hh

end ParisiSpectral

 

open MeasureTheory Set Real Filter Polynomial
open Finset (range)
open scoped Topology BigOperators
namespace ParisiSpectral

lemma fractional_coeff_identity (p : ℝ) (n : ℕ) :
    -(Ring.choose p (n+1) * (-1:ℝ)^(n+1)) =
      p * Ring.multichoose (1-p) n / (n+1) := by
  have he := Ring.choose_smul_choose p (n := n+1) (k := 1) (by omega)
  simp only [Nat.choose_one_right, nsmul_eq_mul, Nat.cast_add, Nat.cast_one,
    Ring.choose_one_right, Nat.add_sub_cancel] at he
  have hc := Ring.choose_neg' (1-p) n
  simp only [show -(1-p) = p-1 by ring, Units.smul_def, zsmul_eq_mul,
    Int.cast_negOnePow, zpow_natCast] at hc
  rw [hc] at he
  apply (eq_div_iff (by positivity : (n:ℝ)+1 ≠ 0)).mpr
  have hpow : ((-1:ℝ)^n)^2 = 1 := by rw [← pow_mul, mul_comm n 2, pow_mul]; norm_num
  rw [pow_succ]
  calc
    _ = ((n:ℝ)+1)*Ring.choose p (n+1)*(-1:ℝ)^n := by ring
    _ = p*Ring.multichoose (1-p) n*((-1:ℝ)^n)^2 := by rw [he]; ring
    _ = _ := by rw [hpow, mul_one]

lemma fractional_coeff_nonneg {p : ℝ} (hp : p ∈ Set.Icc 0 1) (n : ℕ) :
    0 ≤ -(Ring.choose p (n+1) * (-1:ℝ)^(n+1)) := by
  rw [fractional_coeff_identity]
  exact div_nonneg (mul_nonneg hp.1 (multichoose_nonneg (sub_nonneg.mpr hp.2) n)) (by positivity)

lemma hasSum_one_sub_rpow_gap {p z : ℝ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => -(Ring.choose p (n+1) * (-1:ℝ)^(n+1)) * z^(n+1))
      (1-(1-z)^p) := by
  have he : -z ∈ Metric.eball (0:ℝ) 1 := by
    simp only [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_lt_one_iff]
    exact_mod_cast (show ‖-z‖ < 1 by simpa only [norm_neg] using hz)
  have hs : HasSum (fun n : ℕ => Ring.choose p n * (-z)^n) ((1-z)^p) := by
    simpa only [binomialSeries, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul,
      zero_add, sub_eq_add_neg] using
      (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := p)).hasSum he
  have ht := (hasSum_nat_add_iff' (f := fun n : ℕ => Ring.choose p n * (-z)^n) 1).mpr hs
  simp only [Finset.sum_range_one, pow_zero, mul_one, Ring.choose_zero_right] at ht
  have hn := ht.neg
  convert! hn using 1
  · funext n
    rw [neg_pow]
    ring
  · ring

 

lemma coshCone_fractional_defect {a K p : ℝ} {g : ℝ → ℝ}
    (hK : 0 < K) (hg : PositiveDefinite g) (hg0 : g 0 < K)
    (hp : p ∈ Set.Ioo 0 1) :
    PositiveDefinite (fun x => (K*cosh (a*x))^p - (K*cosh (a*x)-g x)^p) := by
  let c : ℝ → ℝ := fun x => K*cosh (a*x)
  let u : ℝ → ℝ := fun x => g x / c x
  have hc (x : ℝ) : 0 < c x := mul_pos hK (cosh_pos _)
  have hbound (x : ℝ) : ‖u x‖ < 1 := by
    dsimp only [u]
    rw [norm_div, Real.norm_eq_abs (c x), abs_of_pos (hc x), div_lt_one (hc x)]
    have hh := mul_le_mul_of_nonneg_left (one_le_cosh (a*x)) hK.le
    exact (hg.norm_le x).trans_lt (hg0.trans_le (by simpa only [mul_one, c] using hh))
  let d : ℕ → ℝ := fun n => -(Ring.choose p (n+1) * (-1:ℝ)^(n+1))
  let G : ℕ → ℝ → ℝ := fun n x => d n * (g x)^(n+1) * (c x)^(p-(n+1:ℕ))
  have hG (n : ℕ) : PositiveDefinite (G n) := by
    have hr : 0 < (n+1:ℕ)-p := by exact_mod_cast (show (0:ℝ) < (n:ℝ)+1-p by linarith [Nat.cast_nonneg (α := ℝ) n, hp.2])
    have hh := ((hg.pow (n+1)).mul ((cosh_neg_rpow_positiveDefinite hr a).smul
      (rpow_nonneg hK.le (-((n+1:ℕ)-p))))).smul (fractional_coeff_nonneg ⟨hp.1.le,hp.2.le⟩ n)
    convert hh using 1
    funext x
    dsimp only [G, d, c]
    rw [show p-(n+1:ℕ) = -((n+1:ℕ)-p) by ring, mul_rpow hK.le (cosh_pos _).le]
    ring
  refine PositiveDefinite.limit (l := atTop) (g := fun n x => ∑ i ∈ range n, G i x)
    (fun n => PositiveDefinite.sum _ (fun i _ => hG i)) ?_
  intro x
  have hs := (hasSum_one_sub_rpow_gap (p := p) (hbound x)).mul_left ((c x)^p)
  have he (n : ℕ) : G n x = (c x)^p * (d n * (u x)^(n+1)) := by
    dsimp [G, u]
    rw [rpow_sub (hc x), rpow_natCast, div_pow]
    ring
  have hEq : (c x)^p * (1-(1-u x)^p) = (K*cosh (a*x))^p-(K*cosh (a*x)-g x)^p := by
    have hux : 0 ≤ 1-u x := by have hh := le_abs_self (u x); have := hbound x; rw [Real.norm_eq_abs] at this; linarith
    rw [mul_sub, mul_one, ← mul_rpow (hc x).le hux]
    congr 2
    dsimp [u, c]
    field_simp
  rw [hEq] at hs
  exact (hs.congr_fun he).tendsto_sum_nat

lemma CoshCone.rpow {a : ℝ} {h : ℝ → ℝ} (hh : CoshCone a h)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) : CoshCone (p*a) (fun x => (h x)^p) := by
  obtain ⟨K,g,hK,hg,hg0,he⟩ := hh.representation
  let D : ℝ → ℝ := fun x => K^p*((2:ℝ)^(1-p)*cosh (p*(a*x))-(cosh (a*x))^p)
  let G : ℝ → ℝ := fun x => (K*cosh (a*x))^p-(K*cosh (a*x)-g x)^p
  have hD : PositiveDefinite D :=
    ((cosh_fractional_gap_positiveDefinite hp).comp_linear a).smul (rpow_nonneg hK.le p)
  have hG : PositiveDefinite G := coshCone_fractional_defect hK hg hg0 hp
  refine ⟨⟨K^p*2^(1-p), (fun x => D x+G x), by positivity, hD.add hG, ?_, ?_⟩⟩
  · dsimp [D, G]
    simp only [mul_zero, cosh_zero, one_rpow, mul_one]
    have hpos : 0 < (K-g 0)^p := rpow_pos_of_pos (sub_pos.mpr hg0) _
    nlinarith
  · intro x
    rw [he]
    dsimp [D, G]
    rw [mul_rpow hK.le (cosh_pos _).le]
    rw [mul_assoc p a x]
    ring

end ParisiSpectral

 

open MeasureTheory ProbabilityTheory Real Filter Set
open scoped Topology NNReal
namespace ParisiSpectral

lemma integrable_cosh_shift (a x : ℝ) (t : ℝ≥0) :
    Integrable (fun z => cosh (a*(x+z))) (gaussianReal 0 t) := by
  have h1 (z : ℝ) : exp (a*(x+z)) = exp (a*x)*exp (a*z) := by rw [mul_add, exp_add]
  have h2 (z : ℝ) : exp (-(a*(x+z))) = exp (-a*x)*exp (-a*z) := by
    rw [show -(a*(x+z)) = -a*x+ -a*z by ring, exp_add]
  simp_rw [cosh_eq, h1, h2]
  exact (((integrable_exp_mul_gaussianReal a).const_mul (exp (a*x))).add
    ((integrable_exp_mul_gaussianReal (-a)).const_mul (exp (-a*x)))).div_const 2

lemma heat_cosh (a x : ℝ) (t : ℝ≥0) :
    heat t (fun y => cosh (a*y)) x = exp ((t:ℝ)*a^2/2)*cosh (a*x) := by
  have h1 (z : ℝ) : exp (a*(x+z)) = exp (a*x)*exp (a*z) := by rw [mul_add, exp_add]
  have h2 (z : ℝ) : exp (-(a*(x+z))) = exp (-a*x)*exp (-a*z) := by
    rw [show -(a*(x+z)) = -a*x+ -a*z by ring, exp_add]
  have hm (b : ℝ) : (∫ z, exp (b*z) ∂gaussianReal 0 t) = exp ((t:ℝ)*b^2/2) := by
    have hh := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := t)) b
    simpa only [mgf, zero_mul, zero_add] using hh
  dsimp only [heat]
  simp_rw [cosh_eq, h1, h2]
  rw [integral_div, integral_add
    ((integrable_exp_mul_gaussianReal a).const_mul (exp (a*x)))
    ((integrable_exp_mul_gaussianReal (-a)).const_mul (exp (-a*x))),
    integral_const_mul, integral_const_mul, hm, hm]
  rw [neg_sq, show -(a*x) = -a*x by ring]
  ring

lemma CoshCone.heat {a : ℝ} {h : ℝ → ℝ}
    (hh : CoshCone a h) (hc : Continuous h) (t : ℝ≥0) : CoshCone a (ParisiSpectral.heat t h) := by
  obtain ⟨K,g,hK,hg,hg0,he⟩ := hh.representation
  have hgc : Continuous g := by
    have heq : g = fun x => K*cosh (a*x)-h x := by funext x; rw [he]; ring
    rw [heq]
    exact (continuous_const.mul (continuous_cosh.comp (continuous_const.mul continuous_id))).sub hc
  have hi (x : ℝ) : Integrable (fun z => g (x+z)) (gaussianReal 0 t) :=
    Integrable.of_bound (hgc.comp (continuous_const.add continuous_id)).aestronglyMeasurable
      (g 0) (ae_of_all _ fun z => hg.norm_le _)
  refine ⟨⟨K*exp ((t:ℝ)*a^2/2), ParisiSpectral.heat t g, by positivity, hg.heat hgc t, ?_, ?_⟩⟩
  · have hle : ParisiSpectral.heat t g 0 ≤ g 0 := by
      have hd := integral_mono (hi 0) (integrable_const (g 0))
        (fun z => (le_abs_self (g (0+z))).trans (hg.norm_le _))
      simpa only [ParisiSpectral.heat, integral_const, probReal_univ, one_smul] using hd
    have hex : 1 ≤ exp ((t:ℝ)*a^2/2) := one_le_exp (by positivity)
    exact hle.trans_lt (hg0.trans_le (by nlinarith))
  · intro x
    dsimp only [ParisiSpectral.heat]
    simp_rw [he]
    rw [integral_sub ((integrable_cosh_shift a x t).const_mul K) (hi x), integral_const_mul]
    have hh := heat_cosh a x t
    dsimp only [ParisiSpectral.heat] at hh
    rw [hh]
    ring

end ParisiSpectral

 

open MeasureTheory Filter Set Real
open scoped Topology
namespace ParisiSpectral

 

lemma CoshCone.limit {a : ℝ} (ha : a ≠ 0) {h : ℕ → ℝ → ℝ} {H : ℝ → ℝ}
    (hh : ∀ n, CoshCone a (h n)) (ht : ∀ x, Tendsto (fun n => h n x) atTop (𝓝 (H x)))
    (hH : 0 < H 0) : CoshCone a H := by
  classical
  choose K g hK hg hg0 he using (fun n => (hh n).representation)
  have hden : 0 < cosh a-1 := sub_pos.mpr (one_lt_cosh.mpr ha)
  have hbound (n : ℕ) : K n ≤ (h n 1-h n 0)/(cosh a-1) := by
    apply (le_div_iff₀ hden).mpr
    have hgn : g n 1 ≤ g n 0 := (le_abs_self _).trans ((hg n).norm_le _)
    rw [he n 1, he n 0]
    simp only [mul_one, mul_zero, cosh_zero]
    nlinarith
  have hb := (((ht 1).sub (ht 0)).div_const (cosh a-1)).bddAbove_range
  obtain ⟨M,hM⟩ := hb
  have hkm (n : ℕ) : K n ∈ Icc (0:ℝ) M :=
    ⟨(hK n).le, (hbound n).trans (hM (mem_range_self n))⟩
  obtain ⟨k,hk,φ,hφ,hlim⟩ := isCompact_Icc.tendsto_subseq hkm
  let G : ℝ → ℝ := fun x => k*cosh (a*x)-H x
  have hglim (x : ℝ) : Tendsto (fun n => g (φ n) x) atTop (𝓝 (G x)) := by
    have heq (n : ℕ) : g (φ n) x = K (φ n)*cosh (a*x)-h (φ n) x := by rw [he]; ring
    simp_rw [heq]
    exact (hlim.mul_const _).sub ((ht x).comp hφ.tendsto_atTop)
  have hG : PositiveDefinite G := PositiveDefinite.limit (fun n => hg (φ n)) hglim
  have hG0 : 0 ≤ k-H 0 := by simpa only [G, mul_zero, cosh_zero, mul_one] using hG.at_zero
  refine ⟨⟨k,G,by linarith,hG,?_,?_⟩⟩
  · dsimp only [G]
    simp only [mul_zero, cosh_zero, mul_one]
    linarith
  · intro x
    dsimp only [G]
    ring

end ParisiSpectral

 

 

open MeasureTheory ProbabilityTheory Filter Set Real
open scoped Topology NNReal
namespace ParisiSpectral

lemma CoshCone.exp_lower {a b : ℝ} {φ : ℝ → ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hc : CoshCone b (fun x => exp (b*φ x))) :
    CoshCone a (fun x => exp (a*φ x)) := by
  rcases eq_or_lt_of_le hab with rfl | hab
  · exact hc
  have hb : 0 < b := ha.trans hab
  have hp : a/b ∈ Set.Ioo 0 1 := ⟨div_pos ha hb, (div_lt_one hb).mpr hab⟩
  have hh := hc.rpow hp
  rw [div_mul_cancel₀ a hb.ne'] at hh
  convert hh using 1
  funext x
  rw [rpow_def_of_pos (exp_pos _), log_exp]
  congr 1
  field_simp

lemma exp_step_heat {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    {a : ℝ} (ha : a ≠ 0) (d : ℝ≥0) (x : ℝ) :
    exp (a*ParisiFinite.step a (sqrt d) f x) = heat d (fun y => exp (a*f y)) x := by
  rw [ParisiFinite.exp_step hf ha]
  have hm : Measure.map (fun z : ℝ => sqrt d*z) (gaussianReal 0 1) = gaussianReal 0 d := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp [sq_sqrt d.coe_nonneg]
  unfold heat
  rw [← hm, integral_map (by fun_prop)]
  exact ((continuous_const.mul (hf.continuous.comp (continuous_const.add continuous_id))).rexp).aestronglyMeasurable

lemma recursion_coshCone {β a : ℝ} (hβ : 0 < β) (ha : 0 < a)
    (ls : ParisiFinite.Schedule) (ho : ParisiGuerra.OrderedFrom β a ls) :
    CoshCone a (fun x => exp (a * ParisiFinite.recursion β ls x)) := by
  induction ls generalizing a with
  | nil =>
    apply CoshCone.exp_lower ha ho
    refine ⟨⟨2, fun _ => 0, by norm_num, PositiveDefinite.constant (by norm_num), by norm_num, ?_⟩⟩
    intro x
    simpa only [ParisiFinite.recursion, sub_zero] using ParisiFinite.exp_terminal hβ x
  | cons l ls ih =>
    have hb : 0 < (l.1:ℝ) := ha.trans_le ho.1
    have hh := (ih hb ho.2).heat
      ((continuous_const.mul (ParisiFinite.recursion_lipschitz hβ ls).continuous).rexp) l.2
    apply CoshCone.exp_lower ha ho.1
    convert hh using 1
    funext x
    exact exp_step_heat (ParisiFinite.recursion_lipschitz hβ ls) hb.ne' l.2 x

 

lemma field_coshCone (β : ℝ≥0) (hβ : 0 < β) {γ : ℝ≥0 → ℝ≥0}
    (hγ : Monotone γ) (hb : ∀ t, γ t ≤ β) (t : ℝ≥0) {a : ℝ}
    (ha : 0 < a) (hat : a ≤ γ t) :
    CoshCone a (fun x => exp (a*ParisiFinite.field β γ t x)) := by
  let ls (n : ℕ) := ParisiFinite.dyadicSchedule γ false t (1-t) n
  have ho (n : ℕ) : ParisiGuerra.OrderedFrom β a (ls n) :=
    ParisiFinite.ordered_lower hat (ParisiFinite.ordered_upper (by exact_mod_cast hb _)
      (ParisiFinite.dyadicSchedule_ordered hγ false t (1-t) n))
  apply CoshCone.limit ha.ne' (h := fun n x => exp (a*ParisiFinite.recursion β (ls n) x))
    (fun n => recursion_coshCone (by exact_mod_cast hβ) ha (ls n) (ho n))
  · intro x
    have hh := ParisiFinite.dyadic_low_tendsto
      (ParisiFinite.terminal_lipschitz (by exact_mod_cast hβ)) hγ t (1-t) x
    simp_rw [← ParisiFinite.recursion_eq_evolve] at hh
    exact Real.continuous_exp.continuousAt.tendsto.comp (hh.const_mul a)
  · exact exp_pos _

lemma field_negative_exp_positiveDefinite (β : ℝ≥0) (hβ : 0 < β)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t, γ t ≤ β)
    (t : ℝ≥0) (ht : 0 < γ t) {r : ℝ} (hr : 0 < r) :
    PositiveDefinite (fun x => exp (-r*ParisiFinite.field β γ t x)) := by
  have ha : 0 < (γ t:ℝ) := by exact_mod_cast ht
  have hh := (field_coshCone β hβ hγ hb t ha le_rfl).neg_rpow_positiveDefinite
    (div_pos hr ha)
  convert hh using 1
  funext x
  rw [rpow_def_of_pos (exp_pos _), log_exp]
  congr 1
  field_simp

end ParisiSpectral

end

end OAI
