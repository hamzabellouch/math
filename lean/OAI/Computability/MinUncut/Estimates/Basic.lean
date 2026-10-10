import Mathlib
import OAI.Computability.MinUncut.Model

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
namespace MinUncut.GaussianHermite
abbrev γ : Measure ℝ := gaussianReal 0 1

def he (n : ℕ) (x : ℝ) : ℝ := aeval x (hermite n)

lemma integrable_poly (p : ℝ[X]) : Integrable (fun x => p.eval x) γ := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [eval_add] using hp.fun_add hq
  | monomial n a =>
    have hn : Integrable (fun x : ℝ => x^n) γ :=
      integrable_pow_of_mem_interior_integrableExpSet (by simp [γ]) n
    simpa only [eval_monomial] using hn.const_mul a

lemma integrable_poly_density (p : ℝ[X]) :
    Integrable (fun x => p.eval x * gaussianPDFReal 0 1 x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [eval_add, add_mul] using hp.fun_add hq
  | monomial n a =>
    have hn := integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)
      (by exact lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n) : (-1:ℝ) < (n:ℝ))
    have heq : (fun x : ℝ => (monomial n a).eval x * gaussianPDFReal 0 1 x) =
      fun x : ℝ => (a * (Real.sqrt (2 * Real.pi))⁻¹) *
        (x^(n:ℝ) * Real.exp (-(1/2) * x^2)) := by
      funext x
      simp only [eval_monomial, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero,
        Real.rpow_natCast]
      rw [show -x^2 / (2:ℝ) = -(1/2) * x^2 by ring]
      ring
    rw [heq]
    exact hn.const_mul _

lemma density_derivative (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have h : HasDerivAt (fun x : ℝ => Real.exp (-(x^2/2)))
      (-x * Real.exp (-(x^2/2))) x := by
    convert (((hasDerivAt_id x).pow 2).div_const 2).neg.exp using 1 <;>
      simp only [id_eq, Pi.pow_apply, Pi.neg_apply]
    ring
  have heq : gaussianPDFReal 0 1 = fun x : ℝ =>
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x^2/2)) := by
    funext x
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, neg_div]
  rw [heq]
  apply (h.const_mul ((Real.sqrt (2 * Real.pi))⁻¹)).congr_deriv
  ring

lemma stein_poly (p : ℝ[X]) :
    (∫ x, x * p.eval x ∂γ) = ∫ x, p.derivative.eval x ∂γ := by
  have hi := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x => p.eval x) (v := gaussianPDFReal 0 1)
    (u' := fun x => p.derivative.eval x) (v' := fun x => -x * gaussianPDFReal 0 1 x)
    (fun x _ => p.hasDerivAt x) (fun x _ => density_derivative x)
    (by convert (integrable_poly_density (-(X*p))) using 1
        funext x; simp only [Pi.mul_apply, eval_neg, eval_mul, eval_X]; ring)
    (integrable_poly_density p.derivative)
    (integrable_poly_density p)
  have hleft : (∫ x, p.eval x * (-x * gaussianPDFReal 0 1 x)) =
      -(∫ x, x * p.eval x ∂γ) := by
    rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:NNReal) ≠ 0), ← integral_neg]
    congr 1
    funext x
    simp only [smul_eq_mul]
    ring
  rw [hleft] at hi
  rw [integral_gaussianReal_eq_integral_smul (f := fun x => p.derivative.eval x)
    (by norm_num : (1:NNReal) ≠ 0)]
  simp only [smul_eq_mul]
  have hr : (∫ x, p.derivative.eval x * gaussianPDFReal 0 1 x) =
      ∫ x, gaussianPDFReal 0 1 x * p.derivative.eval x := by
    congr 1; funext x; ring
  rw [hr] at hi
  linarith

def hePoly (n : ℕ) : ℝ[X] := (hermite n).map (Int.castRingHom ℝ)

@[simp] lemma hePoly_eval (n : ℕ) (x : ℝ) : (hePoly n).eval x = he n x := by
  simp [hePoly, he, aeval_def, eval_map]

@[simp] lemma hePoly_zero : hePoly 0 = 1 := by simp [hePoly]

lemma hePoly_succ (n : ℕ) : hePoly (n+1) = X * hePoly n - (hePoly n).derivative := by
  simp [hePoly, derivative_map]

lemma derivative_hePoly (n : ℕ) : (hePoly (n+1)).derivative = (n+1 : ℝ) • hePoly n := by
  induction n with
  | zero => simp [hePoly_succ]
  | succ n ih =>
    rw [hePoly_succ (n+1), derivative_sub, derivative_mul, derivative_X, one_mul, ih,
      derivative_smul, hePoly_succ n]
    simp only [Nat.cast_add, Nat.cast_one, smul_eq_C_mul, map_add, map_one]
    ring

lemma hePoly_adjoint (n : ℕ) (p : ℝ[X]) :
    (∫ x, he (n+1) x * p.eval x ∂γ) = ∫ x, he n x * p.derivative.eval x ∂γ := by
  have hi := stein_poly (hePoly n * p)
  have ha : Integrable (fun x => (hePoly n).derivative.eval x * p.eval x) γ := by
    simpa using integrable_poly ((hePoly n).derivative * p)
  have hb : Integrable (fun x => (hePoly n).eval x * p.derivative.eval x) γ := by
    simpa using integrable_poly (hePoly n * p.derivative)
  have hc : Integrable (fun x => x * (hePoly n).eval x * p.eval x) γ := by
    convert integrable_poly (X * hePoly n * p) using 1
    funext x; simp only [eval_mul, eval_X]
  simp only [eval_mul, derivative_mul, eval_add] at hi
  rw [integral_add ha hb] at hi
  have heq : (fun x => he (n+1) x * p.eval x) = fun x =>
      x * (hePoly n).eval x * p.eval x - (hePoly n).derivative.eval x * p.eval x := by
    funext x
    rw [← hePoly_eval, hePoly_succ]
    simp [sub_mul]
  rw [heq, integral_sub hc ha]
  simp only [hePoly_eval] at *
  simp only [mul_assoc] at *
  linarith

@[simp] lemma he_zero (x : ℝ) : he 0 x = 1 := by simp [he]

lemma he_mean_succ (n : ℕ) : (∫ x, he (n+1) x ∂γ) = 0 := by
  simpa using hePoly_adjoint n 1

lemma he_product (n m : ℕ) :
    (∫ x, he n x * he m x ∂γ) = if n = m then (n.factorial : ℝ) else 0 := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => simp [γ]
    | succ m => simp [he_mean_succ]
  | succ n ih =>
    cases m with
    | zero => simp [he_mean_succ]
    | succ m =>
      have h := hePoly_adjoint n (hePoly (m+1))
      rw [derivative_hePoly] at h
      simp only [hePoly_eval, eval_smul, smul_eq_mul] at h
      rw [show (fun x => he n x * ((m+1:ℝ) * he m x)) =
        fun x => (m+1:ℝ) * (he n x * he m x) by funext x; ring,
        integral_const_mul, ih] at h
      rw [h]
      by_cases hnm : n = m
      · subst m; simp [Nat.factorial_succ]
      · simp [hnm]

lemma measure_eq_of_moments {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : integrableExpSet id μ = Set.univ) (hν : integrableExpSet id ν = Set.univ)
    (hm : ∀ n : ℕ, (∫ x, x^n ∂μ) = ∫ x, x^n ∂ν) : μ = ν := by
  have haμ : AnalyticOnNhd ℂ (complexMGF id μ) Set.univ := by
    intro z _
    exact analyticAt_complexMGF (by simp [hμ])
  have haν : AnalyticOnNhd ℂ (complexMGF id ν) Set.univ := by
    intro z _
    exact analyticAt_complexMGF (by simp [hν])
  let d := fun z => complexMGF id μ z - complexMGF id ν z
  have hd : AnalyticAt ℂ d 0 := (haμ 0 (Set.mem_univ _)).sub (haν 0 (Set.mem_univ _))
  have hdn (n : ℕ) : iteratedDeriv n d 0 = 0 := by
    rw [show d = fun z => complexMGF id μ z - complexMGF id ν z from rfl,
      iteratedDeriv_fun_sub (haμ 0 (Set.mem_univ _)).contDiffAt
        (haν 0 (Set.mem_univ _)).contDiffAt,
      iteratedDeriv_complexMGF (by simp [hμ]), iteratedDeriv_complexMGF (by simp [hν])]
    simp only [zero_mul, Complex.exp_zero, mul_one, id_eq]
    rw [show (fun x : ℝ => (x:ℂ)^n) = fun x : ℝ => ((x^n:ℝ):ℂ) by ext x; simp,
      integral_complex_ofReal, integral_complex_ofReal, hm n]
    simp
  have ht : analyticOrderAt d (0:ℂ) = ⊤ := by
    rw [ENat.eq_top_iff_forall_ge]
    intro n
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hd).mpr (fun i _ => hdn i)
  have he : complexMGF id μ =ᶠ[𝓝 (0:ℂ)] complexMGF id ν := by
    filter_upwards [analyticOrderAt_eq_top.mp ht] with z hz
    exact sub_eq_zero.mp hz
  apply Measure.ext_of_complexMGF_id_eq
  funext z
  exact haμ.eqOn_of_preconnected_of_eventuallyEq haν isPreconnected_univ (Set.mem_univ 0) he
    (Set.mem_univ z)

lemma memLp_poly (p : ℝ[X]) : MemLp (fun x => p.eval x) 2 γ := by
  apply (memLp_two_iff_integrable_sq (p.continuous.aestronglyMeasurable)).mpr
  convert integrable_poly (p^2) using 1
  funext x
  rw [Polynomial.eval_pow]

lemma memLp_exp (t : ℝ) : MemLp (fun x => Real.exp (t*x)) 2 γ := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  convert integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (2*t) using 1
  funext x
  rw [← Real.exp_nat_mul]
  congr 1
  ring

lemma memLp_positivePart {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    MemLp (fun x => max (f x) 0) 2 μ := by
  apply hf.mono ((hf.aestronglyMeasurable.aemeasurable.max aemeasurable_const).aestronglyMeasurable)
  filter_upwards [] with x
  simp only [Real.norm_eq_abs, abs_of_nonneg (le_max_right (f x) (0:ℝ))]
  exact max_le (le_abs_self _) (abs_nonneg _)

lemma weighted_finite {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {w : Ω → ℝ} (hw : MemLp w 2 μ) :
    IsFiniteMeasure (μ.withDensity (fun x => ENNReal.ofReal (w x))) :=
  isFiniteMeasure_withDensity (hw.integrable (by norm_num)).lintegral_lt_top.ne

lemma weighted_expSet {w : ℝ → ℝ} (hw : MemLp w 2 γ) (hwn : ∀ x, 0 ≤ w x) :
    integrableExpSet id (γ.withDensity (fun x => ENNReal.ofReal (w x))) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro t
  show Integrable (fun x => Real.exp (t*x)) _
  rw [integrable_withDensity_iff_integrable_smul₀'
    hw.aestronglyMeasurable.aemeasurable.ennreal_ofReal (by simp)]
  simpa only [ENNReal.toReal_ofReal (hwn _), smul_eq_mul, Pi.mul_def] using
    hw.integrable_mul (memLp_exp t)

lemma integral_weighted {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {w : Ω → ℝ} (hw : MemLp w 2 μ) (hwn : ∀ x, 0 ≤ w x)
    (q : Ω → ℝ) :
    (∫ x, q x ∂μ.withDensity (fun x => ENNReal.ofReal (w x))) = ∫ x, w x * q x ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul₀
    hw.aestronglyMeasurable.aemeasurable.ennreal_ofReal (by simp)]
  simp only [ENNReal.toReal_ofReal (hwn _), smul_eq_mul]

lemma ae_zero_of_integral_poly_eq_zero {f : ℝ → ℝ} (hf : MemLp f 2 γ)
    (horth : ∀ p : ℝ[X], (∫ x, f x * p.eval x ∂γ) = 0) : f =ᵐ[γ] 0 := by
  let p := fun x => max (f x) 0
  let n := fun x => max (-f x) 0
  have hp : MemLp p 2 γ := memLp_positivePart hf
  have hn : MemLp n 2 γ := memLp_positivePart hf.neg
  have hpn : ∀ x, 0 ≤ p x := fun x => le_max_right _ _
  have hnn : ∀ x, 0 ≤ n x := fun x => le_max_right _ _
  let μ := γ.withDensity (fun x => ENNReal.ofReal (p x))
  let ν := γ.withDensity (fun x => ENNReal.ofReal (n x))
  let : IsFiniteMeasure μ := weighted_finite hp
  let : IsFiniteMeasure ν := weighted_finite hn
  have hμν : μ = ν := by
    apply measure_eq_of_moments (weighted_expSet hp hpn) (weighted_expSet hn hnn)
    intro k
    rw [integral_weighted hp hpn, integral_weighted hn hnn]
    have hi := horth (X^k)
    have hk := memLp_poly (X^k)
    simp only [eval_pow, eval_X] at hi hk
    have heq : (fun x => f x * x^k) = fun x => p x * x^k - n x * x^k := by
      funext x
      dsimp [p,n]
      rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self]
    have hip : Integrable (fun x => p x * x^k) γ := by simpa only [Pi.mul_def] using hp.integrable_mul hk
    have hin : Integrable (fun x => n x * x^k) γ := by simpa only [Pi.mul_def] using hn.integrable_mul hk
    rw [heq, integral_sub hip hin] at hi
    exact sub_eq_zero.mp hi
  have hae := (withDensity_eq_iff_of_sigmaFinite
    hp.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    hn.aestronglyMeasurable.aemeasurable.ennreal_ofReal).mp hμν
  filter_upwards [hae] with x hx
  have heq := congrArg ENNReal.toReal hx
  rw [ENNReal.toReal_ofReal (hpn x), ENNReal.toReal_ofReal (hnn x)] at heq
  have hd : p x - n x = f x := by dsimp [p,n]; exact max_zero_sub_max_neg_zero_eq_self _
  change f x = 0
  linarith

def heSequence : Polynomial.Sequence ℝ where
  elems' := hePoly
  degree_eq' n := by
    rw [hePoly, (hermite_monic n).degree_map, degree_hermite]

lemma heSequence_span : Submodule.span ℝ (Set.range hePoly) = ⊤ := by
  apply heSequence.span
  intro n
  change IsUnit (hePoly n).leadingCoeff
  rw [show (hePoly n).leadingCoeff = 1 from ((hermite_monic n).map _).leadingCoeff]
  exact isUnit_one

lemma ae_zero_of_integral_he_eq_zero {f : ℝ → ℝ} (hf : MemLp f 2 γ)
    (horth : ∀ n, (∫ x, f x * he n x ∂γ) = 0) : f =ᵐ[γ] 0 := by
  apply ae_zero_of_integral_poly_eq_zero hf
  intro p
  have hp : p ∈ Submodule.span ℝ (Set.range hePoly) := by rw [heSequence_span]; trivial
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨n,rfl⟩ := hp
    simpa only [hePoly_eval] using horth n
  | zero => simp
  | add p q hp hq ihp ihq =>
    have hi (q : ℝ[X]) : Integrable (fun x => f x * q.eval x) γ := by
      simpa only [Pi.mul_def] using hf.integrable_mul (memLp_poly q)
    simp only [eval_add, mul_add, integral_add (hi p) (hi q), ihp, ihq, add_zero]
  | smul a p hp ih =>
    simp only [eval_smul, smul_eq_mul]
    rw [show (fun x => f x * (a * p.eval x)) = fun x => a * (f x * p.eval x) by
      funext x; ring, integral_const_mul, ih, mul_zero]

def H (n : ℕ) (x : ℝ) : ℝ := he n x / Real.sqrt (n.factorial : ℝ)

lemma sqrt_factorial_pos (n : ℕ) : 0 < Real.sqrt (n.factorial : ℝ) := by
  positivity

lemma memLp_H (n : ℕ) : MemLp (H n) 2 γ := by
  change MemLp (fun x => he n x / Real.sqrt (n.factorial : ℝ)) 2 γ
  simpa only [ div_eq_mul_inv, hePoly_eval] using (memLp_poly (hePoly n)).mul_const
    (Real.sqrt (n.factorial : ℝ))⁻¹

lemma H_product (n m : ℕ) :
    (∫ x, H n x * H m x ∂γ) = if n = m then 1 else 0 := by
  simp only [H, div_mul_div_comm]
  rw [integral_div, he_product]
  split_ifs with h
  · subst m
    rw [Real.mul_self_sqrt (Nat.cast_nonneg _)]
    exact div_self (by positivity)
  · exact zero_div _

lemma integral_inner_toLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ ω, f ω * g ω ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with ω hfω hgω
  simp only [hfω, hgω, RCLike.inner_apply, conj_trivial, mul_comm]

def Hvec (n : ℕ) : Lp ℝ 2 γ := (memLp_H n).toLp (H n)

lemma Hvec_orthonormal : Orthonormal ℝ Hvec := by
  rw [orthonormal_iff_ite]
  intro n m
  simpa only [Hvec, integral_inner_toLp] using H_product n m

lemma eq_zero_of_inner_Hvec_eq_zero (f : Lp ℝ 2 γ)
    (h : ∀ n, inner ℝ f (Hvec n) = 0) : f = 0 := by
  have hae : (f : ℝ → ℝ) =ᵐ[γ] 0 := by
    apply ae_zero_of_integral_he_eq_zero (Lp.memLp f)
    intro n
    have hi := h n
    rw [L2.inner_def] at hi
    have hieq : (∫ x, inner ℝ (f x) ((Hvec n) x) ∂γ) =
        (∫ x, f x * he n x ∂γ) / Real.sqrt (n.factorial : ℝ) := by
      rw [← integral_div]
      apply integral_congr_ae
      filter_upwards [(memLp_H n).coeFn_toLp] with x hx
      simp only [Hvec] at *
      rw [hx]
      simp [H, mul_div_assoc, mul_comm]
    rw [hieq] at hi
    exact (div_eq_zero_iff).mp hi |>.resolve_right (ne_of_gt (sqrt_factorial_pos n))
  apply Lp.ext
  exact hae.trans (Lp.coeFn_zero ℝ 2 γ).symm

def hermiteBasis : HilbertBasis ℕ ℝ (Lp ℝ 2 γ) :=
  HilbertBasis.mkOfOrthogonalEqBot Hvec_orthonormal (by
    apply eq_bot_iff.mpr
    intro f hf
    change f = 0
    apply eq_zero_of_inner_Hvec_eq_zero f
    intro n
    exact (Submodule.mem_orthogonal' _ f).mp hf _
      (Submodule.subset_span (Set.mem_range_self n)))

section Product
variable {ι : Type*} [Fintype ι]
abbrev γpi (ι : Type*) [Fintype ι] : Measure (ι → ℝ) := Measure.pi (fun _ => γ)

lemma memLp_polyProd (p : ι → ℝ[X]) :
    MemLp (fun x : ι → ℝ => ∏ i, (p i).eval (x i)) 2 (γpi ι) := by
  apply (memLp_two_iff_integrable_sq
    (continuous_finsetProd _ (fun i _ => (p i).continuous.comp (continuous_apply i))).aestronglyMeasurable).mpr
  simpa only [Finset.prod_pow, Function.comp_def] using Integrable.fintype_prod
    (fun i => (memLp_two_iff_integrable_sq (by fun_prop)).mp (memLp_poly (p i)))

def polyProdMap : MultilinearMap ℝ (fun _ : ι => ℝ[X]) ((ι → ℝ) → ℝ) :=
  (MultilinearMap.mkPiAlgebra ℝ ι ((ι → ℝ) → ℝ)).compLinearMap (fun i =>
    { toFun := fun p x => p.eval (x i)
      map_add' := by intros; ext x; simp
      map_smul' := by intros; ext x; simp })

lemma polyProdMap_apply (p : ι → ℝ[X]) (x : ι → ℝ) :
    polyProdMap p x = ∏ i, (p i).eval (x i) := by
  simp [polyProdMap, MultilinearMap.mkPiAlgebra_apply]

def orthPolyMap {f : (ι → ℝ) → ℝ} (hf : MemLp f 2 (γpi ι)) :
    MultilinearMap ℝ (fun _ : ι => ℝ[X]) ℝ where
  toFun p := ∫ x, f x * polyProdMap p x ∂γpi ι
  map_update_add' p i a b := by
    rw [polyProdMap.map_update_add]
    simp only [Pi.add_apply, mul_add]
    apply integral_add <;>
      simpa only [polyProdMap_apply, Pi.mul_def] using hf.integrable_mul (memLp_polyProd _)
  map_update_smul' p i a b := by
    rw [polyProdMap.map_update_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show (fun x => f x * (a * polyProdMap (Function.update p i b) x)) =
      fun x => a * (f x * polyProdMap (Function.update p i b) x) by funext x; ring]
    exact integral_const_mul _ _

lemma heLeadingUnit (n : ℕ) : IsUnit (heSequence n).leadingCoeff := by
  change IsUnit (hePoly n).leadingCoeff
  rw [show (hePoly n).leadingCoeff = 1 from ((hermite_monic n).map _).leadingCoeff]
  exact isUnit_one

lemma ortho_polyProd_of_heProd {f : (ι → ℝ) → ℝ} (hf : MemLp f 2 (γpi ι))
    (h : ∀ a : ι → ℕ, (∫ x, f x * ∏ i, he (a i) (x i) ∂γpi ι) = 0)
    (p : ι → ℝ[X]) : (∫ x, f x * ∏ i, (p i).eval (x i) ∂γpi ι) = 0 := by
  have heq : orthPolyMap hf = 0 := by
    apply Module.Basis.ext_multilinear (fun _ => heSequence.basis heLeadingUnit)
    intro a
    simpa only [orthPolyMap, MultilinearMap.coe_mk, polyProdMap_apply,
      Sequence.basis_eq_self, show (fun i => heSequence (a i)) = fun i => hePoly (a i) from rfl,
      hePoly_eval, zero_apply] using h a
  simpa only [orthPolyMap, MultilinearMap.coe_mk, polyProdMap_apply, zero_apply] using
    congrArg (fun q => q p) heq

lemma memLp_exp_linear (L : (ι → ℝ) →L[ℝ] ℝ) (t : ℝ) :
    MemLp (fun x => Real.exp (t * L x)) 2 (γpi ι) := by
  classical
  have heq (x : ι → ℝ) : Real.exp (t * L x) =
      ∏ i, Real.exp ((t * L (Pi.single i 1)) * x i) := by
    rw [← Real.exp_sum]
    congr 1
    rw [← ContinuousLinearMap.sum_comp_single ℝ (fun _ : ι => ℝ) L x, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply]
    rw [show Pi.single i (x i) = x i • Pi.single i (1:ℝ) by
      simpa only [smul_eq_mul, mul_one] using (Pi.single_smul (f := fun _ : ι => ℝ) i (x i) (1:ℝ))]
    simp [mul_comm, mul_left_comm]
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  simp_rw [heq, ← Finset.prod_pow]
  exact Integrable.fintype_prod (fun i =>
    (memLp_two_iff_integrable_sq (by fun_prop)).mp (memLp_exp (t * L (Pi.single i 1))))

lemma memLp_mvpoly (p : MvPolynomial ι ℝ) :
    MemLp (fun x => MvPolynomial.eval x p) 2 (γpi ι) := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simpa only [MvPolynomial.eval_add, Pi.add_def] using hp.add hq
  | monomial m a =>
    simpa only [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      Polynomial.eval_pow, Polynomial.eval_X] using
      (memLp_polyProd (fun i : ι => (X : ℝ[X])^(m i))).const_mul a

lemma ortho_mvpoly_of_polyProd {f : (ι → ℝ) → ℝ} (hf : MemLp f 2 (γpi ι))
    (h : ∀ p : ι → ℝ[X], (∫ x, f x * ∏ i, (p i).eval (x i) ∂γpi ι) = 0)
    (p : MvPolynomial ι ℝ) : (∫ x, f x * MvPolynomial.eval x p ∂γpi ι) = 0 := by
  have hi (p : MvPolynomial ι ℝ) : Integrable (fun x => f x * MvPolynomial.eval x p) (γpi ι) := by
    simpa only [Pi.mul_def] using hf.integrable_mul (memLp_mvpoly p)
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => rw [show (fun x => f x * MvPolynomial.eval x (p+q)) =
        fun x => f x * MvPolynomial.eval x p + f x * MvPolynomial.eval x q by
          funext x; simp [mul_add], integral_add (hi p) (hi q), hp, hq, add_zero]
  | monomial m a =>
    simp only [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    rw [show (fun x => f x * (a * ∏ i, x i ^ m i)) =
        fun x => a * (f x * ∏ i, x i ^ m i) by funext x; ring, integral_const_mul]
    have hh := h (fun i => (X : ℝ[X]) ^ m i)
    simp only [Polynomial.eval_pow, Polynomial.eval_X] at hh
    rw [hh, mul_zero]

def linearPoly [DecidableEq ι] (L : (ι → ℝ) →L[ℝ] ℝ) : MvPolynomial ι ℝ :=
  ∑ i, MvPolynomial.C (L (Pi.single i 1)) * MvPolynomial.X i

lemma eval_linearPoly [DecidableEq ι] (L : (ι → ℝ) →L[ℝ] ℝ) (x : ι → ℝ) :
    MvPolynomial.eval x (linearPoly L) = L x := by
  simp only [linearPoly, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  rw [← ContinuousLinearMap.sum_comp_single ℝ (fun _ : ι => ℝ) L x]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply]
  rw [show Pi.single i (x i) = x i • Pi.single i (1:ℝ) by
      simpa only [smul_eq_mul, mul_one] using (Pi.single_smul (f := fun _ : ι => ℝ) i (x i) (1:ℝ))]
  simp [mul_comm]

lemma weighted_linear_expSet {w : (ι → ℝ) → ℝ} (hw : MemLp w 2 (γpi ι))
    (hwn : ∀ x, 0 ≤ w x) (L : (ι → ℝ) →L[ℝ] ℝ) :
    integrableExpSet id ((γpi ι).withDensity (fun x => ENNReal.ofReal (w x)) |>.map L) =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro t
  show Integrable (fun x => Real.exp (t*x)) _
  rw [integrable_map_measure (by fun_prop) (by fun_prop)]
  rw [integrable_withDensity_iff_integrable_smul₀'
    hw.aestronglyMeasurable.aemeasurable.ennreal_ofReal (by simp)]
  simpa only [Function.comp_def, ENNReal.toReal_ofReal (hwn _), smul_eq_mul, Pi.mul_def] using
    hw.integrable_mul (memLp_exp_linear L t)

lemma ae_zero_of_integral_mvpoly_eq_zero {f : (ι → ℝ) → ℝ} (hf : MemLp f 2 (γpi ι))
    (horth : ∀ p : MvPolynomial ι ℝ, (∫ x, f x * MvPolynomial.eval x p ∂γpi ι) = 0) :
    f =ᵐ[γpi ι] 0 := by
  classical
  let p := fun x => max (f x) 0
  let n := fun x => max (-f x) 0
  have hp : MemLp p 2 (γpi ι) := memLp_positivePart hf
  have hn : MemLp n 2 (γpi ι) := memLp_positivePart hf.neg
  have hpn : ∀ x, 0 ≤ p x := fun x => le_max_right _ _
  have hnn : ∀ x, 0 ≤ n x := fun x => le_max_right _ _
  let μ := (γpi ι).withDensity (fun x => ENNReal.ofReal (p x))
  let ν := (γpi ι).withDensity (fun x => ENNReal.ofReal (n x))
  let : IsFiniteMeasure μ := weighted_finite hp
  let : IsFiniteMeasure ν := weighted_finite hn
  have hμν : μ = ν := by
    apply Measure.ext_of_charFunDual
    funext L
    rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one]
    have hh : μ.map L = ν.map L := by
      apply measure_eq_of_moments (weighted_linear_expSet hp hpn L)
        (weighted_linear_expSet hn hnn L)
      intro k
      rw [integral_map (by fun_prop) (by fun_prop), integral_map (by fun_prop) (by fun_prop)]
      rw [integral_weighted hp hpn, integral_weighted hn hnn]
      have hi := horth ((linearPoly L)^k)
      have hk := memLp_mvpoly ((linearPoly L)^k)
      simp only [map_pow, eval_linearPoly] at hi hk
      have heq : (fun x => f x * (L x)^k) = fun x => p x * (L x)^k - n x * (L x)^k := by
        funext x
        dsimp [p,n]
        rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self]
      have hip : Integrable (fun x => p x * (L x)^k) (γpi ι) := by
        simpa only [Pi.mul_def] using hp.integrable_mul hk
      have hin : Integrable (fun x => n x * (L x)^k) (γpi ι) := by
        simpa only [Pi.mul_def] using hn.integrable_mul hk
      rw [heq, integral_sub hip hin] at hi
      exact sub_eq_zero.mp hi
    rw [hh]
  have hae := (withDensity_eq_iff_of_sigmaFinite
    hp.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    hn.aestronglyMeasurable.aemeasurable.ennreal_ofReal).mp hμν
  filter_upwards [hae] with x hx
  have heq := congrArg ENNReal.toReal hx
  rw [ENNReal.toReal_ofReal (hpn x), ENNReal.toReal_ofReal (hnn x)] at heq
  have hd : p x - n x = f x := by dsimp [p,n]; exact max_zero_sub_max_neg_zero_eq_self _
  change f x = 0
  linarith

def psi (a : ι → ℕ) (x : ι → ℝ) : ℝ := ∏ i, H (a i) (x i)

lemma continuous_H (n : ℕ) : Continuous (H n) := by
  change Continuous (fun x => he n x / Real.sqrt (n.factorial : ℝ))
  simpa only [hePoly_eval] using (hePoly n).continuous.div_const _

lemma memLp_psi (a : ι → ℕ) : MemLp (psi a) 2 (γpi ι) := by
  apply (memLp_two_iff_integrable_sq
    (continuous_finsetProd _ (fun i _ => (continuous_H (a i)).comp (continuous_apply i))).aestronglyMeasurable).mpr
  simpa only [psi, Function.comp_def, Finset.prod_pow] using Integrable.fintype_prod
    (fun i => (memLp_two_iff_integrable_sq (continuous_H (a i)).aestronglyMeasurable).mp (memLp_H (a i)))

lemma psi_product (a b : ι → ℕ) :
    (∫ x, psi a x * psi b x ∂γpi ι) = if a = b then 1 else 0 := by
  classical
  simp only [psi, ← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_eq_prod (f := fun i (t : ℝ) => H (a i) t * H (b i) t)
    (μ := fun _ => γ)]
  simp only [H_product]
  by_cases hab : a = b
  · simp [hab]
  · rw [ite_eq_right hab]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hab
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

lemma heProd_eq (a : ι → ℕ) (x : ι → ℝ) :
    (∏ i, he (a i) (x i)) = (∏ i, Real.sqrt ((a i).factorial : ℝ)) * psi a x := by
  rw [psi, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [H, mul_div_cancel₀ _ (ne_of_gt (sqrt_factorial_pos _))]

lemma ae_zero_of_integral_psi_eq_zero {f : (ι → ℝ) → ℝ} (hf : MemLp f 2 (γpi ι))
    (horth : ∀ a, (∫ x, f x * psi a x ∂γpi ι) = 0) : f =ᵐ[γpi ι] 0 := by
  apply ae_zero_of_integral_mvpoly_eq_zero hf
  apply ortho_mvpoly_of_polyProd hf
  apply ortho_polyProd_of_heProd hf
  intro a
  simp only [heProd_eq]
  rw [show (fun x => f x * ((∏ i, Real.sqrt ((a i).factorial : ℝ)) * psi a x)) =
      fun x => (∏ i, Real.sqrt ((a i).factorial : ℝ)) * (f x * psi a x) by funext x; ring,
    integral_const_mul, horth a, mul_zero]

def psiVec (a : ι → ℕ) : Lp ℝ 2 (γpi ι) := (memLp_psi a).toLp (psi a)

lemma psiVec_orthonormal : Orthonormal ℝ (psiVec (ι := ι)) := by
  rw [orthonormal_iff_ite]
  intro a b
  simpa only [psiVec, integral_inner_toLp] using psi_product a b

lemma eq_zero_of_inner_psiVec_eq_zero (f : Lp ℝ 2 (γpi ι))
    (h : ∀ a, inner ℝ f (psiVec a) = 0) : f = 0 := by
  have hae : (f : (ι → ℝ) → ℝ) =ᵐ[γpi ι] 0 := by
    apply ae_zero_of_integral_psi_eq_zero (Lp.memLp f)
    intro a
    have hi := h a
    rw [L2.inner_def] at hi
    convert hi using 1
    apply integral_congr_ae
    filter_upwards [(memLp_psi a).coeFn_toLp] with x hx
    simp only [psiVec, hx, RCLike.inner_apply, conj_trivial, mul_comm]
  apply Lp.ext
  exact hae.trans (Lp.coeFn_zero ℝ 2 (γpi ι)).symm

def productHermiteBasis : HilbertBasis (ι → ℕ) ℝ (Lp ℝ 2 (γpi ι)) :=
  HilbertBasis.mkOfOrthogonalEqBot psiVec_orthonormal (by
    apply eq_bot_iff.mpr
    intro f hf
    change f = 0
    apply eq_zero_of_inner_psiVec_eq_zero f
    intro a
    exact (Submodule.mem_orthogonal' _ f).mp hf _
      (Submodule.subset_span (Set.mem_range_self a)))

end Product

def affinePoly (r s : ℝ) : ℝ[X] := C r + C s * X
@[simp] lemma eval_affinePoly (r s x : ℝ) : (affinePoly r s).eval x = r+s*x := by
  simp [affinePoly]
@[simp] lemma derivative_affinePoly (r s : ℝ) : (affinePoly r s).derivative = C s := by
  simp [affinePoly]

lemma integrable_he_affine (n : ℕ) (r s : ℝ) :
    Integrable (fun x => he n (r+s*x)) γ := by
  simpa only [eval_comp, eval_affinePoly, hePoly_eval] using
    integrable_poly ((hePoly n).comp (affinePoly r s))

lemma integrable_mul_he_affine (n : ℕ) (r s : ℝ) :
    Integrable (fun x => x * he n (r+s*x)) γ := by
  convert integrable_poly (X * (hePoly n).comp (affinePoly r s)) using 1
  funext x
  simp only [Polynomial.eval_mul, eval_X, eval_comp, eval_affinePoly, hePoly_eval]

lemma stein_he_affine (n : ℕ) (r s : ℝ) :
    (∫ x, x * he (n+1) (r+s*x) ∂γ) = ((n+1:ℝ)*s) * ∫ x, he n (r+s*x) ∂γ := by
  have h := stein_poly ((hePoly (n+1)).comp (affinePoly r s))
  simp only [derivative_comp, derivative_hePoly, derivative_affinePoly, eval_comp,
    eval_affinePoly, hePoly_eval, eval_mul, eval_C, eval_smul, smul_eq_mul] at h
  rw [h, show (fun x => s * ((n+1:ℝ) * he n (r+s*x))) =
    fun x => ((n+1:ℝ)*s) * he n (r+s*x) by funext x; ring, integral_const_mul]

@[simp] lemma he_one (x : ℝ) : he 1 x = x := by
  rw [← hePoly_eval, show hePoly 1 = X by simp [hePoly_succ]]
  simp

lemma he_recurrence (n : ℕ) (x : ℝ) :
    he (n+2) x = x * he (n+1) x - (n+1:ℝ) * he n x := by
  rw [← hePoly_eval, show n+2 = (n+1)+1 by omega, hePoly_succ, derivative_hePoly]
  simp

lemma he_noise (ρ s c : ℝ) (h : ρ^2+s^2=1) (n : ℕ) :
    (∫ g, he n (ρ*c+s*g) ∂γ) = ρ^n * he n c := by
  induction n using Nat.twoStepInduction with
  | zero => simp [γ]
  | one =>
    have hi : Integrable (fun x : ℝ => x) γ := by simpa using integrable_poly X
    simp only [he_one, pow_one]
    rw [integral_add (integrable_const _) (hi.const_mul s), integral_const_mul]
    rw [integral_const_mul s]
    simp [γ]
  | more n ih0 ih1 =>
    have hi0 := integrable_he_affine n (ρ*c) s
    have hi1 := integrable_he_affine (n+1) (ρ*c) s
    have hig := integrable_mul_he_affine (n+1) (ρ*c) s
    have heq : (fun g => he (n+2) (ρ*c+s*g)) = fun g =>
        (ρ*c) * he (n+1) (ρ*c+s*g) + s*(g * he (n+1) (ρ*c+s*g)) -
        (n+1:ℝ)*he n (ρ*c+s*g) := by
      funext g
      rw [he_recurrence]
      ring
    rw [heq, integral_sub ((hi1.const_mul (ρ*c)).fun_add (hig.const_mul s)) (hi0.const_mul (n+1:ℝ)),
      integral_add (hi1.const_mul _) (hig.const_mul _)]
    simp only [integral_const_mul, stein_he_affine, ih0, ih1, he_recurrence, pow_succ]
    have hh : s*s = 1-ρ*ρ := by nlinarith [h]
    calc
      _ = ρ^n*ρ*ρ*c*he (n+1) c + ((s*s)-1)*((n+1:ℝ)*ρ^n*he n c) := by ring
      _ = _ := by rw [hh]; ring

lemma H_noise (ρ s c : ℝ) (h : ρ^2+s^2=1) (n : ℕ) :
    (∫ g, H n (ρ*c+s*g) ∂γ) = ρ^n * H n c := by
  simp only [H, integral_div, he_noise ρ s c h, mul_div_assoc]

variable {ι : Type*} [Fintype ι]

lemma psi_noise (ρ s : ℝ) (h : ρ^2+s^2=1) (a : ι → ℕ) (c : ι → ℝ) :
    (∫ g, psi a (fun i => ρ*c i+s*g i) ∂γpi ι) = ρ^(∑ i, a i)*psi a c := by
  simp only [psi]
  rw [integral_fintype_prod_eq_prod (f := fun i (t : ℝ) => H (a i) (ρ*c i+s*t))]
  simp only [H_noise ρ s _ h, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

lemma charFunDual_gamma (L : ℝ →L[ℝ] ℝ) :
    charFunDual γ L = Complex.exp ((-(L 1)^2 / 2 : ℝ) : ℂ) := by
  rw [charFunDual_eq_charFun_map_one, γ, gaussianReal_map_continuousLinearMap,
    charFun_gaussianReal]
  simp [Real.coe_toNNReal _ (sq_nonneg _), neg_div]

lemma charFunDual_gammaPi [DecidableEq ι] (L : (ι → ℝ) →L[ℝ] ℝ) :
    charFunDual (γpi ι) L =
      Complex.exp ((-(∑ i, (L (Pi.single i 1))^2) / 2 : ℝ) : ℂ) := by
  classical
  rw [γpi, charFunDual_pi]
  simp only [charFunDual_gamma, ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply]
  rw [← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_sum,
    Complex.ofReal_pow, Complex.ofReal_ofNat]
  rw [← Finset.sum_div, Finset.sum_neg_distrib]

def rotation (ρ s : ℝ) : ((ι → ℝ) × (ι → ℝ)) →L[ℝ] ((ι → ℝ) × (ι → ℝ)) :=
  (ρ • ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ) +
    s • ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ)).prod
  (s • ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ) -
    ρ • ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ))

omit [Fintype ι] in
@[simp] lemma rotation_apply (ρ s : ℝ) (x : (ι → ℝ) × (ι → ℝ)) :
    rotation ρ s x = (ρ • x.1 + s • x.2, s • x.1 - ρ • x.2) := rfl

omit [Fintype ι] in
lemma rotation_involutive (ρ s : ℝ) (h : ρ^2+s^2=1) :
    Function.Involutive (rotation (ι := ι) ρ s) := by
  intro x
  ext i <;> simp only [rotation_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  · calc
      _ = (ρ^2+s^2)*x.1 i := by ring
      _ = x.1 i := by rw [h, one_mul]
  · calc
      _ = (ρ^2+s^2)*x.2 i := by ring
      _ = x.2 i := by rw [h, one_mul]

lemma rotation_preserves (ρ s : ℝ) (h : ρ^2+s^2=1) :
    MeasurePreserving (rotation (ι := ι) ρ s) ((γpi ι).prod (γpi ι))
      ((γpi ι).prod (γpi ι)) := by
  classical
  refine ⟨by fun_prop, ?_⟩
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_map, charFunDual_prod, charFunDual_prod]
  simp only [charFunDual_gammaPi, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply]
  have h1 (i : ι) : L (rotation ρ s (Pi.single i 1, 0)) =
      ρ * L (Pi.single i 1, 0) + s * L (0, Pi.single i 1) := by
    rw [show rotation ρ s (Pi.single i 1, 0) =
        ρ • (Pi.single i 1, 0) + s • (0, Pi.single i 1) by
          ext j <;> simp [rotation_apply]]
    simp only [map_add, map_smul, smul_eq_mul]
  have h2 (i : ι) : L (rotation ρ s (0, Pi.single i 1)) =
      s * L (Pi.single i 1, 0) - ρ * L (0, Pi.single i 1) := by
    rw [show rotation ρ s (0, Pi.single i 1) =
        s • (Pi.single i 1, 0) - ρ • (0, Pi.single i 1) by
          ext j <;> simp [rotation_apply]]
    simp only [map_sub, map_smul, smul_eq_mul]
  simp only [h1, h2]
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.ofReal_add, ← Complex.ofReal_add]
  congr 1
  apply congrArg Complex.ofReal
  have hsum : (∑ i, (ρ * L (Pi.single i 1, 0) + s * L (0, Pi.single i 1))^2) +
      (∑ i, (s * L (Pi.single i 1, 0) - ρ * L (0, Pi.single i 1))^2) =
      (∑ i, (L (Pi.single i 1, 0))^2) + (∑ i, (L (0, Pi.single i 1))^2) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = (ρ^2+s^2)*((L (Pi.single i 1, 0))^2+(L (0, Pi.single i 1))^2) := by ring
      _ = _ := by rw [h, one_mul]
  linarith

def noise (ρ s : ℝ) (Q : (ι → ℝ) → ℝ) (x : ι → ℝ) : ℝ :=
  ∫ y, Q (ρ • x + s • y) ∂γpi ι

lemma measurable_noise (ρ s : ℝ) {Q : (ι → ℝ) → ℝ} (hQ : Measurable Q) :
    Measurable (noise ρ s Q) := by
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.integral_prod_right
  exact (hQ.comp (by fun_prop : Measurable (fun z : (ι → ℝ) × (ι → ℝ) =>
    ρ • z.1+s • z.2))).stronglyMeasurable

lemma psi_integrable (a : ι → ℕ) : Integrable (psi a) (γpi ι) :=
  (memLp_psi a).integrable (by norm_num)

lemma continuous_psi (a : ι → ℕ) : Continuous (psi a) := by
  unfold psi H he
  fun_prop

lemma noise_bound (ρ s : ℝ) {Q : (ι → ℝ) → ℝ} (hQ : ∀ x, |Q x| ≤ 1) (x : ι → ℝ) :
    |noise ρ s Q x| ≤ 1 := by
  simpa [noise, ← Real.norm_eq_abs] using norm_integral_le_of_norm_le_const
    (μ := γpi ι) (f := fun y => Q (ρ • x+s • y)) (C := 1)
      (ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using hQ _)

lemma noise_coefficient (ρ s : ℝ) (h : ρ^2+s^2=1) {Q : (ι → ℝ) → ℝ}
    (hQ : Measurable Q) (hb : ∀ x, |Q x| ≤ 1) (a : ι → ℕ) :
    (∫ x, psi a x * noise ρ s Q x ∂γpi ι) =
      ρ^(∑ i, a i) * ∫ x, psi a x * Q x ∂γpi ι := by
  let μ := (γpi ι).prod (γpi ι)
  let f : ((ι → ℝ) × (ι → ℝ)) → ℝ := fun z => psi a z.1 * Q (ρ • z.1+s • z.2)
  have hqm : Measurable (fun z : (ι → ℝ) × (ι → ℝ) => Q (ρ • z.1+s • z.2)) :=
    hQ.comp (by fun_prop)
  have hfm : Measurable f := ((continuous_psi a).measurable.comp measurable_fst).mul hqm
  have hfi : Integrable f μ := ((psi_integrable a).comp_fst (γpi ι)).mul_bdd
    hqm.aestronglyMeasurable (ae_of_all _ fun x => by
      simpa only [Real.norm_eq_abs] using hb _)
  have hm := rotation_preserves (ι := ι) ρ s h
  have hfm' : Measurable (f ∘ rotation ρ s) := hfm.comp (by fun_prop)
  have hfi' : Integrable (f ∘ rotation ρ s) μ :=
    (hm.integrable_comp hfm.aestronglyMeasurable).mpr hfi
  have htrans (z : (ι → ℝ) × (ι → ℝ)) :
      f (rotation ρ s z) = Q z.1 * psi a (ρ • z.1+s • z.2) := by
    have hx := congrArg Prod.fst (rotation_involutive (ι := ι) ρ s h z)
    change ρ • (ρ • z.1+s • z.2)+s • (s • z.1-ρ • z.2) = z.1 at hx
    dsimp [f, rotation_apply]
    rw [hx, mul_comm]
  calc
    _ = ∫ z, f z ∂μ := by
      rw [integral_prod _ hfi]
      apply integral_congr_ae
      filter_upwards [] with x
      exact (integral_const_mul _ _).symm
    _ = ∫ z, f (rotation ρ s z) ∂μ := by
      simpa only [hm.map_eq] using
        (integral_map (μ := (γpi ι).prod (γpi ι)) hm.measurable.aemeasurable hfm.aestronglyMeasurable)
    _ = ∫ x, ∫ y, Q x * psi a (ρ • x+s • y) ∂γpi ι ∂γpi ι := by
      change (∫ z, (f ∘ rotation ρ s) z ∂(γpi ι).prod (γpi ι)) = _
      rw [integral_prod _ hfi']
      apply integral_congr_ae
      filter_upwards [] with x
      apply integral_congr_ae
      filter_upwards [] with y
      exact htrans (x,y)
    _ = _ := by
      simp only [integral_const_mul, show ∀ x y : ι → ℝ, ρ • x+s • y =
          fun i => ρ*x i+s*y i by intros; rfl, psi_noise ρ s h]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      ring

lemma he_rotation_moment (ρ s c : ℝ) (h : ρ^2+s^2=1) (n : ℕ) :
    (∫ g, (s*c-ρ*g) * he n (ρ*c+s*g) ∂γ) = s*ρ^n*he (n+1) c := by
  have hi := integrable_he_affine n (ρ*c) s
  have hig := integrable_mul_he_affine n (ρ*c) s
  rw [show (fun g => (s*c-ρ*g)*he n (ρ*c+s*g)) = fun g =>
      (s*c)*he n (ρ*c+s*g)-ρ*(g*he n (ρ*c+s*g)) by funext g; ring,
    integral_sub (hi.const_mul _) (hig.const_mul _), integral_const_mul,
    integral_const_mul, he_noise ρ s c h]
  cases n with
  | zero => simp [γ, integral_id_gaussianReal]
  | succ n =>
    rw [stein_he_affine, he_noise ρ s c h, he_recurrence]
    simp only [pow_succ]
    ring

lemma sqrt_factorial_succ (n : ℕ) :
    Real.sqrt ((n+1).factorial : ℝ) = Real.sqrt (n+1:ℝ)*Real.sqrt (n.factorial : ℝ) := by
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    Real.sqrt_mul (by positivity)]

lemma H_rotation_moment (ρ s c : ℝ) (h : ρ^2+s^2=1) (n : ℕ) :
    (∫ g, (s*c-ρ*g) * H n (ρ*c+s*g) ∂γ) =
      s*Real.sqrt (n+1:ℝ)*ρ^n*H (n+1) c := by
  simp only [H, ← mul_div_assoc, integral_div, he_rotation_moment ρ s c h]
  rw [sqrt_factorial_succ]
  have h1 : Real.sqrt (n+1:ℝ) ≠ 0 := by positivity
  have h2 := ne_of_gt (sqrt_factorial_pos n)
  field_simp

lemma psi_rotation_moment [DecidableEq ι] (ρ s : ℝ) (h : ρ^2+s^2=1)
    (a : ι → ℕ) (c : ι → ℝ) (i : ι) :
    (∫ g, (s*c i-ρ*g i) * psi a (ρ • c+s • g) ∂γpi ι) =
      s*Real.sqrt (a i+1:ℝ)*ρ^(∑ j,a j) * psi (Function.update a i (a i+1)) c := by
  have heq (g : ι → ℝ) : (s*c i-ρ*g i)*psi a (ρ • c+s • g) =
      ∏ j, (if j=i then s*c j-ρ*g j else 1)*H (a j) (ρ*c j+s*g j) := by
    rw [Finset.prod_mul_distrib]
    simp [psi, Finset.prod_ite_eq', Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [heq]
  rw [integral_fintype_prod_eq_prod (f := fun j (t : ℝ) =>
    (if j=i then s*c j-ρ*t else 1)*H (a j) (ρ*c j+s*t))]
  have hfactor (j : ι) :
      (∫ t, (if j=i then s*c j-ρ*t else 1)*H (a j) (ρ*c j+s*t) ∂γ) =
        (if j=i then s*Real.sqrt (a i+1:ℝ) else 1)*
          (ρ^(a j)*H ((Function.update a i (a i+1)) j) (c j)) := by
    by_cases hj : j=i
    · subst j
      simp only [ite_true, Function.update_self, H_rotation_moment ρ s _ h]
      ring
    · simp only [hj, ite_false, one_mul, Function.update_of_ne hj, H_noise ρ s _ h]
  simp only [hfactor, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  simp [Finset.prod_ite_eq', psi, mul_assoc]

def score (ρ s : ℝ) (Q : (ι → ℝ) → ℝ) (i : ι) (x : ι → ℝ) : ℝ :=
  ∫ g, g i * Q (ρ • x+s • g) ∂γpi ι

lemma measurable_score (ρ s : ℝ) {Q : (ι → ℝ) → ℝ} (hQ : Measurable Q) (i : ι) :
    Measurable (score ρ s Q i) := by
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.integral_prod_right
  exact (by fun_prop : Measurable (fun z : (ι → ℝ) × (ι → ℝ) =>
    z.2 i * Q (ρ • z.1+s • z.2))).stronglyMeasurable

lemma coordinate_integrable (i : ι) : Integrable (fun g : ι → ℝ => g i) (γpi ι) :=
  integrable_eval ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num))

lemma score_bound (ρ s : ℝ) {Q : (ι → ℝ) → ℝ} (hQ : Measurable Q)
    (hb : ∀ x, |Q x| ≤ 1) (i : ι) (x : ι → ℝ) :
    |score ρ s Q i x| ≤ ∫ g, |g i| ∂γpi ι := by
  have hi : Integrable (fun g : ι → ℝ => g i * Q (ρ • x+s • g)) (γpi ι) :=
    (coordinate_integrable i).mul_bdd (hQ.comp (by fun_prop)).aestronglyMeasurable
      (ae_of_all _ fun g => by simpa only [Real.norm_eq_abs] using hb _)
  calc
    _ ≤ ∫ g, |g i * Q (ρ • x+s • g)| ∂γpi ι := by
      simpa only [score, Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun g : ι → ℝ => g i * Q (ρ • x+s • g))
    _ ≤ _ := integral_mono_ae hi.abs (coordinate_integrable i).abs <|
      ae_of_all _ fun g => by
        change |g i * Q (ρ • x+s • g)| ≤ |g i|
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hb _)

lemma memLp_score (ρ s : ℝ) {Q : (ι → ℝ) → ℝ} (hQ : Measurable Q)
    (hb : ∀ x, |Q x| ≤ 1) (i : ι) : MemLp (score ρ s Q i) 2 (γpi ι) :=
  MemLp.of_bound (measurable_score ρ s hQ i).aestronglyMeasurable _
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using score_bound ρ s hQ hb i x)

lemma score_coefficient [DecidableEq ι] (ρ s : ℝ) (h : ρ^2+s^2=1)
    {Q : (ι → ℝ) → ℝ} (hQ : Measurable Q) (hb : ∀ x, |Q x| ≤ 1)
    (a : ι → ℕ) (i : ι) :
    (∫ x, psi a x * score ρ s Q i x ∂γpi ι) =
      s*Real.sqrt (a i+1:ℝ)*ρ^(∑ j, a j) *
        ∫ x, psi (Function.update a i (a i+1)) x * Q x ∂γpi ι := by
  let μ := (γpi ι).prod (γpi ι)
  let f : ((ι → ℝ) × (ι → ℝ)) → ℝ := fun z =>
    (psi a z.1 * z.2 i) * Q (ρ • z.1+s • z.2)
  have hqm : Measurable (fun z : (ι → ℝ) × (ι → ℝ) => Q (ρ • z.1+s • z.2)) :=
    hQ.comp (by fun_prop)
  have hfm : Measurable f := (((continuous_psi a).measurable.comp measurable_fst).mul
    (by fun_prop)).mul hqm
  have hfi : Integrable f μ := ((psi_integrable a).mul_prod (coordinate_integrable i)).mul_bdd
    hqm.aestronglyMeasurable (ae_of_all _ fun x => by
      simpa only [Real.norm_eq_abs] using hb _)
  have hm := rotation_preserves (ι := ι) ρ s h
  have hfi' : Integrable (f ∘ rotation ρ s) μ :=
    (hm.integrable_comp hfm.aestronglyMeasurable).mpr hfi
  have htrans (z : (ι → ℝ) × (ι → ℝ)) :
      f (rotation ρ s z) = Q z.1 * ((s*z.1 i-ρ*z.2 i)*psi a (ρ • z.1+s • z.2)) := by
    have hx := congrArg Prod.fst (rotation_involutive (ι := ι) ρ s h z)
    change ρ • (ρ • z.1+s • z.2)+s • (s • z.1-ρ • z.2) = z.1 at hx
    dsimp [f, rotation_apply]
    rw [hx]
    ring
  calc
    _ = ∫ z, f z ∂μ := by
      rw [integral_prod _ hfi]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [score, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      dsimp [f]
      ring
    _ = ∫ z, f (rotation ρ s z) ∂μ := by
      simpa only [hm.map_eq] using
        (integral_map (μ := (γpi ι).prod (γpi ι)) hm.measurable.aemeasurable hfm.aestronglyMeasurable)
    _ = ∫ x, ∫ y, Q x * ((s*x i-ρ*y i)*psi a (ρ • x+s • y)) ∂γpi ι ∂γpi ι := by
      change (∫ z, (f ∘ rotation ρ s) z ∂(γpi ι).prod (γpi ι)) = _
      rw [integral_prod _ hfi']
      apply integral_congr_ae
      filter_upwards [] with x
      apply integral_congr_ae
      filter_upwards [] with y
      exact htrans (x,y)
    _ = _ := by
      simp only [integral_const_mul, psi_rotation_moment ρ s h]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      ring

def coeff (f : (ι → ℝ) → ℝ) (a : ι → ℕ) : ℝ := ∫ x, psi a x * f x ∂γpi ι

def degree (a : ι → ℕ) : ℕ := ∑ i, a i

def bump [DecidableEq ι] (i : ι) (a : ι → ℕ) : ι → ℕ := Function.update a i (a i+1)

lemma degree_bump [DecidableEq ι] (i : ι) (a : ι → ℕ) :
    degree (bump i a) = degree a+1 := by
  have heq (j : ι) : bump i a j = a j + if j=i then 1 else 0 := by
    by_cases hj : j=i <;> simp [bump, hj, Function.update_of_ne]
  simp only [degree, heq, Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq']

omit [Fintype ι] in
lemma bump_injective [DecidableEq ι] (i : ι) : Function.Injective (bump i : (ι → ℕ) → _) := by
  intro a b h
  funext j
  by_cases hj : j=i
  · subst j
    have heq := congrFun h i
    simpa [bump] using heq
  · simpa [bump, Function.update_of_ne hj] using congrFun h j

end MinUncut.GaussianHermite
end

end OAI
