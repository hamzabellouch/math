import OAI.MathematicalPhysics.Elasticity.BoundarySymbols

namespace OAI

section
/-! Uniform multivariable Taylor estimates for anisotropically rescaled boundary
layers. The constants are proved for actual smooth compactly supported physical
coefficient extensions; no symbol/asymptotic identification is assumed. -/
noncomputable section
open Set
open scoped BigOperators
namespace ElasticityBoundaryTaylor
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def line (z : E) : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight z

@[simp] lemma line_apply (z : E) (t : ℝ) : line z t = t • z := rfl

lemma iteratedDeriv_line {f : E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (k : ℕ) (z : E) (t : ℝ) :
    iteratedDeriv k (fun t : ℝ => f (t • z)) t =
      iteratedFDeriv ℝ k f (t • z) (fun _ => z) := by
  rw [iteratedDeriv_eq_iteratedFDeriv]
  change iteratedFDeriv ℝ k (f ∘ line z) t (fun _ => 1) = _
  rw [(line z).iteratedFDeriv_comp_right hf t (mod_cast le_top),
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp only [line_apply, one_smul]

def radialTaylor (f : E → F) (n : ℕ) (z : E) : F :=
  ∑ k ∈ Finset.range (n+1), (k.factorial : ℝ)⁻¹ •
    iteratedFDeriv ℝ k f 0 (fun _ => z)

lemma radialTaylor_eq_line {f : E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (n : ℕ) (z : E) :
    radialTaylor f n z = taylorWithinEval (fun t : ℝ => f (t • z)) n (Icc 0 1) 0 1 := by
  rw [taylor_within_apply]
  apply Finset.sum_congr rfl
  intro k hk
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => f (t • z)) :=
    hf.comp (contDiff_id.smul contDiff_const)
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
    (hg.of_le (mod_cast le_top)).contDiffAt (by simp), iteratedDeriv_line hf]
  simp

lemma radialTaylor_remainder {f : E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (n : ℕ) {C : ℝ} (hC : ∀ x, ‖iteratedFDeriv ℝ (n+1) f x‖ ≤ C) (z : E) :
    ‖f z - radialTaylor f n z‖ ≤ C * ‖z‖^(n+1) / (n.factorial : ℝ) := by
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => f (t • z)) :=
    hf.comp (contDiff_id.smul contDiff_const)
  have hbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖iteratedDerivWithin (n+1) (fun t : ℝ => f (t • z)) (Icc 0 1) t‖ ≤
        C * ‖z‖^(n+1) := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
      (hg.of_le (mod_cast le_top)).contDiffAt ht, iteratedDeriv_line hf]
    exact (ContinuousMultilinearMap.le_opNorm _ _).trans (by
      simpa using mul_le_mul_of_nonneg_right (hC (t • z)) (pow_nonneg (norm_nonneg z) (n+1)))
  have h := taylor_mean_remainder_bound (f := fun t : ℝ => f (t • z))
    (a := 0) (b := 1) (n := n) (x := 1) (by norm_num)
    (hg.of_le (mod_cast le_top)).contDiffOn (by simp) hbound
  simpa only [radialTaylor_eq_line hf, one_smul, sub_zero, one_pow, mul_one] using h

lemma compact_iteratedFDeriv_bound {f : E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := ((hf.of_le (show (n : WithTop ℕ∞) ≤ (⊤ : ℕ∞) from by
    exact_mod_cast le_top)).continuous_iteratedFDeriv').bounded_above_of_compact_support
      (hc.iteratedFDeriv n)
  exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩

/-- Every smooth compactly supported coefficient has a global polynomially
weighted Taylor remainder estimate, at every finite order. -/
theorem compact_radialTaylor_remainder {f : E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z,
      ‖f z - radialTaylor f n z‖ ≤ C * ‖z‖^(n+1) := by
  obtain ⟨C, hC, hbound⟩ := compact_iteratedFDeriv_bound hf hc (n+1)
  refine ⟨C/(n.factorial : ℝ), div_nonneg hC (Nat.cast_nonneg _), fun z => ?_⟩
  simpa only [div_mul_eq_mul_div] using radialTaylor_remainder hf n hbound z

end ElasticityBoundaryTaylor

end
end
section
/-! Literal polynomial representations of the actual Frechet Taylor jets and
of their anisotropic parameter dependence. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryTaylorPolynomial
open MvPolynomial ElasticityBoundaryTaylor ElasticityBoundaryMVCalculus ElasticityBoundaryScaling
abbrev Y := Fin 3 → ℝ

/-- The diagonal of a real multilinear map, expanded in the fixed coordinates. -/
def diagonal {n : ℕ} (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => Y) ℂ) : MP :=
  ∑ j : Fin n → Fin 3, C (T (fun k => Pi.single (j k) 1)) * ∏ k, X (j k)

lemma value_diagonal {n : ℕ} (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => Y) ℂ)
    (y : Y) : value (diagonal T) y = T (fun _ => y) := by
  classical
  have hy : (fun _ : Fin n => y) = (fun _ : Fin n => ∑ i : Fin 3, y i • Pi.single i (1:ℝ)) := by
    funext k i
    simp [Pi.single_apply]
  rw [hy]
  change _ = T.toMultilinearMap (fun _ => ∑ i : Fin 3, y i • Pi.single i (1:ℝ))
  rw [T.toMultilinearMap.map_sum]
  simp only [diagonal, value, eval_sum, eval_mul, eval_C, eval_prod, eval_X]
  apply Finset.sum_congr rfl
  intro j _
  rw [T.toMultilinearMap.map_smul_univ]
  simp only [Complex.real_smul, Complex.ofReal_prod]
  change T (fun k => Pi.single (j k) 1) * _ = _ * T (fun k => Pi.single (j k) 1)
  exact mul_comm _ _

def taylor (f : Y → ℂ) (n : ℕ) : MP :=
  ∑ k ∈ Finset.range (n+1), ((k.factorial : ℂ)⁻¹) • diagonal (iteratedFDeriv ℝ k f 0)

lemma value_taylor (f : Y → ℂ) (n : ℕ) (y : Y) :
    value (taylor f n) y = radialTaylor f n y := by
  simp only [taylor, value, eval_sum, radialTaylor]
  apply Finset.sum_congr rfl
  intro k _
  change value (((k.factorial : ℂ)⁻¹) • diagonal (iteratedFDeriv ℝ k f 0)) y = _
  rw [value_smul, value_diagonal]
  simp [Complex.real_smul]

def weightOrder (i : Fin 3) : ℕ := if i=2 then 2 else 1

def parameterize : MP →ₐ[ℂ] Polynomial MP :=
  MvPolynomial.aeval (fun i => Polynomial.C (X i) * Polynomial.X^(weightOrder i))

lemma eval_parameterize (p : MP) (δ : ℝ) :
    (parameterize p).eval (C (δ:ℂ)) =
      MvPolynomial.aeval (fun i => C ((scaleFactor δ i : ℝ):ℂ)*X i) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [parameterize]
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, Polynomial.eval_mul, hp]
      congr 1
      simp only [parameterize, aeval_X, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      unfold weightOrder scaleFactor
      split_ifs <;> simp only [Complex.ofReal_pow, map_pow, pow_one] <;> ring

lemma value_parameterize (p : MP) (δ : ℝ) (y : Y) :
    value ((parameterize p).eval (C (δ:ℂ))) y = value p (scale δ y) := by
  rw [eval_parameterize]
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, value_add, hp, hq]
  | mul_X p i hp =>
      rw [map_mul, aeval_X, value_mul, hp, value_mul, value_C, value_X, value_mul, value_X]
      simp only [scale_apply, Complex.ofReal_mul]

lemma value_parameterized_taylor (f : Y → ℂ) (n : ℕ) (δ : ℝ) (y : Y) :
    value ((parameterize (taylor f n)).eval (C (δ:ℂ))) y =
      radialTaylor f n (scale δ y) := by rw [value_parameterize, value_taylor]

end ElasticityBoundaryTaylorPolynomial

end
end
section
/-! Corrected amplitudes for the literal Taylor tensor differential operator.
The operator coefficients are computed, rather than a formal sequence assumed. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryActualTower
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryTensorSeries ElasticityBoundaryMVTower ElasticityBoundaryTaylorPolynomial

lemma operator_monomial (a : Tensor) (b : Lower) (n : ℕ) (p : W) :
    operator a b (Polynomial.monomial n p)=
      Polynomial.X^n*operator a b (Polynomial.C p) := by
  have h : Polynomial.monomial n p = Polynomial.monomial n 1*Polynomial.C p := by
    rw [Polynomial.monomial_mul_C, one_mul]
  rw [h, operator_monomial_mul, Polynomial.monomial_one_right_eq_X_pow]

def amplitude (p : ℕ → W) (N : ℕ) : Polynomial W :=
  ∑ n ∈ Finset.range (N+1), Polynomial.monomial n (p n)

lemma coefficient_operator_amplitude (a : Tensor) (b : Lower) (p : ℕ → W)
    {N d : ℕ} (hd : d≤N) :
    (operator a b (amplitude p N)).coeff d =
      ∑ k ∈ Finset.range (d+1), coefficient a b k (p (d-k)) := by
  simp only [amplitude, map_sum, operator_monomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_X_pow_mul', ← coefficient_apply]
  have hsub : (∑ n ∈ Finset.range (N+1), if n≤d then coefficient a b (d-n) (p n) else 0) =
      ∑ n ∈ Finset.range (d+1), coefficient a b (d-n) (p n) := by
    rw [← Finset.sum_subset (Finset.range_mono (show d+1≤N+1 by omega))
      (f := fun n => if n≤d then coefficient a b (d-n) (p n) else 0)]
    · apply Finset.sum_congr rfl
      intro n hn
      rw [ite_eq_left (by simp only [Finset.mem_range] at hn; omega)]
    · intro n _ hn
      rw [ite_eq_right (by simp only [Finset.mem_range] at hn; omega)]
  rw [hsub, ← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_range] at hk
  congr 2
  omega

/-- A true finite polynomial family cancels the literal tensor operator to
any requested order. This is not an assumption about an unknown symbol. -/
theorem finite_tensor_amplitude (a : Tensor) (b : Lower) (l m : ℂ)
    (hm : m≠0) (he : l+2*m≠0) (hp : l+3*m≠0)
    (ha : ∀ i α j β, (a i α j β).coeff 0=C (ElasticityBoundaryLayerOperator.elasticityTensor l m i α j β))
    (p₀ : W) (h₀ : normal l m p₀=0) (N : ℕ) :
    ∃ (p : ℕ → W) (R : Polynomial W), p 0=p₀ ∧
      (∀ n, 0<n → boundary (p n)=0) ∧
      operator a b (amplitude p N)=Polynomial.X^(N+1)*R := by
  obtain ⟨p,hp0,hb,hc⟩ := triangular_amplitudes l m hm he hp (coefficient a b)
    (coefficient_zero a b l m ha) p₀ h₀
  have hd : Polynomial.X^(N+1) ∣ operator a b (amplitude p N) := by
    apply Polynomial.X_pow_dvd_iff.mpr
    intro d hd
    rw [coefficient_operator_amplitude a b p (by omega), hc]
  obtain ⟨R,hR⟩ := hd
  exact ⟨p,R,hp0,hb,hR⟩

lemma parameterize_coeff_zero (p : MP) :
    (parameterize p).coeff 0=C (value p 0) := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  induction p using MvPolynomial.induction_on with
  | C c => simp [parameterize]
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq, value_add]
  | mul_X p i hp =>
      have hw : weightOrder i≠0 := by unfold weightOrder; split_ifs <;> decide
      simp only [map_mul, Polynomial.eval_mul, parameterize, aeval_X,
        Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, zero_pow hw,
        mul_zero, value_mul, value_X, Pi.zero_apply, Complex.ofReal_zero, map_zero]

lemma taylor_coeff_zero {f : (Fin 3 → ℝ) → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) (N : ℕ) :
    (parameterize (taylor f N)).coeff 0=C (f 0) := by
  rw [parameterize_coeff_zero, value_taylor]
  obtain ⟨A,_,hA⟩ := ElasticityBoundaryTaylor.compact_radialTaylor_remainder hf hc N
  have hz : f 0-ElasticityBoundaryTaylor.radialTaylor f N 0=0 := by
    apply norm_eq_zero.mp
    exact le_antisymm (by simpa using hA 0) (norm_nonneg _)
  rw [(sub_eq_zero.mp hz).symm]

end ElasticityBoundaryActualTower

end
end
section
/-! Honest L2 bounds and exact change of variables for physical boundary layers. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryProfileBounds
open ElasticityBoundaryMVCalculus ElasticityBoundaryScaling ElasticityBoundaryWeights
  ElasticityBoundaryProfile
abbrev Y := Fin 3 → ℝ

def halfspace : Set Y := {y | 0<y 2}
lemma measurable_halfspace : MeasurableSet halfspace :=
  (isOpen_lt continuous_const (continuous_apply 2)).measurableSet

lemma one_add_pow_le {r : ℝ} (hr : 0≤r) (n : ℕ) : (1+r)^n ≤ 2^n*(1+r^n) := by
  by_cases h : r≤1
  · calc
      _ ≤ (2:ℝ)^n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ ≤ _ := by nlinarith [pow_nonneg hr n, pow_nonneg (show (0:ℝ)≤2 by norm_num) n]
  · have h1 : 1≤r := le_of_not_ge h
    calc
      _ ≤ (2*r)^n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ = (2:ℝ)^n*r^n := mul_pow _ _ _
      _ ≤ _ := by nlinarith [pow_nonneg (show (0:ℝ)≤2 by norm_num) n]

lemma polynomial_square_bound (p : MP) :
    ∃ C : ℝ, 0≤C ∧ ∃ n : ℕ, ∀ y : Y, ‖value p y‖^2 ≤ C*(1+‖y‖^n) := by
  obtain ⟨A,hA,n,h⟩ := polynomialGrowth p
  refine ⟨A^2*2^(2*n),by positivity,2*n,fun y => ?_⟩
  calc
    _ ≤ (A*(1+‖y‖)^n)^2 := pow_le_pow_left₀ (norm_nonneg _) (h y) 2
    _ = A^2*(1+‖y‖)^(2*n) := by rw [mul_pow, ← pow_mul]; ring
    _ ≤ A^2*(2^(2*n)*(1+‖y‖^(2*n))) :=
      mul_le_mul_of_nonneg_left (one_add_pow_le (norm_nonneg y) _) (sq_nonneg A)
    _ = _ := by ring

lemma integrable_polynomial_square_weight (p : MP) {b : ℝ} (hb : 0<b) :
    Integrable (fun y : Y => ‖value p y‖^2*weight b y) := by
  obtain ⟨C,hC,n,h⟩ := polynomial_square_bound p
  have hI := ((integrable_weight hb).add (integrable_norm_moment hb n)).const_mul C
  apply hI.mono' (((smooth_value p).continuous.norm.pow 2).measurable.mul
    (measurable_weight b)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun y => by
    change |‖value p y‖^2 * weight b y| ≤ C * (weight b y + ‖y‖^n * weight b y)
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (weight_nonneg b y))]
    convert mul_le_mul_of_nonneg_right (h y) (weight_nonneg b y) using 1
    ring)

lemma integrableOn_profile_square (δ : ℝ) (p : MP) :
    IntegrableOn (fun y => ‖profile δ p y‖^2) halfspace := by
  have h := integrable_polynomial_square_weight p (by norm_num : (0:ℝ)<2)
  rw [← integrable_indicator_iff measurable_halfspace]
  apply h.congr
  exact Filter.Eventually.of_forall (fun y => (profile_square_weight δ p y).symm)

lemma memLp_profile (δ : ℝ) (p : MP) : MemLp (profile δ p) 2 (volume.restrict halfspace) :=
  (memLp_two_iff_integrable_sq_norm (smooth_profile δ p).continuous.aestronglyMeasurable).mpr
    (integrableOn_profile_square δ p)

lemma integral_profile_square (δ : ℝ) (p : MP) :
    (∫ y in halfspace, ‖profile δ p y‖^2) = ∫ y : Y, ‖value p y‖^2*weight 2 y := by
  rw [← integral_indicator measurable_halfspace]
  exact integral_congr_ae (Filter.Eventually.of_forall (profile_square_weight δ p))

lemma scale_mem_halfspace {δ : ℝ} (hδ : δ≠0) (y : Y) : scale δ y ∈ halfspace ↔ y∈halfspace := by
  change 0<scale δ y 2 ↔ 0<y 2
  simp only [scale_apply, scaleFactor]
  exact mul_pos_iff_of_pos_left (sq_pos_of_ne_zero hδ)

lemma scale_indicator {F : Type*} [Zero F] {δ : ℝ} (hδ : δ≠0) (f : Y → F) (y : Y) :
    halfspace.indicator f (scale δ y)=halfspace.indicator (fun y => f (scale δ y)) y := by
  classical
  change (if scale δ y ∈ halfspace then _ else 0) = (if y∈halfspace then _ else 0)
  rw [scale_mem_halfspace hδ]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem integralOn_scale {δ : ℝ} (hδ : δ≠0) (f : Y → F) :
    (∫ y in halfspace, f y) = δ^4 • ∫ y in halfspace, f (scale δ y) := by
  rw [← integral_indicator measurable_halfspace, integral_scale hδ]
  simp_rw [scale_indicator hδ]
  rw [integral_indicator measurable_halfspace]

lemma integrableOn_scaled_iff {δ : ℝ} (hδ : δ≠0) (f : Y → F) :
    IntegrableOn (fun y => f (scale δ y)) halfspace ↔ IntegrableOn f halfspace := by
  rw [← integrable_indicator_iff measurable_halfspace, ← integrable_indicator_iff measurable_halfspace]
  simpa only [scale_indicator hδ] using (scaled_integrable_iff hδ (halfspace.indicator f))

lemma physicalProfile_scale {δ : ℝ} (hδ : δ≠0) (p : MP) (y : Y) :
    physicalProfile δ p (scale δ y)=profile δ p y := by
  simp only [physicalProfile, scale_comp, inv_mul_cancel₀ hδ, scale_one]

/-- Exact delta^4 factor in the true unscaled L2 mass. -/
theorem integral_physicalProfile_square {δ : ℝ} (hδ : δ≠0) (p : MP) :
    (∫ y in halfspace, ‖physicalProfile δ p y‖^2) =
      δ^4 * ∫ y : Y, ‖value p y‖^2*weight 2 y := by
  rw [integralOn_scale hδ]
  simp_rw [physicalProfile_scale hδ]
  rw [integral_profile_square]
  rfl

lemma memLp_physicalProfile {δ : ℝ} (hδ : δ≠0) (p : MP) :
    MemLp (physicalProfile δ p) 2 (volume.restrict halfspace) := by
  apply (memLp_two_iff_integrable_sq_norm
    (smooth_physicalProfile δ p).continuous.aestronglyMeasurable).mpr
  change IntegrableOn (fun x => ‖physicalProfile δ p x‖^2) halfspace
  rw [← integrableOn_scaled_iff hδ]
  simpa only [physicalProfile_scale hδ] using integrableOn_profile_square δ p

end ElasticityBoundaryProfileBounds

end
end
section
/-! Uniform true L2/H1 estimates for finite corrected boundary amplitudes. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryParameterBounds
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryProfile
  ElasticityBoundaryProfileBounds ElasticityBoundaryWeights ElasticityBoundaryParameter
abbrev Y := Fin 3 → ℝ

def atParameter (q : Polynomial MP) (δ : ℝ) : MP := q.eval (C (δ:ℂ))

lemma atParameter_add (q r : Polynomial MP) (δ : ℝ) :
    atParameter (q+r) δ=atParameter q δ+atParameter r δ := Polynomial.eval_add

lemma value_parameter_monomial (n : ℕ) (p : MP) (δ : ℝ) (y : Y) :
    value (atParameter (Polynomial.monomial n p) δ) y=value p y*(δ:ℂ)^n := by
  simp [atParameter,value]

lemma parameterGrowth (q : Polynomial MP) :
    ∃ A : ℝ, 0≤A ∧ ∃ n : ℕ, ∀ δ : ℝ, 0≤δ → δ≤1 → ∀ y : Y,
      ‖value (atParameter q δ) y‖ ≤ A*(1+‖y‖)^n := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
      obtain ⟨A,hA,a,ha⟩ := hp
      obtain ⟨B,hB,b,hb⟩ := hq
      refine ⟨A+B,add_nonneg hA hB,max a b,fun δ hδ hδ1 y => ?_⟩
      have hr : 1≤1+‖y‖ := by linarith [norm_nonneg y]
      calc
        _ ≤ ‖value (atParameter p δ) y‖+‖value (atParameter q δ) y‖ := by
          rw [atParameter_add,value_add]; exact norm_add_le _ _
        _ ≤ A*(1+‖y‖)^a+B*(1+‖y‖)^b := add_le_add (ha δ hδ hδ1 y) (hb δ hδ hδ1 y)
        _ ≤ A*(1+‖y‖)^(max a b)+B*(1+‖y‖)^(max a b) :=
          add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr (le_max_left _ _)) hA)
            (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr (le_max_right _ _)) hB)
        _ = _ := by ring
  | monomial k p =>
      obtain ⟨A,hA,a,ha⟩ := polynomialGrowth p
      refine ⟨A,hA,a,fun δ hδ hδ1 y => ?_⟩
      rw [value_parameter_monomial, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hδ]
      exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ hδ hδ1)).trans (ha y)

lemma parameter_square_bound (q : Polynomial MP) :
    ∃ C : ℝ, 0≤C ∧ ∃ n : ℕ, ∀ δ : ℝ, 0≤δ → δ≤1 → ∀ y : Y,
      ‖value (atParameter q δ) y‖^2 ≤ C*(1+‖y‖^n) := by
  obtain ⟨A,hA,n,ha⟩ := parameterGrowth q
  refine ⟨A^2*2^(2*n),by positivity,2*n,fun δ hδ hδ1 y => ?_⟩
  calc
    _ ≤ (A*(1+‖y‖)^n)^2 := pow_le_pow_left₀ (norm_nonneg _) (ha δ hδ hδ1 y) 2
    _ = A^2*(1+‖y‖)^(2*n) := by rw [mul_pow, ← pow_mul]; ring
    _ ≤ A^2*(2^(2*n)*(1+‖y‖^(2*n))) :=
      mul_le_mul_of_nonneg_left (one_add_pow_le (norm_nonneg y) _) (sq_nonneg A)
    _ = _ := by ring

lemma parameter_mass_bound (q : Polynomial MP) :
    ∃ C : ℝ, 0≤C ∧ ∀ δ : ℝ, 0≤δ → δ≤1 →
      (∫ y : Y, ‖value (atParameter q δ) y‖^2*weight 2 y) ≤ C := by
  obtain ⟨A,hA,n,ha⟩ := parameter_square_bound q
  let g : Y → ℝ := fun y => A*(weight 2 y+‖y‖^n*weight 2 y)
  have hi : Integrable g := ((integrable_weight (by norm_num : (0:ℝ)<2)).add
    (integrable_norm_moment (by norm_num : (0:ℝ)<2) n)).const_mul A
  refine ⟨∫ y, g y, integral_nonneg (fun y => ?_), fun δ hδ hδ1 => ?_⟩
  · exact mul_nonneg hA (add_nonneg (weight_nonneg _ _)
      (mul_nonneg (pow_nonneg (norm_nonneg _) _) (weight_nonneg _ _)))
  · apply integral_mono (integrable_polynomial_square_weight _ (by norm_num)) hi
    intro y
    have h := mul_le_mul_of_nonneg_right (ha δ hδ hδ1 y) (weight_nonneg 2 y)
    convert h using 1
    dsimp [g]; ring

/-- No inverse powers remain in the true L2 norm of a first physical partial:
the inverse delta^4 differential factor and delta^4 Jacobian cancel exactly. -/
lemma integral_physical_partial {δ : ℝ} (hδ : δ≠0) (p : MP) (j : Fin 3) :
    (∫ z in halfspace, ‖fderiv ℝ (physicalProfile δ p) z (Pi.single j 1)‖^2) =
      ∫ y : Y, ‖value (D δ j p) y‖^2*weight 2 y := by
  simp_rw [fderiv_physicalProfile_basis hδ, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_nonneg (sq_nonneg δ), mul_pow]
  rw [integral_const_mul, integral_physicalProfile_square hδ]
  have hs : ((δ^2)⁻¹)^2*δ^4=1 := by field_simp
  rw [← mul_assoc, hs, one_mul]

/-- The actual corrected physical profiles, for a fixed finite polynomial
family, have uniformly bounded first-partial L2 masses. -/
theorem uniform_physical_partial (q : Polynomial MP) (j : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ δ : ℝ, 0<δ → δ≤1 →
      (∫ z in halfspace, ‖fderiv ℝ (physicalProfile δ (atParameter q δ)) z
        (Pi.single j 1)‖^2) ≤ C := by
  obtain ⟨C,hC,h⟩ := parameter_mass_bound (PD j q)
  refine ⟨C,hC,fun δ hδ hδ1 => ?_⟩
  rw [integral_physical_partial hδ.ne']
  change (∫ y : Y, ‖value (D δ j (q.eval (MvPolynomial.C (δ:ℂ)))) y‖^2*weight 2 y) ≤ C
  rw [← eval_PD]
  exact h δ hδ.le hδ1

end ElasticityBoundaryParameterBounds

end
end
section
/-! Uniform polynomial-growth estimates for the actual smooth coefficient
Taylor errors, multiplied by a finite amplitude family. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryOrderBound
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryParameterBounds
  ElasticityBoundaryTaylorPolynomial ElasticityBoundaryTaylor ElasticityBoundaryScaling
  ElasticityBoundaryProfileBounds ElasticityBoundaryWeights
abbrev Y := Fin 3 → ℝ

/-- A quantitative bound, with constants independent of concentration and
of the half-space point. The polynomial spatial weight is integrable against
our Gaussian/normal exponential. -/
def OrderBound (f : ℝ → Y → ℂ) (k : ℕ) : Prop :=
  ∃ A : ℝ, 0≤A ∧ ∃ n : ℕ, ∀ δ : ℝ, 0<δ → δ≤1 → ∀ y : Y,
    ‖f δ y‖ ≤ A*δ^k*(1+‖y‖)^n

lemma OrderBound.zero (k : ℕ) : OrderBound (fun _ _ => 0) k := by
  exact ⟨0,le_rfl,0,fun _ _ _ _ => by simp⟩

lemma OrderBound.add {f g : ℝ → Y → ℂ} {k : ℕ}
    (hf : OrderBound f k) (hg : OrderBound g k) : OrderBound (fun δ y => f δ y+g δ y) k := by
  obtain ⟨A,hA,a,ha⟩ := hf
  obtain ⟨B,hB,b,hb⟩ := hg
  refine ⟨A+B,add_nonneg hA hB,max a b,fun δ hδ hδ1 y => ?_⟩
  have hr : 1≤1+‖y‖ := by linarith [norm_nonneg y]
  calc
    _ ≤ ‖f δ y‖+‖g δ y‖ := norm_add_le _ _
    _ ≤ A*δ^k*(1+‖y‖)^a+B*δ^k*(1+‖y‖)^b :=
      add_le_add (ha δ hδ hδ1 y) (hb δ hδ hδ1 y)
    _ ≤ A*δ^k*(1+‖y‖)^(max a b)+B*δ^k*(1+‖y‖)^(max a b) :=
      add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr (le_max_left _ _))
        (mul_nonneg hA (pow_nonneg hδ.le _)))
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr (le_max_right _ _))
        (mul_nonneg hB (pow_nonneg hδ.le _)))
    _ = _ := by ring

lemma OrderBound.sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → Y → ℂ) {k : ℕ}
    (h : ∀ i∈s, OrderBound (f i) k) : OrderBound (fun δ y => ∑ i∈s, f i δ y) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using OrderBound.zero k
  | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi] using (h i (Finset.mem_insert_self _ _)).add
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

lemma OrderBound.mul {f g : ℝ → Y → ℂ} {k l : ℕ}
    (hf : OrderBound f k) (hg : OrderBound g l) : OrderBound (fun δ y => f δ y*g δ y) (k+l) := by
  obtain ⟨A,hA,a,ha⟩ := hf
  obtain ⟨B,hB,b,hb⟩ := hg
  refine ⟨A*B,mul_nonneg hA hB,a+b,fun δ hδ hδ1 y => ?_⟩
  rw [norm_mul]
  calc
    _ ≤ (A*δ^k*(1+‖y‖)^a)*(B*δ^l*(1+‖y‖)^b) :=
      mul_le_mul (ha δ hδ hδ1 y) (hb δ hδ hδ1 y) (norm_nonneg _)
        (by positivity)
    _ = _ := by rw [pow_add, pow_add]; ring

lemma OrderBound.weaken {f : ℝ → Y → ℂ} {k l : ℕ} (hf : OrderBound f k) (hl : l≤k) :
    OrderBound f l := by
  obtain ⟨A,hA,n,h⟩ := hf
  refine ⟨A,hA,n,fun δ hδ hδ1 y => ?_⟩
  exact (h δ hδ hδ1 y).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hδ.le hδ1 hl) hA) (by positivity))

lemma parameter_bound (p : Polynomial MP) :
    OrderBound (fun δ y => value (atParameter p δ) y) 0 := by
  obtain ⟨A,hA,n,h⟩ := parameterGrowth p
  exact ⟨A,hA,n,fun δ hδ hδ1 y => by simpa using h δ hδ.le hδ1 y⟩

lemma power_bound (k : ℕ) : OrderBound (fun δ _ => (δ:ℂ)^k) k := by
  refine ⟨1,by norm_num,0,fun δ hδ _ _ => ?_⟩
  simp [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]

lemma parameter_factor_bound (p : Polynomial MP) (k : ℕ) :
    OrderBound (fun δ y => value (atParameter (Polynomial.X^k*p) δ) y) k := by
  have h := (power_bound k).mul (parameter_bound p)
  simpa [atParameter,value] using h

/-- The actual smooth coefficient minus its literal Taylor polynomial carries
the prescribed power of delta uniformly, not only at each fixed spatial point. -/
lemma taylor_error_bound {f : Y → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) (N : ℕ) :
    OrderBound (fun δ y => f (scale δ y)-
      value (atParameter (parameterize (taylor f N)) δ) y) (N+1) := by
  obtain ⟨A,hA,h⟩ := compact_radialTaylor_remainder hf hc N
  refine ⟨A,hA,N+1,fun δ hδ hδ1 y => ?_⟩
  change ‖f (scale δ y)-value ((parameterize (taylor f N)).eval (C (δ:ℂ))) y‖ ≤ _
  rw [value_parameterized_taylor]
  calc
    _ ≤ A*‖scale δ y‖^(N+1) := h _
    _ ≤ A*(δ*‖y‖)^(N+1) := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (scale_norm_le hδ.le hδ1 y) _) hA
    _ = A*δ^(N+1)*‖y‖^(N+1) := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg y)
      (by linarith : ‖y‖≤1+‖y‖) _) (by positivity)

/-- Every such explicit bound gives a genuine weighted L2 estimate. -/
theorem OrderBound.square_mass {f : ℝ → Y → ℂ} {k : ℕ} (hf : OrderBound f k)
    (hm : ∀ δ, Continuous (f δ)) {b : ℝ} (hb : 0<b) :
    ∃ C : ℝ, 0≤C ∧ ∀ δ : ℝ, 0<δ → δ≤1 →
      Integrable (fun y => ‖f δ y‖^2*weight b y) ∧
      (∫ y, ‖f δ y‖^2*weight b y) ≤ C*δ^(2*k) := by
  obtain ⟨A,hA,n,h⟩ := hf
  let g : Y → ℝ := fun y => A^2*2^(2*n)*(weight b y+‖y‖^(2*n)*weight b y)
  have hi : Integrable g := ((integrable_weight hb).add
    (integrable_norm_moment hb (2*n))).const_mul (A^2*2^(2*n))
  have hg (y : Y) : 0≤g y := by
    dsimp [g]
    exact mul_nonneg (by positivity) (add_nonneg (weight_nonneg _ _)
      (mul_nonneg (by positivity) (weight_nonneg _ _)))
  refine ⟨∫ y, g y, integral_nonneg hg,fun δ hδ hδ1 => ?_⟩
  have hp (y : Y) : ‖f δ y‖^2*weight b y ≤ δ^(2*k)*g y := by
    have hsq := pow_le_pow_left₀ (norm_nonneg _) (h δ hδ hδ1 y) 2
    have hpoly := one_add_pow_le (norm_nonneg y) (2*n)
    have hbase : ‖f δ y‖^2 ≤ (A^2*δ^(2*k))*(2^(2*n)*(1+‖y‖^(2*n))) := by
      calc
        _ ≤ (A*δ^k*(1+‖y‖)^n)^2 := hsq
        _ = (A^2*δ^(2*k))*(1+‖y‖)^(2*n) := by simp only [mul_pow, ← pow_mul]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hpoly (by positivity)
    calc
      _ ≤ ((A^2*δ^(2*k))*(2^(2*n)*(1+‖y‖^(2*n))))*weight b y :=
        mul_le_mul_of_nonneg_right hbase (weight_nonneg b y)
      _ = _ := by dsimp [g]; ring
  have hI : Integrable (fun y => ‖f δ y‖^2*weight b y) := by
    apply (hi.const_mul (δ^(2*k))).mono'
      (((hm δ).norm.pow 2).measurable.mul (measurable_weight b)).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun y => by
      change |‖f δ y‖^2*weight b y| ≤ δ^(2*k)*g y
      rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (weight_nonneg b y))]
      exact hp y)
  refine ⟨hI, ?_⟩
  have hbound := integral_mono hI (hi.const_mul (δ^(2*k))) hp
  rw [integral_const_mul, mul_comm] at hbound
  exact hbound

end ElasticityBoundaryOrderBound

end
end
section
/-! The genuine smooth variable-coefficient operator applied to constructed
finite boundary amplitudes. The remaining error is estimated, not discarded. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundarySmoothOperator
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryParameter ElasticityBoundaryParameterBounds ElasticityBoundaryTensorSeries
  ElasticityBoundaryActualTower ElasticityBoundaryTaylorPolynomial ElasticityBoundaryOrderBound
  ElasticityBoundaryScaling ElasticityBoundaryLayerOperator ElasticityBoundaryWeights
abbrev Y := Fin 3 → ℝ
abbrev SmoothTensor := Fin 3 → Fin 3 → Fin 3 → Fin 3 → Y → ℂ
abbrev SmoothLower := Fin 3 → Fin 3 → Fin 3 → Y → ℂ

def tensorTaylor (a : SmoothTensor) (N : ℕ) : Tensor :=
  fun i α j β => parameterize (taylor (a i α j β) N)
def lowerTaylor (b : SmoothLower) (N : ℕ) : Lower :=
  fun i j β => parameterize (taylor (b i j β) N)

/-- The scaled amplitude of the literal differential expression; the PD
operators are already identified with true scaled first/second derivatives. -/
def scaledOperator (a : SmoothTensor) (b : SmoothLower) (q : Polynomial W)
    (δ : ℝ) (i : Fin 3) (y : Y) : ℂ :=
  (∑ α, ∑ j, ∑ β, a i α j β (scale δ y) *
    value (atParameter (PD α (PD β (unpack j q))) δ) y) +
  (δ:ℂ)^2 * ∑ j, ∑ β, b i j β (scale δ y) *
    value (atParameter (PD β (unpack j q)) δ) y

lemma polynomial_operator_value (a : Tensor) (b : Lower) (q : Polynomial W)
    (δ : ℝ) (i : Fin 3) (y : Y) :
    value (atParameter (unpack i (operator a b q)) δ) y =
    (∑ α, ∑ j, ∑ β, value (atParameter (a i α j β) δ) y *
      value (atParameter (PD α (PD β (unpack j q))) δ) y) +
    (δ:ℂ)^2 * ∑ j, ∑ β, value (atParameter (b i j β) δ) y *
      value (atParameter (PD β (unpack j q)) δ) y := by
  rw [unpack_operator]
  simp [atParameter, value, Polynomial.eval_finsetSum]

def scaledError (a : SmoothTensor) (b : SmoothLower) (q : Polynomial W)
    (N : ℕ) (δ : ℝ) (i : Fin 3) (y : Y) : ℂ :=
  (∑ α, ∑ j, ∑ β, (a i α j β (scale δ y)-
    value (atParameter (tensorTaylor a N i α j β) δ) y) *
    value (atParameter (PD α (PD β (unpack j q))) δ) y) +
  (δ:ℂ)^2 * ∑ j, ∑ β, (b i j β (scale δ y)-
    value (atParameter (lowerTaylor b N i j β) δ) y) *
    value (atParameter (PD β (unpack j q)) δ) y

lemma scaledOperator_decomposition (a : SmoothTensor) (b : SmoothLower) (q : Polynomial W)
    (N : ℕ) (δ : ℝ) (i : Fin 3) (y : Y) :
    scaledOperator a b q δ i y =
      value (atParameter (unpack i (operator (tensorTaylor a N) (lowerTaylor b N) q)) δ) y +
      scaledError a b q N δ i y := by
  rw [polynomial_operator_value]
  simp only [scaledOperator, scaledError, sub_mul, Finset.sum_sub_distrib, mul_sub]
  ring

lemma error_order_bound (a : SmoothTensor) (b : SmoothLower)
    (ha : ∀ i α j β, ContDiff ℝ (⊤ : ℕ∞) (a i α j β) ∧ HasCompactSupport (a i α j β))
    (hb : ∀ i j β, ContDiff ℝ (⊤ : ℕ∞) (b i j β) ∧ HasCompactSupport (b i j β))
    (q : Polynomial W) (N : ℕ) (i : Fin 3) :
    OrderBound (fun δ y => scaledError a b q N δ i y) (N+1) := by
  have hA : OrderBound (fun δ y => ∑ α, ∑ j, ∑ β, (a i α j β (scale δ y)-
      value (atParameter (tensorTaylor a N i α j β) δ) y) *
      value (atParameter (PD α (PD β (unpack j q))) δ) y) (N+1) := by
    apply OrderBound.sum
    intro α _
    apply OrderBound.sum
    intro j _
    apply OrderBound.sum
    intro β _
    simpa only [Nat.add_zero, tensorTaylor] using
      (taylor_error_bound (ha i α j β).1 (ha i α j β).2 N).mul
        (parameter_bound (PD α (PD β (unpack j q))))
  have hB : OrderBound (fun δ y => ∑ j, ∑ β, (b i j β (scale δ y)-
      value (atParameter (lowerTaylor b N i j β) δ) y) *
      value (atParameter (PD β (unpack j q)) δ) y) (N+1) := by
    apply OrderBound.sum
    intro j _
    apply OrderBound.sum
    intro β _
    simpa only [Nat.add_zero, lowerTaylor] using
      (taylor_error_bound (hb i j β).1 (hb i j β).2 N).mul
        (parameter_bound (PD β (unpack j q)))
  exact hA.add (((power_bound 2).mul hB).weaken (by omega))

lemma unpack_X_pow_mul (i : Fin 3) (k : ℕ) (q : Polynomial W) :
    unpack i (Polynomial.X^k*q)=Polynomial.X^k*unpack i q := by
  simpa only [Polynomial.monomial_one_right_eq_X_pow] using unpack_monomial_mul i k q

lemma scaledOperator_order_bound (a : SmoothTensor) (b : SmoothLower)
    (ha : ∀ i α j β, ContDiff ℝ (⊤ : ℕ∞) (a i α j β) ∧ HasCompactSupport (a i α j β))
    (hb : ∀ i j β, ContDiff ℝ (⊤ : ℕ∞) (b i j β) ∧ HasCompactSupport (b i j β))
    (q R : Polynomial W) (N : ℕ)
    (hR : operator (tensorTaylor a N) (lowerTaylor b N) q=Polynomial.X^(N+1)*R)
    (i : Fin 3) : OrderBound (fun δ y => scaledOperator a b q δ i y) (N+1) := by
  simp_rw [scaledOperator_decomposition a b q N, hR, unpack_X_pow_mul]
  exact (parameter_factor_bound (unpack i R) (N+1)).add (error_order_bound a b ha hb q N i)

lemma continuous_scaledOperator (a : SmoothTensor) (b : SmoothLower)
    (ha : ∀ i α j β, Continuous (a i α j β)) (hb : ∀ i j β, Continuous (b i j β))
    (q : Polynomial W) (δ : ℝ) (i : Fin 3) : Continuous (scaledOperator a b q δ i) := by
  apply Continuous.add
  · apply continuous_finsetSum
    intro α _
    apply continuous_finsetSum
    intro j _
    apply continuous_finsetSum
    intro β _
    exact ((ha i α j β).comp (scale δ).continuous).mul (smooth_value _).continuous
  · apply continuous_const.mul
    apply continuous_finsetSum
    intro j _
    apply continuous_finsetSum
    intro β _
    exact ((hb i j β).comp (scale δ).continuous).mul (smooth_value _).continuous

/-- For every smooth compact coefficient tensor with the physical frozen
value, the constructed amplitudes have a genuine arbitrarily small scaled
residual in weighted L2. No near-constantness is required. -/
theorem finite_smooth_amplitude (a : SmoothTensor) (b : SmoothLower)
    (ha : ∀ i α j β, ContDiff ℝ (⊤ : ℕ∞) (a i α j β) ∧ HasCompactSupport (a i α j β))
    (hb : ∀ i j β, ContDiff ℝ (⊤ : ℕ∞) (b i j β) ∧ HasCompactSupport (b i j β))
    (l m : ℂ) (hm : m≠0) (he : l+2*m≠0) (hp : l+3*m≠0)
    (ha0 : ∀ i α j β, a i α j β 0=elasticityTensor l m i α j β)
    (p₀ : W) (h₀ : normal l m p₀=0) (N : ℕ) :
    ∃ p : ℕ → W, p 0=p₀ ∧ (∀ n, 0<n → boundary (p n)=0) ∧
      ∀ i : Fin 3, ∃ C : ℝ, 0≤C ∧ ∀ δ : ℝ, 0<δ → δ≤1 →
        Integrable (fun y => ‖scaledOperator a b (amplitude p N) δ i y‖^2*weight 2 y) ∧
        (∫ y, ‖scaledOperator a b (amplitude p N) δ i y‖^2*weight 2 y) ≤ C*δ^(2*(N+1)) := by
  have hta0 : ∀ i α j β, (tensorTaylor a N i α j β).coeff 0=C (elasticityTensor l m i α j β) := by
    intro i α j β
    rw [tensorTaylor, taylor_coeff_zero (ha i α j β).1 (ha i α j β).2, ha0]
  obtain ⟨p,R,hp0,hpb,hR⟩ := finite_tensor_amplitude (tensorTaylor a N) (lowerTaylor b N)
    l m hm he hp hta0 p₀ h₀ N
  refine ⟨p,hp0,hpb,fun i => ?_⟩
  exact (scaledOperator_order_bound a b ha hb (amplitude p N) R N hR i).square_mass
    (fun δ => continuous_scaledOperator a b (fun i α j β => (ha i α j β).1.continuous)
      (fun i j β => (hb i j β).1.continuous) _ δ i) (by norm_num)

end ElasticityBoundarySmoothOperator

end
end
section
/-! Literal unscaled differential residuals of the constructed boundary fields.
The estimates are in the actual half-space L2 norm, not a formal series norm. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryStrongLayer
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryParameter ElasticityBoundaryParameterBounds ElasticityBoundaryTensorSeries
  ElasticityBoundaryActualTower ElasticityBoundarySmoothOperator ElasticityBoundaryProfile
  ElasticityBoundaryProfileBounds ElasticityBoundaryScaling ElasticityBoundaryLayerOperator
  ElasticityBoundaryWeights
abbrev Y := Fin 3 → ℝ

def dpart (f : Y → ℂ) (j : Fin 3) (z : Y) : ℂ :=
  fderiv ℝ f z (Pi.single j 1)

def strong (a : SmoothTensor) (b : SmoothLower) (u : Fin 3 → Y → ℂ) (i : Fin 3) (z : Y) : ℂ :=
  (∑ α, ∑ j, ∑ β, a i α j β z * dpart (dpart (u j) β) α z) +
    ∑ j, ∑ β, b i j β z * dpart (u j) β z

def layer (q : Polynomial W) (δ : ℝ) (j : Fin 3) : Y → ℂ :=
  physicalProfile δ (atParameter (unpack j q) δ)

lemma D_atParameter (δ : ℝ) (j : Fin 3) (p : Polynomial MP) :
    D δ j (atParameter p δ)=atParameter (PD j p) δ := (eval_PD j p δ).symm

lemma partial_layer {δ : ℝ} (hδ : δ≠0) (q : Polynomial W) (j β : Fin 3) (z : Y) :
    dpart (layer q δ j) β z = ((δ^2)⁻¹:ℝ) •
      physicalProfile δ (atParameter (PD β (unpack j q)) δ) z := by
  rw [dpart, layer, fderiv_physicalProfile_basis hδ, D_atParameter]

lemma second_layer {δ : ℝ} (hδ : δ≠0) (q : Polynomial W) (j α β : Fin 3) (z : Y) :
    dpart (dpart (layer q δ j) β) α z = ((δ^4)⁻¹:ℝ) •
      physicalProfile δ (atParameter (PD α (PD β (unpack j q))) δ) z := by
  change fderiv ℝ (fun x => fderiv ℝ (physicalProfile δ (atParameter (unpack j q) δ)) x
    (Pi.single β 1)) z (Pi.single α 1)=_
  rw [second_physicalProfile hδ, D_atParameter, D_atParameter]

/-- The computed scaled operator is exactly the actual strong differential
residual, including all coefficient-gradient/lower terms. -/
theorem strong_layer_scale (a : SmoothTensor) (b : SmoothLower)
    {δ : ℝ} (hδ : δ≠0) (q : Polynomial W) (i : Fin 3) (y : Y) :
    strong a b (layer q δ) i (scale δ y) =
      ((δ^4)⁻¹:ℝ) • (envelope δ y*scaledOperator a b q δ i y) := by
  simp only [strong, second_layer hδ, partial_layer hδ, physicalProfile_scale hδ,
    profile, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow]
  have h24 : ((δ:ℂ)^2)⁻¹=((δ:ℂ)^4)⁻¹*(δ:ℂ)^2 := by
    have hd : (δ:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hδ
    field_simp
  rw [h24]
  have hA (c v : ℂ) : c*(((δ:ℂ)^4)⁻¹*(envelope δ y*v)) =
      (((δ:ℂ)^4)⁻¹*envelope δ y)*(c*v) := by ring
  have hB (c v : ℂ) : c*((((δ:ℂ)^4)⁻¹*(δ:ℂ)^2)*(envelope δ y*v)) =
      ((((δ:ℂ)^4)⁻¹*envelope δ y)*(δ:ℂ)^2)*(c*v) := by ring
  simp_rw [hA, hB, ← Finset.mul_sum]
  unfold scaledOperator
  ring

lemma envelope_product_indicator (δ : ℝ) (f : Y → ℂ) (y : Y) :
    halfspace.indicator (fun y => ‖envelope δ y*f y‖^2) y=‖f y‖^2*weight 2 y := by
  have h := profile_square_weight δ (C (f y)) y
  change halfspace.indicator (fun z => ‖profile δ (C (f y)) z‖^2) y= _ at h
  by_cases hy : y∈halfspace
  · simpa only [Set.indicator_of_mem hy, profile, value_C] using h
  · simpa only [Set.indicator_of_notMem hy, value_C] using h

lemma integral_envelope_product (δ : ℝ) (f : Y → ℂ) :
    (∫ y in halfspace, ‖envelope δ y*f y‖^2)=∫ y : Y, ‖f y‖^2*weight 2 y := by
  rw [← integral_indicator measurable_halfspace]
  exact integral_congr_ae (Filter.Eventually.of_forall (envelope_product_indicator δ f))

lemma integrable_envelope_product_iff (δ : ℝ) (f : Y → ℂ) :
    IntegrableOn (fun y => ‖envelope δ y*f y‖^2) halfspace ↔
      Integrable (fun y => ‖f y‖^2*weight 2 y) := by
  rw [← integrable_indicator_iff measurable_halfspace]
  have h : halfspace.indicator (fun y => ‖envelope δ y*f y‖^2) =
      (fun y => ‖f y‖^2*weight 2 y) := funext (envelope_product_indicator δ f)
  rw [h]

lemma strong_layer_mass (a : SmoothTensor) (b : SmoothLower)
    {δ : ℝ} (hδ : δ≠0) (q : Polynomial W) (i : Fin 3) :
    (∫ z in halfspace, ‖strong a b (layer q δ) i z‖^2) =
      (δ^4)⁻¹ * ∫ y : Y, ‖scaledOperator a b q δ i y‖^2*weight 2 y := by
  rw [integralOn_scale hδ]
  simp_rw [strong_layer_scale a b hδ, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (show 0≤δ^4 by positivity)]
  simp_rw [mul_pow]
  rw [integral_const_mul, integral_envelope_product]
  change δ^4*(((δ^4)⁻¹)^2*_)=_
  have hpow : δ^4*((δ^4)⁻¹)^2=(δ^4)⁻¹ := by field_simp
  rw [← mul_assoc, hpow]

lemma integrable_strong_layer_square (a : SmoothTensor) (b : SmoothLower)
    {δ : ℝ} (hδ : δ≠0) (q : Polynomial W) (i : Fin 3)
    (h : Integrable (fun y => ‖scaledOperator a b q δ i y‖^2*weight 2 y)) :
    IntegrableOn (fun z => ‖strong a b (layer q δ) i z‖^2) halfspace := by
  rw [← integrableOn_scaled_iff hδ]
  simp_rw [strong_layer_scale a b hδ, norm_smul, mul_pow]
  exact ((integrable_envelope_product_iff δ _).mpr h).const_mul _

lemma continuous_strong_layer (a : SmoothTensor) (b : SmoothLower)
    (ha : ∀ i α j β, Continuous (a i α j β)) (hb : ∀ i j β, Continuous (b i j β))
    {δ : ℝ} (hδ : δ≠0) (q : Polynomial W) (i : Fin 3) :
    Continuous (strong a b (layer q δ) i) := by
  have h : strong a b (layer q δ) i = fun z =>
      (∑ α, ∑ j, ∑ β, a i α j β z * (((δ^4)⁻¹:ℝ) •
        physicalProfile δ (atParameter (PD α (PD β (unpack j q))) δ) z)) +
      ∑ j, ∑ β, b i j β z * (((δ^2)⁻¹:ℝ) •
        physicalProfile δ (atParameter (PD β (unpack j q)) δ) z) := by
    funext z
    simp only [strong, second_layer hδ, partial_layer hδ]
  rw [h]
  apply Continuous.add
  · apply continuous_finsetSum
    intro α _
    apply continuous_finsetSum
    intro j _
    apply continuous_finsetSum
    intro β _
    exact (ha i α j β).mul ((smooth_physicalProfile δ _).continuous.const_smul ((δ^4)⁻¹:ℝ))
  · apply continuous_finsetSum
    intro j _
    apply continuous_finsetSum
    intro β _
    exact (hb i j β).mul ((smooth_physicalProfile δ _).continuous.const_smul ((δ^2)⁻¹:ℝ))

/-- Genuine arbitrary-order half-space strong residuals of finite smooth
boundary trial fields. The norm is the actual unscaled L2 norm. -/
theorem finite_strong_layer (a : SmoothTensor) (b : SmoothLower)
    (ha : ∀ i α j β, ContDiff ℝ (⊤ : ℕ∞) (a i α j β) ∧ HasCompactSupport (a i α j β))
    (hb : ∀ i j β, ContDiff ℝ (⊤ : ℕ∞) (b i j β) ∧ HasCompactSupport (b i j β))
    (l m : ℂ) (hm : m≠0) (he : l+2*m≠0) (hp : l+3*m≠0)
    (ha0 : ∀ i α j β, a i α j β 0=elasticityTensor l m i α j β)
    (p₀ : W) (h₀ : normal l m p₀=0) (N : ℕ) :
    ∃ p : ℕ → W, p 0=p₀ ∧ (∀ n, 0<n → boundary (p n)=0) ∧
      ∀ i : Fin 3, ∃ C : ℝ, 0≤C ∧ ∀ δ : ℝ, 0<δ → δ≤1 →
        MemLp (strong a b (layer (amplitude p (N+1)) δ) i) 2 (volume.restrict halfspace) ∧
        (∫ z in halfspace, ‖strong a b (layer (amplitude p (N+1)) δ) i z‖^2) ≤ C*δ^(2*N) := by
  obtain ⟨p,hp0,hpb,hpN⟩ := finite_smooth_amplitude a b ha hb l m hm he hp ha0 p₀ h₀ (N+1)
  refine ⟨p,hp0,hpb,fun i => ?_⟩
  obtain ⟨C,hC,hI⟩ := hpN i
  refine ⟨C,hC,fun δ hδ hδ1 => ?_⟩
  obtain ⟨hInt,hBound⟩ := hI δ hδ hδ1
  refine ⟨(memLp_two_iff_integrable_sq_norm
    (continuous_strong_layer a b (fun i α j β => (ha i α j β).1.continuous)
      (fun i j β => (hb i j β).1.continuous) hδ.ne' _ i).aestronglyMeasurable).mpr
        (integrable_strong_layer_square a b hδ.ne' _ i hInt), ?_⟩
  rw [strong_layer_mass a b hδ.ne']
  calc
    _ ≤ (δ^4)⁻¹*(C*δ^(2*(N+1+1))) :=
      mul_le_mul_of_nonneg_left hBound (by positivity)
    _ = C*δ^(2*N) := by
      rw [show 2*(N+1+1)=4+2*N by omega, pow_add]
      field_simp

end ElasticityBoundaryStrongLayer

end
end
section
/-! True pullback of a second-order physical system. The coefficient Hessian
term is retained, and no equivalence of augmented and physical DN data is used. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryPullback
open ElasticityBoundaryChainRule ElasticityBoundarySmoothOperator ElasticityBoundaryStrongLayer
abbrev I := Fin 3
abbrev Y := Fin 3 → ℝ
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
abbrev Tensor (E : Type*) := I → I → I → I → E → ℂ
abbrev Lower (E : Type*) := I → I → I → E → ℂ

def directional (e : I → E) (a : Tensor E) (b : Lower E) (u : I → E → ℂ) (i : I) (x : E) : ℂ :=
  (∑ k, ∑ j, ∑ l, a i k j l x*dd (dd (u j) (e l)) (e k) x)+
    ∑ j, ∑ l, b i j l x*dd (u j) (e l) x

def principalPull (e : I → E) (a : Tensor E) (ψ : E → Y) : Tensor E :=
  fun i α j β x => ∑ k, ∑ l, a i k j l x*(jac ψ (e k) α x:ℂ)*(jac ψ (e l) β x:ℂ)

def lowerPull (e : I → E) (a : Tensor E) (b : Lower E) (ψ : E → Y) : Lower E :=
  fun i j β x => (∑ k, ∑ l, a i k j l x*(hess ψ (e k) (e l) β x:ℂ))+
    ∑ l, b i j l x*(jac ψ (e l) β x:ℂ)

lemma shuffle3 {R : Type*} [AddCommMonoid R] (f : I → I → I → R) :
    (∑ i, ∑ j, ∑ k, f i j k)=∑ j, ∑ k, ∑ i, f i j k := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact Finset.sum_comm

lemma shuffle5 {R : Type*} [AddCommMonoid R] (f : I → I → I → I → I → R) :
    (∑ k, ∑ j, ∑ l, ∑ β, ∑ α, f k j l β α)=
      ∑ α, ∑ j, ∑ β, ∑ k, ∑ l, f k j l β α := by
  simp_rw [Finset.sum_comm (f := fun β α => f _ _ _ β α)]
  simp_rw [Finset.sum_comm (f := fun l α => ∑ β, f _ _ l β α)]
  simp_rw [Finset.sum_comm (f := fun j α => ∑ l, ∑ β, f _ j l β α)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [Finset.sum_comm (f := fun l β => f _ j l β α)]
  exact Finset.sum_comm

/-- The actual system under a smooth coordinate map, including all lower
terms from its Hessian. No coordinate Jacobian is silently discarded. -/
theorem directional_comp (e : I → E) (a : Tensor E) (b : Lower E)
    {ψ : E → Y} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (u : I → Y → ℂ)
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) (i : I) (x : E) :
    directional e a b (fun j z => u j (ψ z)) i x =
      (∑ α, ∑ j, ∑ β, principalPull e a ψ i α j β x*cp (cp (u j) β) α (ψ x))+
        ∑ j, ∑ β, lowerPull e a b ψ i j β x*cp (u j) β (ψ x) := by
  simp only [directional, dd_dd_comp (hu _) hψ,
    dd_comp ((hu _).differentiable (by simp)) (hψ.differentiable (by simp)),
    mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  have hp : (∑ k, ∑ j, ∑ l, ∑ β, ∑ α,
      a i k j l x*((jac ψ (e l) β x:ℂ)*(jac ψ (e k) α x:ℂ)*cp (cp (u j) β) α (ψ x))) =
      ∑ α, ∑ j, ∑ β, principalPull e a ψ i α j β x*cp (cp (u j) β) α (ψ x) := by
    rw [shuffle5]
    unfold principalPull
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro β _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [hp]
  unfold lowerPull
  simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  have hh : (∑ k, ∑ j, ∑ l, ∑ β,
      a i k j l x*((hess ψ (e k) (e l) β x:ℂ)*cp (u j) β (ψ x))) =
      ∑ j, ∑ β, ∑ k, ∑ l, a i k j l x*(hess ψ (e k) (e l) β x:ℂ)*cp (u j) β (ψ x) := by
    simp_rw [Finset.sum_comm (f := fun l β => a i _ _ l x*(_*cp (u _) β (ψ x)))]
    rw [shuffle3]
    simp only [mul_assoc]
  have hb : (∑ j, ∑ l, ∑ α, b i j l x*((jac ψ (e l) α x:ℂ)*cp (u j) α (ψ x)))=
      ∑ j, ∑ β, ∑ l, b i j l x*(jac ψ (e l) β x:ℂ)*cp (u j) β (ψ x) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
    simp only [mul_assoc]
  rw [hh,hb]
  abel

end ElasticityBoundaryPullback

end
end
section
/-! Orthogonal covariance of the literal isotropic tensor in physical
coordinates. The frame is an actual Euclidean isometry, not a gauge freedom. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryRotation
open ElasticityBoundaryLayerOperator
abbrev I := Fin 3
abbrev X := EuclideanSpace ℝ I

def frameMatrix (Q : X ≃ₗᵢ[ℝ] X) (i j : I) : ℂ := (Q (EuclideanSpace.single j 1) i : ℂ)

lemma frameMatrix_orthogonal (Q : X ≃ₗᵢ[ℝ] X) (j k : I) :
    (∑ i, frameMatrix Q i j*frameMatrix Q i k)=if j=k then 1 else 0 := by
  have hreal : (∑ i, Q (EuclideanSpace.single j 1) i*Q (EuclideanSpace.single k 1) i)=
      if j=k then 1 else 0 := by
    calc
      _ = inner ℝ (Q (EuclideanSpace.single k 1)) (Q (EuclideanSpace.single j 1)) := by
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        rfl
      _ = inner ℝ (EuclideanSpace.single k 1) (EuclideanSpace.single j 1) := Q.inner_map_map _ _
      _ = _ := by simp [EuclideanSpace.inner_single_left, PiLp.single_apply, eq_comm]
  simpa only [frameMatrix, ← Complex.ofReal_mul, ← Complex.ofReal_sum, apply_ite,
    Complex.ofReal_one, Complex.ofReal_zero] using congrArg Complex.ofReal hreal

def rotateTensor (Q : I → I → ℂ) (a : I → I → I → I → ℂ) (s α r β : I) : ℂ :=
  ∑ i, ∑ k, ∑ j, ∑ l, Q i s*Q k α*a i k j l*Q j r*Q l β

def columnDot (Q : I → I → ℂ) (i j : I) : ℂ := ∑ k, Q k i*Q k j

lemma rotate_isotropic_formula (Q : I → I → ℂ) (l m : ℂ) (s α r β : I) :
    rotateTensor Q (elasticityTensor l m) s α r β =
      l*columnDot Q s α*columnDot Q r β+
      m*(columnDot Q s r*columnDot Q α β+columnDot Q s β*columnDot Q α r) := by
  unfold rotateTensor elasticityTensor
  simp only [mul_add, add_mul, Finset.sum_add_distrib]
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
    Finset.sum_ite_irrel, Fintype.sum_ite_eq, Finset.sum_const_zero]
  unfold columnDot
  simp only [Finset.mul_sum, Finset.sum_mul]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · congr 1
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- Simultaneously transporting displacement and spatial coordinates by the
same actual orthogonal frame leaves the frozen physical tensor unchanged. -/
theorem rotate_isotropic (Q : X ≃ₗᵢ[ℝ] X) (l m : ℂ) (s α r β : I) :
    rotateTensor (frameMatrix Q) (elasticityTensor l m) s α r β=elasticityTensor l m s α r β := by
  rw [rotate_isotropic_formula]
  simp only [columnDot, frameMatrix_orthogonal, elasticityTensor]

end ElasticityBoundaryRotation

end
end
section
/-! Exact constant-frame transformation of the strong differential operator. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryFrameOperator
open ElasticityBoundaryChainRule ElasticityBoundaryPullback ElasticityBoundaryRotation
abbrev I := Fin 3
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def mix (Q : I → I → ℂ) (u : I → E → ℂ) (i : I) (x : E) : ℂ := ∑ j, Q i j*u j x

def mixedTensor (R S : I → I → ℂ) (a : Tensor E) : Tensor E :=
  fun s k r l x => ∑ i, ∑ j, R s i*a i k j l x*S j r

def mixedLower (R S : I → I → ℂ) (b : Lower E) : Lower E :=
  fun s r l x => ∑ i, ∑ j, R s i*b i j l x*S j r

lemma smooth_mix (Q : I → I → ℂ) (u : I → E → ℂ)
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) (i : I) :
    ContDiff ℝ (⊤ : ℕ∞) (mix Q u i) := by
  exact ContDiff.sum (fun j _ => contDiff_const.mul (hu j))

lemma dd_mix (Q : I → I → ℂ) (u : I → E → ℂ)
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) (i : I) (v x : E) :
    dd (mix Q u i) v x=∑ j, Q i j*dd (u j) v x := by
  change dd (fun z => ∑ j, Q i j*u j z) v x=_
  rw [dd_sum Finset.univ (fun j z => Q i j*u j z)
    (fun j _ => (contDiff_const.mul (hu j)).differentiable (by simp))]
  apply Finset.sum_congr rfl
  intro j _
  rw [dd_mul (differentiable_const _) ((hu j).differentiable (by simp))]
  have hz : dd (fun _ : E => Q i j) v x=0 := by simp [dd]
  rw [hz,zero_mul,zero_add]

lemma dd_dd_mix (Q : I → I → ℂ) (u : I → E → ℂ)
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) (i : I) (v w x : E) :
    dd (dd (mix Q u i) w) v x=∑ j, Q i j*dd (dd (u j) w) v x := by
  have he : dd (mix Q u i) w=mix Q (fun j => dd (u j) w) i := by
    funext z
    exact dd_mix Q u hu i w z
  rw [he]
  exact dd_mix Q _ (fun j => smooth_dd (hu j) w) i v x

lemma shuffle4 {R : Type*} [AddCommMonoid R] (f : I → I → I → I → R) :
    (∑ i, ∑ j, ∑ l, ∑ r, f i j l r)=∑ r, ∑ l, ∑ i, ∑ j, f i j l r := by
  simp_rw [Finset.sum_comm (f := fun l r => f _ _ l r)]
  simp_rw [Finset.sum_comm (f := fun j r => ∑ l, f _ j l r)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  simp_rw [Finset.sum_comm (f := fun j l => f _ j l r)]
  exact Finset.sum_comm

/-- Input displacement and output equation rotation retain every literal term. -/
theorem directional_mix (e : I → E) (R S : I → I → ℂ) (a : Tensor E) (b : Lower E)
    (u : I → E → ℂ) (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) (s : I) (x : E) :
    (∑ i, R s i*directional e a b (mix S u) i x)=
      directional e (mixedTensor R S a) (mixedLower R S b) u s x := by
  simp only [directional, dd_dd_mix S u hu, dd_mix S u hu,
    mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  unfold mixedTensor mixedLower
  simp only [Finset.sum_mul]
  congr 1
  · rw [shuffle5, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · rw [shuffle4]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

end ElasticityBoundaryFrameOperator

end
end
section
/-! The strong expression is the divergence of the actual isotropic stress,
with every Lamé-gradient term retained. It is not an independently prescribed
system. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryPhysicalStrong
open ElasticityBoundaryChainRule ElasticityBoundaryPullback ElasticityBoundaryLayerOperator
abbrev I := Fin 3
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def divergence (e : I → E) (u : I → E → ℂ) (x : E) : ℂ := ∑ j, dd (u j) (e j) x

def stress (e : I → E) (l m : E → ℂ) (u : I → E → ℂ) (i k : I) (x : E) : ℂ :=
  (if i=k then l x*divergence e u x else 0)+
    m x*(dd (u i) (e k) x+dd (u k) (e i) x)

def coeff (l m : E → ℂ) : Tensor E := fun i k j r x => elasticityTensor (l x) (m x) i k j r

def lower (e : I → E) (l m : E → ℂ) : Lower E := fun i j β x =>
  dd l (e i) x*(if j=β then 1 else 0)+dd m (e β) x*(if i=j then 1 else 0)+
    dd m (e j) x*(if i=β then 1 else 0)

lemma dd_add {f g : E → ℂ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (v x : E) :
    dd (fun z => f z+g z) v x=dd f v x+dd g v x := by
  rw [dd, fderiv_fun_add (hf x) (hg x), add_apply]
  rfl

lemma dd_ite (P : Prop) [Decidable P] (f g : E → ℂ) (v x : E) :
    dd (fun z => if P then f z else g z) v x=if P then dd f v x else dd g v x := by
  by_cases h : P <;> simp [h]

lemma smooth_divergence (e : I → E) (u : I → E → ℂ)
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) : ContDiff ℝ (⊤ : ℕ∞) (divergence e u) := by
  exact ContDiff.sum (fun j _ => smooth_dd (hu j) _)

lemma stress_derivative (e : I → E) {l m : E → ℂ}
    (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (u : I → E → ℂ) (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) (i k : I) (x : E) :
    dd (stress e l m u i k) (e k) x =
      (if i=k then dd l (e k) x*divergence e u x+l x*(∑ j, dd (dd (u j) (e j)) (e k) x) else 0)+
      dd m (e k) x*(dd (u i) (e k) x+dd (u k) (e i) x)+
      m x*(dd (dd (u i) (e k)) (e k) x+dd (dd (u k) (e i)) (e k) x) := by
  have hd := smooth_divergence e u hu
  have hsum (v : E) : dd (divergence e u) v x=∑ j, dd (dd (u j) (e j)) v x := by
    exact dd_sum Finset.univ (fun j => dd (u j) (e j))
      (fun j _ => (smooth_dd (hu j) _).differentiable (by simp)) v x
  have h0 : Differentiable ℝ (fun z => if i=k then l z*divergence e u z else 0) := by
    by_cases h : i=k
    · simpa [h] using (hl.mul hd).differentiable (by simp)
    · simp only [h,ite_false]
      exact differentiable_const 0
  change dd (fun z => (if i=k then l z*divergence e u z else 0)+
    m z*(dd (u i) (e k) z+dd (u k) (e i) z)) (e k) x=_
  rw [dd_add h0 ((hm.mul ((smooth_dd (hu i) _).add (smooth_dd (hu k) _))).differentiable (by simp)),
    dd_ite, dd_mul (hl.differentiable (by simp)) (hd.differentiable (by simp)), hsum,
    dd_mul (hm.differentiable (by simp))
      (((smooth_dd (hu i) _).add (smooth_dd (hu k) _)).differentiable (by simp)),
    dd_add ((smooth_dd (hu i) _).differentiable (by simp)) ((smooth_dd (hu k) _).differentiable (by simp))]
  have hz : dd (fun _ : E => (0 : ℂ)) (e k) x=0 := by simp [dd]
  rw [hz]
  ring

lemma tensor_contract (l m : ℂ) (d : I → I → I → ℂ) (i : I) :
    (∑ k, ∑ j, ∑ β, elasticityTensor l m i k j β*d j k β)=
      l*(∑ j, d j i j)+m*(∑ k, d i k k)+m*(∑ k, d k k i) := by
  simp only [elasticityTensor, add_mul, mul_add, Finset.sum_add_distrib]
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
    Finset.sum_ite_irrel, Fintype.sum_ite_eq, Finset.sum_const_zero]
  simp only [← Finset.mul_sum]
  ring

lemma lower_contract (dl dm : I → ℂ) (d : I → I → ℂ) (i : I) :
    (∑ j, ∑ β, (dl i*(if j=β then 1 else 0)+dm β*(if i=j then 1 else 0)+
      dm j*(if i=β then 1 else 0))*d j β)=
      dl i*(∑ j, d j j)+(∑ k, dm k*d i k)+∑ k, dm k*d k i := by
  simp only [add_mul, Finset.sum_add_distrib, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
    Finset.sum_ite_irrel, Fintype.sum_ite_eq, Finset.sum_const_zero]
  rw [← Finset.mul_sum]

/-- Divergence of the physical Lamé stress equals the constructed literal
second-order system, including its exact first-order coefficient terms. -/
theorem stress_divergence (e : I → E) {l m : E → ℂ}
    (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (u : I → E → ℂ) (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) (i : I) (x : E) :
    (∑ k, dd (stress e l m u i k) (e k) x)=directional e (coeff l m) (lower e l m) u i x := by
  simp only [stress_derivative e hl hm u hu, Finset.sum_add_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, mul_add, ← Finset.mul_sum]
  change _ = (∑ k, ∑ j, ∑ β, elasticityTensor (l x) (m x) i k j β*dd (dd (u j) (e β)) (e k) x)+
    ∑ j, ∑ β, (dd l (e i) x*(if j=β then 1 else 0)+dd m (e β) x*(if i=j then 1 else 0)+
      dd m (e j) x*(if i=β then 1 else 0))*dd (u j) (e β) x
  rw [tensor_contract]
  rw [lower_contract (fun k => dd l (e k) x) (fun k => dd m (e k) x) (fun j β => dd (u j) (e β) x) i]
  simp only [divergence]
  ring

end ElasticityBoundaryPhysicalStrong

end
end

end OAI
