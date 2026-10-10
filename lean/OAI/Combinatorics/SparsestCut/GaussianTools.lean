import OAI.Combinatorics.SparsestCut.Model

namespace OAI

universe u1 u2

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.GaussianTools

section Concentration
variable {Ω : Type u1} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma subgaussian_abs_tail {X : Ω → ℝ} {c : ℝ≥0}
    (hX : HasSubgaussianMGF X c μ) {u : ℝ} (hu : 0 ≤ u) :
    μ.real {sample | u < |X sample|} ≤ 2 * Real.exp (-u^2 / (2 * c)) := by
  have hsub : {sample | u < |X sample|} ⊆ {sample | u ≤ X sample} ∪ {sample | u ≤ -X sample} := by
    intro sample hω
    change u < |X sample| at hω
    rcases lt_abs.mp hω with h | h
    · exact Or.inl h.le
    · exact Or.inr h.le
  calc
    _ ≤ μ.real ({sample | u ≤ X sample} ∪ {sample | u ≤ -X sample}) := measureReal_mono hsub
    _ ≤ μ.real {sample | u ≤ X sample} + μ.real {sample | u ≤ -X sample} := measureReal_union_le _ _
    _ ≤ Real.exp (-u^2 / (2 * c)) + Real.exp (-u^2 / (2 * c)) :=
      add_le_add (hX.measure_ge_le hu) (hX.neg.measure_ge_le hu)
    _ = _ := by ring

theorem bounded_concentration {n : ℕ} (hn : 0 < n) (X : Fin n → Ω → ℝ)
    (hmeas : ∀ i, AEMeasurable (X i) μ) (hind : iIndepFun X μ)
    {B : ℝ} (hB : 0 < B) (hbound : ∀ i, ∀ᵐ sample ∂μ, |X i sample| ≤ B)
    {u : ℝ} (hu : 0 ≤ u) :
    μ.real {sample | u < |(∑ i, (X i sample - ∫ z, X i z ∂μ)) / (n : ℝ)|} ≤
      2 * Real.exp (-(n : ℝ) * u^2 / (2 * B^2)) := by
  classical
  let Y : Fin n → Ω → ℝ := fun i sample => X i sample - ∫ z, X i z ∂μ
  have hY (i : Fin n) : HasSubgaussianMGF (Y i) ⟨B^2, sq_nonneg B⟩ μ := by
    have hh := hasSubgaussianMGF_of_mem_Icc (hmeas i)
      (show ∀ᵐ sample ∂μ, X i sample ∈ Icc (-B) B by
        filter_upwards [hbound i] with sample hω using abs_le.mp hω)
    have hc : ((‖B - -B‖₊ / 2) ^ 2) = (⟨B^2, sq_nonneg B⟩ : ℝ≥0) := by
      ext
      change (‖B - -B‖ / 2) ^ 2 = B ^ 2
      rw [Real.norm_eq_abs]
      rw [abs_of_nonneg (by linarith : 0 ≤ B - -B)]
      ring
    exact (congrArg (fun variance : ℝ≥0 => HasSubgaussianMGF (Y i) variance μ) hc).mp hh
  have hYi : iIndepFun Y μ := hind.comp (fun i z => z - ∫ z, X i z ∂μ) (fun i => by fun_prop)
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun hYi
    (s := Finset.univ) (fun i hi => hY i)
  have havg := hsum.const_mul ((n : ℝ)⁻¹)
  have htail := subgaussian_abs_tail havg hu
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  convert htail using 1
  · congr 1; ext sample
    simp only [Y, div_eq_mul_inv, mul_comm]
  · congr 2
    have hc : ((⟨(n : ℝ)⁻¹ ^ 2, sq_nonneg _⟩ : ℝ≥0) *
        ∑ _ : Fin n, (⟨B^2, sq_nonneg _⟩ : ℝ≥0) : ℝ≥0) =
        (⟨B^2 / n, div_nonneg (sq_nonneg _) (by positivity)⟩ : ℝ≥0) := by
      apply NNReal.eq
      change (n : ℝ)⁻¹ ^ 2 * ↑(∑ _ : Fin n, (⟨B^2, sq_nonneg _⟩ : ℝ≥0)) = B^2 / n
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      change (n : ℝ)⁻¹ ^ 2 * ↑(n • (⟨B^2, sq_nonneg _⟩ : ℝ≥0)) = B^2 / n
      simp only [nsmul_eq_mul]
      change (n : ℝ)⁻¹ ^ 2 * ((n : ℝ) * B^2) = B^2 / n
      field_simp

    change -(n : ℝ) * u^2 / (2 * B^2) =
      -u^2 / (2 * (((⟨(n : ℝ)⁻¹ ^ 2, sq_nonneg _⟩ : ℝ≥0) *
        ∑ _ : Fin n, (⟨B^2, sq_nonneg _⟩ : ℝ≥0) : ℝ≥0) : ℝ))
    rw [hc]
    change -(n : ℝ) * u^2 / (2 * B^2) = -u^2 / (2 * (B^2 / n))
    field_simp

end Concentration

section Fourier
variable {E : Type u2} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma gaussian_cos_integrable (w : E) :
    Integrable (fun g : E => Real.cos (inner ℝ g w)) (stdGaussian E) := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
  · exact (by fun_prop : Continuous (fun g : E => Real.cos (inner ℝ g w))).aestronglyMeasurable
  · exact ae_of_all _ (fun g => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one _)

lemma gaussian_cos (w : E) :
    (∫ g : E, Real.cos (inner ℝ g w) ∂stdGaussian E) =
      Real.exp (-‖w‖^2 / 2) := by
  have hh := congrArg Complex.re (charFun_stdGaussian w)
  rw [charFun_apply] at hh
  have hf : Integrable (fun g : E => Complex.exp ((inner ℝ g w : ℂ) * Complex.I))
      (stdGaussian E) := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
    · exact (by fun_prop : Continuous (fun g : E => Complex.exp ((inner ℝ g w : ℂ) * Complex.I))).aestronglyMeasurable
    · exact ae_of_all _ (fun g => by simp)
  have hi := Complex.reCLM.integral_comp_comm hf
  change (∫ g : E, (Complex.exp ((inner ℝ g w : ℂ) * Complex.I)).re ∂stdGaussian E) =
    (∫ g : E, Complex.exp ((inner ℝ g w : ℂ) * Complex.I) ∂stdGaussian E).re at hi
  rw [← hi] at hh
  simpa [Complex.exp_re, pow_two, Complex.mul_re, Complex.mul_im] using hh

lemma gaussian_linear_sin_integrable (w v : E) :
    Integrable (fun g : E => inner ℝ g v * Real.sin (inner ℝ g w)) (stdGaussian E) := by
  apply Integrable.mono' ((IsGaussian.integrable_id (μ := stdGaussian E)).norm.mul_const ‖v‖)
  · exact (by fun_prop : Continuous (fun g : E => inner ℝ g v * Real.sin (inner ℝ g w))).aestronglyMeasurable
  · filter_upwards [] with g
    simp only [Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ |inner ℝ g v| * 1 := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)
      _ ≤ ‖g‖ * ‖v‖ := by simpa using abs_real_inner_le_norm g v

lemma gaussian_linear_sin (w v : E) :
    (∫ g : E, inner ℝ g v * Real.sin (inner ℝ g w) ∂stdGaussian E) =
      inner ℝ w v * Real.exp (-‖w‖^2 / 2) := by
  let F : ℝ → E → ℝ := fun t g => Real.cos (inner ℝ g (w + t • v))
  let F' : ℝ → E → ℝ := fun t g => -Real.sin (inner ℝ g (w + t • v)) * inner ℝ g v
  have hd (g : E) (t : ℝ) : HasDerivAt (fun t => F t g) (F' t g) t := by
    have h := ((hasDerivAt_const t w).add ((hasDerivAt_id t).smul_const v))
    have hh := ((hasDerivAt_const t g).inner ℝ h).cos
    simpa [F, F'] using hh
  have hbound (g : E) (t : ℝ) : ‖F' t g‖ ≤ ‖g‖ * ‖v‖ := by
    simp only [F', Real.norm_eq_abs, abs_mul, abs_neg]
    calc
      _ ≤ 1 * |inner ℝ g v| := mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)
      _ ≤ ‖g‖ * ‖v‖ := by simpa using abs_real_inner_le_norm g v
  have hi := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := stdGaussian E) (F := F) (F' := F') (bound := fun g => ‖g‖ * ‖v‖)
    (s := Set.univ) (x₀ := (0 : ℝ)) (Filter.univ_mem)
    (Filter.Eventually.of_forall (fun t =>
      (show Continuous (F t) by dsimp [F]; fun_prop).aestronglyMeasurable))
    (by simpa [F] using gaussian_cos_integrable w)
    (show AEStronglyMeasurable (F' 0) (stdGaussian E) from
      (show Continuous (F' 0) by dsimp [F']; fun_prop).aestronglyMeasurable)
    (ae_of_all _ (fun g t _ => hbound g t))
    ((IsGaussian.integrable_id (μ := stdGaussian E)).norm.mul_const ‖v‖)
    (ae_of_all _ (fun g t _ => hd g t))
  have ht := (((hasDerivAt_const (0 : ℝ) w).add
    ((hasDerivAt_id (0 : ℝ)).smul_const v)).norm_sq.neg.div_const 2).exp
  have heq : (fun t => ∫ g : E, F t g ∂stdGaussian E) =
      (fun t : ℝ => Real.exp (-‖w + t • v‖^2 / 2)) := by
    funext t
    exact gaussian_cos _
  rw [heq] at hi
  have huniq := hi.2.unique ht
  simp only [F', zero_smul, add_zero, one_smul, zero_add] at huniq
  have hneg : (∫ g : E, -Real.sin (inner ℝ g w) * inner ℝ g v ∂stdGaussian E) =
      -(∫ g : E, inner ℝ g v * Real.sin (inner ℝ g w) ∂stdGaussian E) := by
    rw [← integral_neg]
    congr 1
    funext g
    ring
  rw [hneg] at huniq
  dsimp at huniq
  simp only [zero_smul, add_zero] at huniq
  nlinarith

lemma gaussian_vector_sin_integrable (w : E) :
    Integrable (fun g : E => Real.sin (inner ℝ g w) • g) (stdGaussian E) := by
  exact (IsGaussian.integrable_id (μ := stdGaussian E)).bdd_smul 1
    (by fun_prop) (ae_of_all _ (fun g => by simpa using Real.abs_sin_le_one (inner ℝ g w)))

lemma gaussian_vector_sin (w : E) :
    (∫ g : E, Real.sin (inner ℝ g w) • g ∂stdGaussian E) =
      Real.exp (-‖w‖^2 / 2) • w := by
  apply ext_inner_left ℝ
  intro v
  rw [← integral_inner (gaussian_vector_sin_integrable w), inner_smul_right]
  simp only [inner_smul_right]
  simpa only [real_inner_comm, mul_comm] using gaussian_linear_sin w v

lemma gaussian_inner_law (v : E) :
    (stdGaussian E).map (fun g => inner ℝ v g) =
      gaussianReal 0 (⟨‖v‖^2, sq_nonneg _⟩ : ℝ≥0) := by
  have h := IsGaussian.map_eq_gaussianReal (μ := stdGaussian E) (innerSL ℝ v)
  simp only [integral_strongDual_stdGaussian, variance_dual_stdGaussian,
    innerSL_apply_norm] at h
  have hvariance : (‖v‖^2).toNNReal = (⟨‖v‖^2, sq_nonneg _⟩ : ℝ≥0) :=
    Real.toNNReal_of_nonneg (sq_nonneg _)
  exact h.trans (congrArg (gaussianReal 0) hvariance)

lemma gaussian_inner_sq (v : E) :
    (∫ g : E, (inner ℝ v g)^2 ∂stdGaussian E) = ‖v‖^2 := by
  have h := variance_dual_stdGaussian (innerSL ℝ v)
  rw [variance_eq_integral (by fun_prop), integral_strongDual_stdGaussian] at h
  simpa only [sub_zero, innerSL_apply_norm, innerSL_apply_apply] using h

lemma gaussian_inner_subgaussian (v : E) :
    HasSubgaussianMGF (fun g => inner ℝ v g) (⟨‖v‖^2, sq_nonneg _⟩ : ℝ≥0) (stdGaussian E) where
  integrable_exp_mul t := by
    have h := integrable_exp_mul_gaussianReal (μ := 0)
      (v := (⟨‖v‖^2, sq_nonneg _⟩ : ℝ≥0)) t
    rw [← gaussian_inner_law v] at h
    exact (integrable_map_measure h.aestronglyMeasurable (by fun_prop)).mp h
  mgf_le t := by
    rw [mgf_gaussianReal ⟨by fun_prop, gaussian_inner_law v⟩]
    simp

lemma gaussian_inner_tail (v : E) (hv : ‖v‖ = 1) {u : ℝ} (hu : 0 ≤ u) :
    (stdGaussian E).real {g | u < |inner ℝ v g|} ≤ 2 * Real.exp (-u^2 / 2) := by
  have h := subgaussian_abs_tail (gaussian_inner_subgaussian v) hu
  change _ ≤ 2 * Real.exp (-u^2 / (2 * ‖v‖^2)) at h
  simpa [hv] using h

end Fourier
section NormTails

lemma gaussian_real_exp_sq (t : ℝ) (ht : t < 1/2) :
    (∫ x : ℝ, Real.exp (t * x^2) ∂gaussianReal 0 1) =
      Real.exp (-(1/2 : ℝ) * Real.log (1 - 2*t)) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  have heq (x : ℝ) : gaussianPDFReal 0 1 x * Real.exp (t * x^2) =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1/2-t) * x^2) := by
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simp_rw [smul_eq_mul, heq]
  rw [integral_const_mul, integral_gaussian]
  have hpos : 0 < 1 - 2*t := by linarith
  have hhalf : 0 < 1/2-t := by linarith
  have hpi := Real.pi_pos
  have heq2 : (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (Real.pi / (1/2-t)) =
      Real.sqrt ((1 - 2*t)⁻¹) := by
    rw [← Real.sqrt_inv, ← Real.sqrt_mul (inv_nonneg.mpr (by positivity))]
    congr 1
    field_simp

  rw [heq2, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (inv_pos.mpr hpos), Real.log_inv]
  congr 1
  ring

lemma gaussian_real_exp_sq_integrable (t : ℝ) (ht : t < 1/2) :
    Integrable (fun x : ℝ => Real.exp (t * x^2)) (gaussianReal 0 1) := by
  by_contra h
  have hh := gaussian_real_exp_sq t ht
  rw [integral_undef h] at hh
  exact (Real.exp_ne_zero _).symm hh

lemma gaussian_exp_norm_sq {n : ℕ} (t : ℝ) (ht : t < 1/2) :
    (∫ g : EuclideanSpace ℝ (Fin n), Real.exp (t * ‖g‖^2)
      ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
      Real.exp (-(n : ℝ)/2 * Real.log (1-2*t)) := by
  rw [← map_pi_eq_stdGaussian]
  rw [integral_map (by fun_prop) (by fun_prop)]
  have heq (g : Fin n → ℝ) : Real.exp (t * ‖WithLp.toLp 2 g‖^2) =
      ∏ i, Real.exp (t * (g i)^2) := by
    rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum, Real.exp_sum]
  simp_rw [heq]
  have hp := integral_fintype_prod_eq_pow (ι := Fin n) (μ := gaussianReal 0 1)
    (fun x : ℝ => Real.exp (t * x^2))
  rw [Fintype.card_fin] at hp
  change (∫ x : Fin n → ℝ, ∏ i, Real.exp (t * x i ^ 2) ∂Measure.pi (fun _ => gaussianReal 0 1)) =
    (∫ x : ℝ, Real.exp (t * x^2) ∂gaussianReal 0 1) ^ n at hp
  rw [hp, gaussian_real_exp_sq t ht, ← Real.exp_nat_mul]
  congr 1
  ring

lemma gaussian_exp_norm_sq_integrable {n : ℕ} (t : ℝ) (ht : t < 1/2) :
    Integrable (fun g : EuclideanSpace ℝ (Fin n) => Real.exp (t * ‖g‖^2))
       (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  by_contra h
  have hh := gaussian_exp_norm_sq (n := n) t ht
  rw [integral_undef h] at hh
  exact (Real.exp_ne_zero _).symm hh

lemma gaussian_norm_upper {n : ℕ} :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).real
      {g | 4 * (n : ℝ) < ‖g‖^2} ≤ Real.exp (-(n : ℝ)/2) := by
  let μ := stdGaussian (EuclideanSpace ℝ (Fin n))
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := μ)
    (f := fun g => Real.exp ((1/4 : ℝ) * ‖g‖^2))
    (ae_of_all _ (fun _ => (Real.exp_pos _).le))
    (gaussian_exp_norm_sq_integrable (1/4) (by norm_num)) (Real.exp n)
  rw [gaussian_exp_norm_sq (1/4) (by norm_num)] at hmark
  have hs : {g : EuclideanSpace ℝ (Fin n) | 4 * (n : ℝ) < ‖g‖^2} ⊆
      {g | Real.exp n ≤ Real.exp ((1/4 : ℝ) * ‖g‖^2)} := by
    intro g hg
    apply Real.exp_le_exp.mpr
    change 4 * (n : ℝ) < ‖g‖^2 at hg
    linarith
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  calc
    _ ≤ μ.real {g | Real.exp n ≤ Real.exp ((1/4 : ℝ) * ‖g‖^2)} := measureReal_mono hs
    _ ≤ Real.exp (-(n : ℝ)/2 * Real.log (1-2*(1/4 : ℝ))) / Real.exp n :=
      (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa [mul_comm] using hmark)
    _ ≤ Real.exp (-(n : ℝ)/2) := by
      rw [← Real.exp_sub]
      apply Real.exp_le_exp.mpr
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      have hl : Real.log (1-2*(1/4 : ℝ)) = -Real.log 2 := by
        norm_num
        rw [show (1/2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
      rw [hl]
      nlinarith

lemma gaussian_norm_lower {n : ℕ} :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).real
      {g | ‖g‖^2 < (n : ℝ)/4} ≤ Real.exp (-(n : ℝ)/8) := by
  let μ := stdGaussian (EuclideanSpace ℝ (Fin n))
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := μ)
    (f := fun g => Real.exp ((-1/2 : ℝ) * ‖g‖^2))
    (ae_of_all _ (fun _ => (Real.exp_pos _).le))
    (gaussian_exp_norm_sq_integrable (-1/2) (by norm_num)) (Real.exp (-(n : ℝ)/8))
  rw [gaussian_exp_norm_sq (-1/2) (by norm_num)] at hmark
  have hs : {g : EuclideanSpace ℝ (Fin n) | ‖g‖^2 < (n : ℝ)/4} ⊆
      {g | Real.exp (-(n : ℝ)/8) ≤ Real.exp ((-1/2 : ℝ) * ‖g‖^2)} := by
    intro g hg
    apply Real.exp_le_exp.mpr
    change ‖g‖^2 < (n : ℝ)/4 at hg
    linarith
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  calc
    _ ≤ μ.real {g | Real.exp (-(n : ℝ)/8) ≤ Real.exp ((-1/2 : ℝ) * ‖g‖^2)} := measureReal_mono hs
    _ ≤ Real.exp (-(n : ℝ)/2 * Real.log (1-2*(-1/2 : ℝ))) / Real.exp (-(n : ℝ)/8) :=
      (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa [mul_comm] using hmark)
    _ ≤ Real.exp (-(n : ℝ)/8) := by
      rw [← Real.exp_sub]
      apply Real.exp_le_exp.mpr
      norm_num only at *
      have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at hh ⊢
      nlinarith

lemma gaussian_norm_tail {n : ℕ} :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).real
      {g | ‖g‖ ∉ Icc (Real.sqrt n / 2) (2 * Real.sqrt n)} ≤
      2 * Real.exp (-(n : ℝ)/8) := by
  have hs : {g : EuclideanSpace ℝ (Fin n) | ‖g‖ ∉ Icc (Real.sqrt n / 2) (2 * Real.sqrt n)} ⊆
      {g | ‖g‖^2 < (n : ℝ)/4} ∪ {g | 4 * (n : ℝ) < ‖g‖^2} := by
    intro g hg
    change ¬(Real.sqrt n / 2 ≤ ‖g‖ ∧ ‖g‖ ≤ 2 * Real.sqrt n) at hg
    have hsq := Real.sq_sqrt (Nat.cast_nonneg n)
    have hsqrt := Real.sqrt_nonneg (n : ℝ)
    have hnorm := norm_nonneg g
    rcases not_and_or.mp hg with h | h
    · exact Or.inl (by simp only [mem_ofPred_eq]; nlinarith [lt_of_not_ge h])
    · exact Or.inr (by simp only [mem_ofPred_eq]; nlinarith [lt_of_not_ge h])
  calc
    _ ≤ _ := measureReal_mono hs
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ Real.exp (-(n : ℝ)/8) + Real.exp (-(n : ℝ)/2) :=
      add_le_add gaussian_norm_lower gaussian_norm_upper
    _ ≤ 2 * Real.exp (-(n : ℝ)/8) := by
      have hh : Real.exp (-(n : ℝ)/2) ≤ Real.exp (-(n : ℝ)/8) :=
        Real.exp_le_exp.mpr (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
      linarith

lemma gaussian_truncated_sq_bound {n : ℕ} :
    (∫ g : EuclideanSpace ℝ (Fin n),
      ({g | 4*(n : ℝ) < ‖g‖^2} : Set (EuclideanSpace ℝ (Fin n))).indicator
        (fun g => ‖g‖^2) g ∂stdGaussian (EuclideanSpace ℝ (Fin n))) ≤
      16 * Real.exp (-(n : ℝ)/12) := by
  let μ := stdGaussian (EuclideanSpace ℝ (Fin n))
  have hm (g : EuclideanSpace ℝ (Fin n)) :
      ({g | 4*(n : ℝ) < ‖g‖^2} : Set (EuclideanSpace ℝ (Fin n))).indicator
        (fun g => ‖g‖^2) g ≤
      (16 * Real.exp (-(n : ℝ)/4)) * Real.exp ((1/8 : ℝ) * ‖g‖^2) := by
    by_cases hg : 4*(n : ℝ) < ‖g‖^2
    · simp only [Set.indicator, Set.mem_ofPred_eq, hg, ↓reduceIte]
      have he := Real.add_one_le_exp (‖g‖^2/16)
      have hh : Real.exp (‖g‖^2/16) ≤
          Real.exp (-(n : ℝ)/4) * Real.exp ((1/8 : ℝ) * ‖g‖^2) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        linarith
      nlinarith
    · simp only [Set.indicator, Set.mem_ofPred_eq, hg, ↓reduceIte]
      positivity
  have hi := (gaussian_exp_norm_sq_integrable (n := n) (1/8) (by norm_num)).const_mul
    (16 * Real.exp (-(n : ℝ)/4))
  calc
    _ ≤ ∫ g : EuclideanSpace ℝ (Fin n),
        (16 * Real.exp (-(n : ℝ)/4)) * Real.exp ((1/8 : ℝ) * ‖g‖^2) ∂μ := by
      apply integral_mono_of_nonneg
      · exact ae_of_all _ (fun g => Set.indicator_nonneg (fun g _ => sq_nonneg ‖g‖) g)
      · exact hi
      · exact ae_of_all _ hm
    _ = 16 * Real.exp (-(n : ℝ)/4 - (n : ℝ)/2 * Real.log (1-2*(1/8 : ℝ))) := by
      rw [integral_const_mul, gaussian_exp_norm_sq (1/8) (by norm_num), mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ 16 * Real.exp (-(n : ℝ)/12) := by
      gcongr
      have hl : Real.log (1-2*(1/8 : ℝ)) = -Real.log (4/3) := by
        norm_num
        rw [show (3/4 : ℝ) = (4/3 : ℝ)⁻¹ by norm_num, Real.log_inv]
      rw [hl]
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4/3)
      have hn := Nat.cast_nonneg (α := ℝ) n
      nlinarith

lemma gaussian_norm_sq_integrable {n : ℕ} :
    Integrable (fun g : EuclideanSpace ℝ (Fin n) => ‖g‖^2)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  apply Integrable.mono' ((gaussian_exp_norm_sq_integrable (n := n) (1/4) (by norm_num)).const_mul 4)
  · fun_prop
  · filter_upwards [] with g
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have := Real.add_one_le_exp ((1/4 : ℝ) * ‖g‖^2)
    linarith

end NormTails

section Truncation
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "μ" => stdGaussian E

noncomputable def truncate (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  {g | ‖g‖^2 ≤ 4*(n : ℝ)}.indicator f

lemma measurable_truncation_set : MeasurableSet {g : E | ‖g‖^2 ≤ 4*(n : ℝ)} := by
  measurability

lemma measurable_tail_set : MeasurableSet {g : E | 4*(n : ℝ) < ‖g‖^2} := by
  measurability

lemma integrable_truncate {f : E → ℝ} (hf : Integrable f μ) :
    Integrable (truncate n f) μ := hf.indicator measurable_truncation_set

lemma truncation_bias {f : E → ℝ} (hf : Integrable f μ)
    (hb : ∀ g, 4*(n : ℝ) < ‖g‖^2 → |f g| ≤ ‖g‖^2) :
    |(∫ g, truncate n f g ∂μ) - ∫ g, f g ∂μ| ≤
      16 * Real.exp (-(n : ℝ)/12) := by
  let T : Set E := {g | 4*(n : ℝ) < ‖g‖^2}
  have hT : MeasurableSet T := measurable_tail_set
  have hid (g : E) : truncate n f g - f g = -T.indicator f g := by
    by_cases h : ‖g‖^2 ≤ 4*(n : ℝ)
    · simp [truncate, T, h, not_lt.mpr h]
    · simp [truncate, T, h, lt_of_not_ge h]
  rw [← integral_sub (integrable_truncate hf) hf]
  simp_rw [hid]
  rw [integral_neg, abs_neg]
  calc
    |∫ g, T.indicator f g ∂μ| ≤ ∫ g, |T.indicator f g| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ g, T.indicator (fun g => ‖g‖^2) g ∂μ := by
      apply integral_mono ((hf.indicator hT).abs) (gaussian_norm_sq_integrable.indicator hT)
      intro g
      by_cases hg : g ∈ T
      · simpa [Set.indicator_of_mem hg] using hb g hg
      · simp [Set.indicator_of_notMem hg]
    _ ≤ _ := gaussian_truncated_sq_bound

lemma inner_sq_integrable (v : E) : Integrable (fun g => (inner ℝ v g)^2) μ := by
  apply Integrable.mono' (gaussian_norm_sq_integrable.const_mul (‖v‖^2))
  · fun_prop
  · filter_upwards [] with g
    simp only [Real.norm_eq_abs, abs_sq]
    have h := abs_real_inner_le_norm v g
    simpa only [sq_abs, mul_pow] using pow_le_pow_left₀ (abs_nonneg _) h 2

lemma truncation_covariance_bias (v : E) (hv : ‖v‖ = 1) :
    |(∫ g, truncate n (fun g => (inner ℝ v g)^2) g ∂μ) - 1| ≤
      16 * Real.exp (-(n : ℝ)/12) := by
  have h := truncation_bias (inner_sq_integrable v) (fun g hg => by
    have hh := abs_real_inner_le_norm v g
    rw [hv, one_mul] at hh
    simpa only [abs_sq, sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hh 2)
  simpa [gaussian_inner_sq, hv] using h

lemma truncation_fourier_bias (hn : 1 ≤ n) (v w : E) (hv : ‖v‖ = 1) :
    |(∫ g, truncate n (fun g => inner ℝ g v * Real.sin (inner ℝ g w)) g ∂μ) -
      inner ℝ w v * Real.exp (-‖w‖^2/2)| ≤
      16 * Real.exp (-(n : ℝ)/12) := by
  have h := truncation_bias (gaussian_linear_sin_integrable w v) (fun g hg => by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hh := abs_real_inner_le_norm g v
    rw [hv, mul_one] at hh
    have hn1 : 1 ≤ ‖g‖ := by nlinarith [norm_nonneg g]
    calc
      |inner ℝ g v * Real.sin (inner ℝ g w)| ≤ |inner ℝ g v| * 1 := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)
      _ ≤ ‖g‖^2 := by nlinarith)
  simpa only [gaussian_linear_sin] using h

lemma truncate_fourier_bound (v w : E) (hv : ‖v‖ = 1) (g : E) :
    |truncate n (fun g => inner ℝ g v * Real.sin (inner ℝ g w)) g| ≤ 2*Real.sqrt n := by
  by_cases hg : ‖g‖^2 ≤ 4*(n : ℝ)
  · have hh := abs_real_inner_le_norm g v
    rw [hv, mul_one] at hh
    have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n)
    have hb : ‖g‖ ≤ 2*Real.sqrt n := by nlinarith [Real.sqrt_nonneg (n : ℝ), norm_nonneg g]
    simp only [truncate, Set.indicator, Set.mem_ofPred_eq, hg, ↓reduceIte, abs_mul]
    calc
      _ ≤ |inner ℝ g v| * 1 := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)
      _ ≤ _ := by linarith
  · simp only [truncate, Set.indicator, Set.mem_ofPred_eq, hg, ↓reduceIte, abs_zero]
    positivity

lemma truncate_covariance_bound (v : E) (hv : ‖v‖ = 1) (g : E) :
    |truncate n (fun g => (inner ℝ v g)^2) g| ≤ 4*(n : ℝ) := by
  by_cases hg : ‖g‖^2 ≤ 4*(n : ℝ)
  · have hh := abs_real_inner_le_norm v g
    rw [hv, one_mul] at hh
    have hb := pow_le_pow_left₀ (abs_nonneg _) hh 2
    rw [sq_abs] at hb
    simp only [truncate, Set.indicator, Set.mem_ofPred_eq, hg, ↓reduceIte, abs_sq]
    nlinarith
  · simp only [truncate, Set.indicator, Set.mem_ofPred_eq, hg, ↓reduceIte, abs_zero]
    positivity
end Truncation

end UniformSparsestCut.GaussianTools

end

end OAI
