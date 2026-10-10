import OAI.Geometry.ProjectionBodies.SignSpectrum

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped NNReal ENNReal RealInnerProductSpace Gradient
namespace PettyProjection.Spherical

lemma norm_gradient_eq {n : ℕ} (f : Space n → ℝ) (x : Space n) :
    ‖∇ f x‖ = ‖fderiv ℝ f x‖ :=
  (InnerProductSpace.toDual ℝ (Space n)).symm.norm_map _

lemma gradient_pow {n : ℕ} {f : Space n → ℝ} {x : Space n}
    (hf : DifferentiableAt ℝ f x) (k : ℕ) :
    ∇ (fun y => f y^k) x = ((k : ℝ)*f x^(k-1)) • ∇ f x := by
  apply (InnerProductSpace.toDual ℝ (Space n)).injective
  rw [toDual_gradient, map_smul, toDual_gradient]
  simpa only [nsmul_eq_mul] using (hf.hasFDerivAt.pow k).fderiv

lemma signField_eq_gradient {n : ℕ} (k : ℝ) (f : Space n → ℝ) (u : Sphere n) :
    signField k f u = f u • (u : Space n) +
      k⁻¹ • (∇ f u - ⟪∇ f u,(u : Space n)⟫ • (u : Space n)) := by
  rw [inner_gradient_left]
  rfl

lemma norm_signField_le {n : ℕ} (k : ℝ) (f : Space n → ℝ) (u : Sphere n) :
    ‖signField k f u‖ ≤ |f u| + 2*|k⁻¹| *‖fderiv ℝ f u‖ := by
  rw [signField_eq_gradient]
  calc
    _ ≤ ‖f u • (u : Space n)‖ + ‖k⁻¹ • (∇ f u - ⟪∇ f u,(u : Space n)⟫ • (u : Space n))‖ := norm_add_le _ _
    _ ≤ |f u| + |k⁻¹| *(‖∇ f u‖ + |⟪∇ f u,(u : Space n)⟫|) := by
      simp only [norm_smul, norm_coe, mul_one, Real.norm_eq_abs]
      gcongr
      have h := norm_sub_le (∇ f u) (⟪∇ f u,(u : Space n)⟫ • (u : Space n))
      simpa only [norm_smul, norm_coe, mul_one, Real.norm_eq_abs] using h
    _ ≤ |f u| + |k⁻¹| *(‖∇ f u‖ + ‖∇ f u‖) := by
      gcongr
      simpa only [norm_coe, mul_one] using abs_real_inner_le_norm (∇ f u) (u : Space n)
    _ = _ := by rw [norm_gradient_eq]; ring

lemma normSmooth_powerField_bound {n : ℕ} (g : Seminorm ℝ (Space n)) (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j (u : Sphere n),
      ‖signField (k : ℝ) (fun x => normSmooth g (shrinkingBump n j) x^k) u‖ ≤ B := by
  obtain ⟨C,hC⟩ := seminorm_lipschitz n g
  let M : ℝ := 2*C
  have hM : 0 ≤ M := by positivity
  have hv (j : ℕ) (u : Sphere n) : |normSmooth g (shrinkingBump n j) u| ≤ M := by
    have hg : |g u| ≤ C := by
      have h := hC.dist_le_mul (u : Space n) 0
      simpa only [map_zero, dist_zero_right, norm_coe, mul_one, Real.norm_eq_abs] using h
    have he := normSmooth_dist_le g (shrinkingBump n j) hC u
    have hr : (shrinkingBump n j).rOut ≤ 1 := by
      change 1 / ((j : ℝ)+1) ≤ 1
      exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) j])
    have hc := mul_le_mul_of_nonneg_left hr C.coe_nonneg
    have ht := abs_add_le (normSmooth g (shrinkingBump n j) u-g u) (g u)
    rw [sub_add_cancel] at ht
    rw [Real.dist_eq] at he
    dsimp [M]
    linarith
  have hd (j : ℕ) (u : Sphere n) :
      ‖fderiv ℝ (fun x => normSmooth g (shrinkingBump n j) x^k) u‖ ≤
        (k : ℝ) * M^(k-1) * C := by
    have hdiff := (normSmooth_contDiff g (shrinkingBump n j)).differentiable (by norm_num) (u : Space n)
    rw [(hdiff.hasFDerivAt.pow k).fderiv, norm_smul, Real.norm_eq_abs,
      nsmul_eq_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k), abs_pow]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hv j u) _) (Nat.cast_nonneg _))
      (norm_fderiv_le_of_lipschitz ℝ (normSmooth_lipschitz g _ hC)) (norm_nonneg _) (by positivity)
  refine ⟨M^k + 2*|(k : ℝ)⁻¹| *((k : ℝ)*M^(k-1)*C), by positivity, ?_⟩
  intro j u
  exact (norm_signField_le _ _ u).trans (add_le_add
    (by simpa only [abs_pow] using pow_le_pow_left₀ (abs_nonneg _) (hv j u) k)
    (mul_le_mul_of_nonneg_left (hd j u) (by positivity)))

lemma normSmooth_powerField_tendsto {n : ℕ} (g : Seminorm ℝ (Space n)) (k : ℕ) :
    ∀ᵐ (u : Sphere n) ∂sigma n,
      Tendsto (fun j => signField (k : ℝ) (fun x => normSmooth g (shrinkingBump n j) x^k) u)
        atTop (𝓝 (signField (k : ℝ) (fun x => g x^k) u)) := by
  filter_upwards [seminorm_ae_differentiable_sphere g] with u hu
  have hg : Tendsto (fun j => ∇ (fun x => normSmooth g (shrinkingBump n j) x^k) u)
      atTop (𝓝 (∇ (fun x => g x^k) u)) := by
    simp_rw [gradient_pow ((normSmooth_contDiff g _).differentiable (by norm_num) (u : Space n)) k, gradient_pow hu k]
    exact (((normSmooth_tendsto g u).pow (k-1)).const_mul (k : ℝ)).smul (normSmooth_gradient_tendsto g hu)
  simp_rw [signField_eq_gradient]
  exact ((normSmooth_tendsto g u).pow k).smul_const (u : Space n) |>.add
    ((hg.sub ((hg.inner (tendsto_const_nhds (x := (u : Space n)))).smul_const (u : Space n))).const_smul (k : ℝ)⁻¹)

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical

lemma signedPair_tendsto {n : ℕ} [NeZero n] {F G : ℕ → Sphere n → Space n}
    {F₀ G₀ : Sphere n → Space n} {B C : ℝ} (hB : 0 ≤ B)
    (hF : ∀ j, Continuous (F j)) (hG : ∀ j, Continuous (G j))
    (hFB : ∀ j u, ‖F j u‖ ≤ B) (hGC : ∀ j u, ‖G j u‖ ≤ C)
    (hFlim : ∀ᵐ u ∂sigma n, Tendsto (fun j => F j u) atTop (𝓝 (F₀ u)))
    (hGlim : ∀ᵐ u ∂sigma n, Tendsto (fun j => G j u) atTop (𝓝 (G₀ u))) :
    Tendsto (fun j => signedPair (F j) (G j)) atTop (𝓝 (signedPair F₀ G₀)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => B*C)
  · intro j
    exact (signedPair_integrable (hF j) (hG j)).aestronglyMeasurable
  · exact integrable_const _
  · intro j
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul (abs_sign_le _) (abs_real_inner_le_norm _ _) (abs_nonneg _) (by norm_num)).trans
      (by simpa only [one_mul] using mul_le_mul (hFB j z.1) (hGC j z.2) (norm_nonneg _) hB)
  · filter_upwards [Measure.quasiMeasurePreserving_fst.ae hFlim,
      Measure.quasiMeasurePreserving_snd.ae hGlim] with z hzF hzG
    exact (hzF.inner hzG).const_mul _

lemma ae_bound_of_limit {n : ℕ} {F : ℕ → Sphere n → Space n}
    {F₀ : Sphere n → Space n} {B : ℝ} (hFB : ∀ j u, ‖F j u‖ ≤ B)
    (hFlim : ∀ᵐ u ∂sigma n, Tendsto (fun j => F j u) atTop (𝓝 (F₀ u))) :
    ∀ᵐ u ∂sigma n, ‖F₀ u‖ ≤ B := by
  filter_upwards [hFlim] with u hu
  exact le_of_tendsto hu.norm (Eventually.of_forall fun j => hFB j u)

lemma signedPair_integrable_of_ae_bound {n : ℕ} [NeZero n] {F G : Sphere n → Space n}
    {B C : ℝ} (hB : 0 ≤ B)
    (hF : AEStronglyMeasurable F (sigma n)) (hG : AEStronglyMeasurable G (sigma n))
    (hFB : ∀ᵐ u ∂sigma n, ‖F u‖ ≤ B) (hGC : ∀ᵐ u ∂sigma n, ‖G u‖ ≤ C) :
    Integrable (fun z : Sphere n × Sphere n => Real.sign ⟪(z.1 : Space n),(z.2 : Space n)⟫ *
      ⟪F z.1,G z.2⟫) ((sigma n).prod (sigma n)) := by
  apply (integrable_const (B*C)).mono'
  · exact ((sign_measurable.comp (by fun_prop : Continuous
      (fun z : Sphere n × Sphere n => ⟪(z.1 : Space n),(z.2 : Space n)⟫)).measurable).aestronglyMeasurable).mul
        ((hF.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).inner
          (hG.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd))
  · filter_upwards [Measure.quasiMeasurePreserving_fst.ae hFB,
      Measure.quasiMeasurePreserving_snd.ae hGC] with z hzF hzG
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul (abs_sign_le _) (abs_real_inner_le_norm _ _) (abs_nonneg _) (by norm_num)).trans
      (by simpa only [one_mul] using mul_le_mul hzF hzG (norm_nonneg _) hB)

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical

lemma inner_Q_Q_expand {n : ℕ} (hn : 2 ≤ n) [NeZero n] (f g : C(Sphere n, ℝ)) :
    ⟪Q n (toH n f),Q n (toH n g)⟫ = mean (fun u => f u*g u) - mean f*mean g -
      ⟪(harmonicSpace n 2).starProjection (toH n f),(harmonicSpace n 2).starProjection (toH n g)⟫ := by
  rw [inner_Q_Q, Q_eq_sub_projections hn, inner_sub_left, inner_sub_left,
    harmonicSpace_zero_projection, inner_toH, inner_toH]
  have h : mean (fun u => (mean f)*g u) = mean f*mean g := integral_const_mul (mean f) g
  change _ - mean (fun u => mean f*g u) - _ = _
  rw [h]
  congr 1
  have hs := Submodule.inner_starProjection_left_eq_right (harmonicSpace n 2)
    (toH n f) ((harmonicSpace n 2).starProjection (toH n g))
  rw [Submodule.starProjection_eq_self_iff.mpr ((harmonicSpace n 2).starProjection_apply_mem _)] at hs
  exact (Submodule.inner_starProjection_left_eq_right _ _ _).trans hs.symm

lemma sign_spectral_estimate_with_two {n : ℕ} (hn : 2 ≤ n) [NeZero n]
    {a : ℝ} (ha : 0 ≤ a) (f : C(Sphere n, ℝ)) {g : Space n → ℝ}
    (hg : ContDiff ℝ 2 g) :
    mean f*mean (fun x : Sphere n => g x) -
      ((1+a*(4*(n+2)))/((n+1)*(n+3)))*‖Q n (toH n f)‖*
        ‖Q n (toH n (restrictContinuous g hg.continuous))‖ -
      |signFactor n 1 a| * ‖(harmonicSpace n 2).starProjection (toH n f)‖ *
        ‖(harmonicSpace n 2).starProjection (toH n (restrictContinuous g hg.continuous))‖ ≤
      mean (fun x => f x*signOperator a g hg x) := by
  have hi := inner_Q_Q_expand hn f (signOperator a g hg)
  rw [mean_signOperator] at hi
  have hfat := signOperator_projection_even (j := 1) hn a hg
  norm_num only [Nat.mul_one] at hfat
  rw [hfat, real_inner_smul_right] at hi
  have hcs := neg_le_of_abs_le (abs_real_inner_le_norm
    (Q n (toH n f)) (Q n (toH n (signOperator a g hg))))
  have hb := mul_le_mul_of_nonneg_left (norm_Q_signOperator_le hn ha hg)
    (norm_nonneg (Q n (toH n f)))
  have hab := mul_le_mul_of_nonneg_left
    (abs_real_inner_le_norm ((harmonicSpace n 2).starProjection (toH n f))
      ((harmonicSpace n 2).starProjection (toH n (restrictContinuous g hg.continuous))))
      (abs_nonneg (signFactor n 1 a))
  rw [← abs_mul] at hab
  have htwo := neg_le_of_abs_le hab
  rw [hi] at hcs
  nlinarith

lemma sign_form_estimate_with_two {n : ℕ} (hn : 2 ≤ n) [NeZero n]
    {k : ℝ} (hk : 0 < k) {f g : Space n → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    mean (fun u : Sphere n => f u)*mean (fun u : Sphere n => g u) -
      ((1+(2/k+((n : ℝ)-1)/k^2)*(4*(n+2)))/((n+1)*(n+3)))*
        ‖Q n (toH n (restrictContinuous f hf.continuous))‖*
        ‖Q n (toH n (restrictContinuous g hg.continuous))‖ -
      |signFactor n 1 (2/k+((n : ℝ)-1)/k^2)| *
        ‖(harmonicSpace n 2).starProjection (toH n (restrictContinuous f hf.continuous))‖ *
        ‖(harmonicSpace n 2).starProjection (toH n (restrictContinuous g hg.continuous))‖ ≤
      signedPair (signField k f) (signField k g)/cosineConstant n := by
  rw [signedPair_fields hn k hf hg, mul_div_cancel_left₀ _ (cosineConstant_pos n).ne']
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  exact sign_spectral_estimate_with_two hn (a := 2/k+((n : ℝ)-1)/k^2) (by positivity) (restrictContinuous f hf.continuous) hg

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped NNReal ENNReal RealInnerProductSpace Gradient
namespace PettyProjection.Spherical

lemma normSmooth_power_restrict_tendsto {n : ℕ} (g : Seminorm ℝ (Space n)) (k : ℕ) :
    Tendsto (fun j => restrictContinuous (fun x => normSmooth g (shrinkingBump n j) x^k)
      ((normSmooth_contDiff g _).continuous.pow k)) atTop
      (𝓝 (restrictContinuous (fun x => g x^k) ((seminorm_continuous n g).pow k))) := by
  obtain ⟨F,R,hF,_,hFt,_⟩ := seminorm_approximation g
  have h := hFt.pow k
  simp only [hF] at h
  convert h using 1 <;> congr 1

lemma norm_signedPair_tendsto {n : ℕ} [NeZero n]
    (f g : Seminorm ℝ (Space n)) (k : ℕ) :
    Tendsto (fun j => signedPair
      (signField (k : ℝ) (fun x => normSmooth f (shrinkingBump n j) x^k))
      (signField (k : ℝ) (fun x => normSmooth g (shrinkingBump n j) x^k))) atTop
      (𝓝 (signedPair (signField (k : ℝ) (fun x => f x^k))
        (signField (k : ℝ) (fun x => g x^k)))) := by
  obtain ⟨B,hB,hFB⟩ := normSmooth_powerField_bound f k
  obtain ⟨C,_,hGC⟩ := normSmooth_powerField_bound g k
  exact signedPair_tendsto hB
    (fun j => signField_continuous _ ((normSmooth_contDiff f _).pow k |>.of_le (by norm_num)))
    (fun j => signField_continuous _ ((normSmooth_contDiff g _).pow k |>.of_le (by norm_num)))
    hFB hGC (normSmooth_powerField_tendsto f k) (normSmooth_powerField_tendsto g k)

/-- The sign-transform lower bound for powers of arbitrary nonsmooth norms. -/
theorem norm_sign_form {n : ℕ} (hn : 2 ≤ n) [NeZero n]
    (f g : Seminorm ℝ (Space n)) {k : ℕ} (hk : 0 < k)
    (h2 : (harmonicSpace n 2).starProjection (toH n
      (restrictContinuous (fun x => f x^k) ((seminorm_continuous n f).pow k))) = 0) :
    mean (fun u : Sphere n => f u^k)*mean (fun u : Sphere n => g u^k) -
      ((1+(2/(k : ℝ)+((n : ℝ)-1)/(k : ℝ)^2)*(4*(n+2)))/((n+1)*(n+3)))*
        ‖Q n (toH n (restrictContinuous (fun x => f x^k) ((seminorm_continuous n f).pow k)))‖*
        ‖Q n (toH n (restrictContinuous (fun x => g x^k) ((seminorm_continuous n g).pow k)))‖ ≤
      signedPair (signField (k : ℝ) (fun x => f x^k))
        (signField (k : ℝ) (fun x => g x^k))/cosineConstant n := by
  have hF := normSmooth_power_restrict_tendsto f k
  have hG := normSmooth_power_restrict_tendsto g k
  have hmF := (continuous_mean.tendsto _).comp hF
  have hmG := (continuous_mean.tendsto _).comp hG
  have hqF := (((Q n).continuous.comp (toH n).continuous).norm.tendsto _).comp hF
  have hqG := (((Q n).continuous.comp (toH n).continuous).norm.tendsto _).comp hG
  have hpF := ((((harmonicSpace n 2).starProjection.continuous.comp (toH n).continuous).norm).tendsto _).comp hF
  have hpG := ((((harmonicSpace n 2).starProjection.continuous.comp (toH n).continuous).norm).tendsto _).comp hG
  have hleft := ((hmF.mul hmG).sub ((hqF.const_mul
    ((1+(2/(k : ℝ)+((n : ℝ)-1)/(k : ℝ)^2)*(4*(n+2)))/((n+1)*(n+3)))).mul hqG)).sub
      ((hpF.const_mul |signFactor n 1 (2/(k : ℝ)+((n : ℝ)-1)/(k : ℝ)^2)|).mul hpG)
  simp only [Function.comp_apply] at hleft
  rw [h2, norm_zero, mul_zero, zero_mul, sub_zero] at hleft
  exact le_of_tendsto_of_tendsto hleft ((norm_signedPair_tendsto f g k).div_const (cosineConstant n))
    (Eventually.of_forall fun j => sign_form_estimate_with_two hn (by exact_mod_cast hk)
      ((normSmooth_contDiff f _).pow k |>.of_le (by norm_num))
      ((normSmooth_contDiff g _).pow k |>.of_le (by norm_num)))

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical

lemma reverse_lorentz {a b x y : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hx2 : x^2 ≤ a^2-1) (hy2 : y^2 ≤ b^2-1) :
    1 ≤ a*b-x*y := by
  have hab : 0 ≤ a*b-1 := by nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
  have he : (x*y)^2 ≤ (a*b-1)^2 := by
    have hp := mul_le_mul hx2 hy2 (sq_nonneg y) (by nlinarith : 0 ≤ a^2-1)
    nlinarith [sq_nonneg (a-b)]
  have hxy : 0 ≤ x*y := mul_nonneg hx hy
  nlinarith [sq_nonneg (a*b-1-x*y)]

lemma reverse_lorentz_strict {a b x y : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hx2 : x^2 ≤ a^2-1) (hy2 : y^2 ≤ b^2-1)
    (hxs : 1 < a → x^2 < a^2-1) (hys : 1 < b → y^2 < b^2-1)
    (he : a*b-x*y = 1) : a = 1 ∧ b = 1 := by
  have hprod : x*y = a*b-1 := by linarith
  by_cases hA : a = 1
  · have hx0 : x = 0 := by rw [hA] at hx2; nlinarith [sq_nonneg x]
    rw [hA,hx0] at he
    constructor; exact hA; nlinarith
  have ha' : 1 < a := lt_of_le_of_ne ha (Ne.symm hA)
  by_cases hB : b = 1
  · have hy0 : y = 0 := by rw [hB] at hy2; nlinarith [sq_nonneg y]
    rw [hB,hy0] at he
    exact False.elim (hA (by nlinarith))
  have hb' : 1 < b := lt_of_le_of_ne hb (Ne.symm hB)
  have hpa : 0 < a^2-1 := by nlinarith
  have hpb : 0 < b^2-1 := by nlinarith
  have hp : x^2*y^2 < (a^2-1)*(b^2-1) :=
    (mul_le_mul_of_nonneg_left hy2 (sq_nonneg x)).trans_lt
      (mul_lt_mul_of_pos_right (hxs ha') hpb)
  have hbstrict := hys hb'
  nlinarith [sq_nonneg (a-b), sq_nonneg (x*y-(a*b-1))]

lemma coefficient_sign_factor {n : ℕ} (hn : 4 ≤ n) :
    ((1+(2/(Scalar.exponent n : ℝ)+((n : ℝ)-1)/(Scalar.exponent n : ℝ)^2)*
      (4*(n+2)))/((n+1)*(n+3))) = Scalar.coefficient n := by
  unfold Scalar.exponent Scalar.coefficient
  split_ifs with h
  · subst n; norm_num
  · have h1 : (n : ℝ)+1 ≠ 0 := by positivity
    have h3 : (n : ℝ)+3 ≠ 0 := by positivity
    push_cast
    field_simp
    ring

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical
open Scalar

def gaugeMoment {n : ℕ} (g : Seminorm ℝ (Space n)) (k : ℕ) : ℝ :=
  mean (fun u : Sphere n => g u^k)

def gaugeTail {n : ℕ} [NeZero n] (g : Seminorm ℝ (Space n)) (k : ℕ) : ℝ :=
  ‖Q n (toH n (restrictContinuous (fun x => g x^k) ((seminorm_continuous n g).pow k)))‖

lemma gaugeMoment_ranges {n : ℕ} (hn : 4 ≤ n) [NeZero n]
    (g : Seminorm ℝ (Space n)) (hg : ∀ u : Sphere n, 0 < g u)
    (hnorm : mean (fun u : Sphere n => (g u)⁻¹^n) = 1) :
    1 ≤ gaugeMoment g (exponent n-1) ∧ gaugeMoment g (exponent n-1) ≤ gaugeMoment g (exponent n) := by
  obtain ⟨hm,ht,htm,_,_⟩ := norm_mean_ranges hn (restrictContinuous g (seminorm_continuous n g)) hg hnorm
  have hk : 0 < (exponent n : ℝ) := by unfold exponent; split_ifs <;> norm_num
  have hc : ((exponent n : ℝ)-1)/(exponent n : ℝ) ≤ 1 := (div_le_one hk).mpr (by linarith)
  change 0 ≤ gaugeMoment g (exponent n)-1 at hm
  change 0 ≤ gaugeMoment g (exponent n-1)-1 at ht
  change gaugeMoment g (exponent n-1)-1 ≤ _*(gaugeMoment g (exponent n)-1) at htm
  constructor; linarith
  have hp := mul_le_mul_of_nonneg_right hc hm
  linarith

lemma gaugeTail_of_one {n : ℕ} [NeZero n] (g : Seminorm ℝ (Space n)) (k : ℕ)
    (hg : ∀ u : Sphere n, g u = 1) : gaugeTail g k = 0 := by
  have he : restrictContinuous (fun x => g x^k) ((seminorm_continuous n g).pow k) =
      ContinuousMap.const (Sphere n) 1 := by ext u; simp [restrictContinuous,hg u]
  unfold gaugeTail
  rw [he,Q_constant,norm_zero]

lemma scaled_norm_energy {n : ℕ} (hn : 4 ≤ n) [NeZero n]
    (g : Seminorm ℝ (Space n)) (hg : ∀ u : Sphere n, 0 < g u)
    (hnorm : mean (fun u : Sphere n => (g u)⁻¹^n) = 1)
    {s : ℝ} (hs : 0 < s) (hst : 1 ≤ s*gaugeMoment g (exponent n-1)) :
    let a := s*gaugeMoment g (exponent n)
    let e := s*Real.sqrt (coefficient n)*gaugeTail g (exponent n)
    1 ≤ a ∧ 0 ≤ e ∧ e^2 ≤ a^2-1 ∧ (1 < a → e^2 < a^2-1) := by
  dsimp only
  obtain ⟨ht,htm⟩ := gaugeMoment_ranges hn g hg hnorm
  have ha : 1 ≤ s*gaugeMoment g (exponent n) := hst.trans (mul_le_mul_of_nonneg_left htm hs.le)
  have he : 0 ≤ s*Real.sqrt (coefficient n)*gaugeTail g (exponent n) := by
    apply mul_nonneg (mul_nonneg hs.le (Real.sqrt_nonneg _)); exact norm_nonneg _
  have hc := coefficient_pos n
  have hid : (s*Real.sqrt (coefficient n)*gaugeTail g (exponent n))^2 =
      s^2*(coefficient n*gaugeTail g (exponent n)^2) := by
    rw [mul_pow,mul_pow,Real.sq_sqrt hc.le]; ring
  obtain ⟨hnrm,hnrme⟩ := norm_estimate hn g hg hnorm
  change coefficient n*gaugeTail g (exponent n)^2 ≤
      gaugeMoment g (exponent n)^2-gaugeMoment g (exponent n-1)^2 at hnrm
  have hsq : 1 ≤ (s*gaugeMoment g (exponent n-1))^2 := by nlinarith
  have herr : (s*Real.sqrt (coefficient n)*gaugeTail g (exponent n))^2 ≤
      (s*gaugeMoment g (exponent n))^2-1 := by
    rw [hid]
    calc
      _ ≤ s^2*(gaugeMoment g (exponent n)^2-gaugeMoment g (exponent n-1)^2) :=
        mul_le_mul_of_nonneg_left hnrm (sq_nonneg s)
      _ = (s*gaugeMoment g (exponent n))^2-(s*gaugeMoment g (exponent n-1))^2 := by ring
      _ ≤ _ := sub_le_sub_left hsq _
  refine ⟨ha,he,herr,?_⟩
  intro ha'
  by_cases hconst : ∀ u : Sphere n, g u = 1
  · rw [gaugeTail_of_one g _ hconst]
    nlinarith
  have hstrict : coefficient n*gaugeTail g (exponent n)^2 <
      gaugeMoment g (exponent n)^2-gaugeMoment g (exponent n-1)^2 := by
    apply lt_of_le_of_ne hnrm
    intro heq
    exact hconst (hnrme.mp heq)
  rw [hid]
  calc
    _ < s^2*(gaugeMoment g (exponent n)^2-gaugeMoment g (exponent n-1)^2) :=
      mul_lt_mul_of_pos_left hstrict (sq_pos_of_pos hs)
    _ = (s*gaugeMoment g (exponent n))^2-(s*gaugeMoment g (exponent n-1))^2 := by ring
    _ ≤ _ := sub_le_sub_left hsq _

lemma normalized_one_eq {n : ℕ} (hn : 4 ≤ n) [NeZero n]
    (g : Seminorm ℝ (Space n)) (hg : ∀ u : Sphere n, 0 < g u)
    (hnorm : mean (fun u : Sphere n => (g u)⁻¹^n) = 1)
    {s : ℝ} (hs : 0 < s) (hst : 1 ≤ s*gaugeMoment g (exponent n-1))
    (ha : s*gaugeMoment g (exponent n) = 1) :
    (∀ u : Sphere n, g u = 1) ∧ s = 1 := by
  have hne := norm_estimate hn g hg hnorm
  have ht := (gaugeMoment_ranges hn g hg hnorm).1
  have hmt : gaugeMoment g (exponent n) ≤ gaugeMoment g (exponent n-1) := by
    apply (mul_le_mul_iff_right₀ hs).mp
    simpa only [mul_comm s] using (ha.le.trans hst)
  have hm : 0 ≤ gaugeMoment g (exponent n) := by nlinarith [ha]
  have heq : coefficient n*gaugeTail g (exponent n)^2 =
      gaugeMoment g (exponent n)^2-gaugeMoment g (exponent n-1)^2 := by
    have hineq : coefficient n*gaugeTail g (exponent n)^2 ≤
        gaugeMoment g (exponent n)^2-gaugeMoment g (exponent n-1)^2 := hne.1
    apply le_antisymm hineq
    have hc := mul_nonneg (coefficient_pos n).le (sq_nonneg (gaugeTail g (exponent n)))
    nlinarith
  have hconst := hne.2.mp heq
  refine ⟨hconst,?_⟩
  have hmone : gaugeMoment g (exponent n) = 1 := by
    unfold gaugeMoment
    have he : (fun u : Sphere n => g u^exponent n) = (fun _ => (1 : ℝ)) := by funext u; simp [hconst u]
    rw [he,mean_const]
  simpa only [hmone,mul_one] using ha

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped NNReal ENNReal RealInnerProductSpace Gradient
namespace PettyProjection.Spherical

lemma seminorm_euler {n : ℕ} (g : Seminorm ℝ (Space n)) {x : Space n}
    (hd : DifferentiableAt ℝ (g : Space n → ℝ) x) :
    fderiv ℝ g x x = g x := by
  have he : (fun t : ℝ => g (t • x)) =ᶠ[𝓝 (1 : ℝ)] (fun t => t * g x) := by
    filter_upwards [eventually_gt_nhds (zero_lt_one : (0 : ℝ) < 1)] with t ht
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos ht]
  have hx : HasFDerivAt (g : Space n → ℝ) (fderiv ℝ g x) ((1 : ℝ) • x) := by simpa using hd.hasFDerivAt
  have hc := hx.comp_hasDerivAt (1 : ℝ) ((hasDerivAt_id (1 : ℝ)).smul_const x)
  simp only [one_smul] at hc
  have hl := (hasDerivAt_id (1 : ℝ)).mul_const (g x)
  simp only [one_mul] at hl
  exact (hc.congr_of_eventuallyEq he.symm).unique hl

def gaugeField {n : ℕ} (g : Seminorm ℝ (Space n)) (k : ℕ) (u : Sphere n) : Space n :=
  g u^(k-1) • ∇ (g : Space n → ℝ) u

lemma signField_power_eq {n : ℕ} (g : Seminorm ℝ (Space n)) {k : ℕ} (hk : 0 < k)
    {u : Sphere n} (hd : DifferentiableAt ℝ (g : Space n → ℝ) (u : Space n)) :
    signField (k : ℝ) (fun x => g x^k) u = gaugeField g k u := by
  rw [signField_eq_gradient, gradient_pow hd k]
  rw [real_inner_smul_left, inner_gradient_left, seminorm_euler g hd]
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hp : g u^(k-1)*g u = g u^k := by
    rw [← pow_succ]; congr 1; omega
  rw [smul_sub, smul_smul, smul_smul]
  have h1 : (k : ℝ)⁻¹*((k : ℝ)*g u^(k-1)) = g u^(k-1) := by field_simp
  have h2 : (k : ℝ)⁻¹*((k : ℝ)*g u^(k-1)*g u) = g u^k := by
    calc
      _ = ((k : ℝ)⁻¹*((k : ℝ)*g u^(k-1)))*g u := by ring
      _ = _ := by rw [h1,hp]
  rw [h1,h2]
  dsimp only [gaugeField]
  abel

lemma signField_power_ae_eq {n : ℕ} (g : Seminorm ℝ (Space n)) {k : ℕ} (hk : 0 < k) :
    signField (k : ℝ) (fun x => g x^k) =ᵐ[sigma n] gaugeField g k := by
  filter_upwards [seminorm_ae_differentiable_sphere g] with u hu
  exact signField_power_eq g hk hu

lemma gaugeField_measurable_bound {n : ℕ} (g : Seminorm ℝ (Space n)) {k : ℕ} (hk : 0 < k) :
    AEStronglyMeasurable (gaugeField g k) (sigma n) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ u ∂sigma n, ‖gaugeField g k u‖ ≤ B := by
  have hlim := normSmooth_powerField_tendsto g k
  have he := signField_power_ae_eq g hk
  have hm := aestronglyMeasurable_of_tendsto_ae (u := atTop)
    (fun j => (signField_continuous (k : ℝ)
      ((normSmooth_contDiff g _).pow k |>.of_le (by norm_num))).aestronglyMeasurable) hlim
  obtain ⟨B,hB,hbound⟩ := normSmooth_powerField_bound g k
  refine ⟨hm.congr he, B,hB, ?_⟩
  filter_upwards [he, ae_bound_of_limit hbound hlim] with u hu hb
  rw [← hu]; exact hb

lemma signedPair_congr_ae {n : ℕ} {F G F' G' : Sphere n → Space n}
    (hF : F =ᵐ[sigma n] F') (hG : G =ᵐ[sigma n] G') :
    signedPair F G = signedPair F' G' := by
  have : IsFiniteMeasure (sigma n) := by unfold sigma; infer_instance
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hF,
    Measure.quasiMeasurePreserving_snd.ae hG] with z hzF hzG
  rw [hzF,hzG]

lemma signedPair_gaugeField {n : ℕ} (f g : Seminorm ℝ (Space n)) {k : ℕ} (hk : 0 < k) :
    signedPair (signField (k : ℝ) (fun x => f x^k)) (signField (k : ℝ) (fun x => g x^k)) =
      signedPair (gaugeField f k) (gaugeField g k) :=
  signedPair_congr_ae (signField_power_ae_eq f hk) (signField_power_ae_eq g hk)

def absolutePair {n : ℕ} (F G : Sphere n → Space n) : ℝ :=
  ∫ z : Sphere n × Sphere n, |⟪F z.1,G z.2⟫| ∂(sigma n).prod (sigma n)

lemma gaugeField_absolute_integrable {n : ℕ} [NeZero n]
    (f g : Seminorm ℝ (Space n)) {k : ℕ} (hk : 0 < k) :
    Integrable (fun z : Sphere n × Sphere n =>
      |⟪gaugeField f k z.1,gaugeField g k z.2⟫|) ((sigma n).prod (sigma n)) := by
  obtain ⟨hf,B,hB,hFB⟩ := gaugeField_measurable_bound f hk
  obtain ⟨hg,C,_,hGC⟩ := gaugeField_measurable_bound g hk
  apply (integrable_const (B*C)).mono'
  · have hm : AEStronglyMeasurable (fun z : Sphere n × Sphere n =>
        ⟪gaugeField f k z.1,gaugeField g k z.2⟫) ((sigma n).prod (sigma n)) :=
      (hf.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).inner
        (hg.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
    simpa only [Real.norm_eq_abs] using hm.norm
  · filter_upwards [Measure.quasiMeasurePreserving_fst.ae hFB,
      Measure.quasiMeasurePreserving_snd.ae hGC] with z hzF hzG
    simpa only [Real.norm_eq_abs, abs_abs] using
      (abs_real_inner_le_norm _ _).trans (mul_le_mul hzF hzG (norm_nonneg _) hB)

lemma signedPair_gaugeField_le_absolute {n : ℕ} [NeZero n]
    (f g : Seminorm ℝ (Space n)) {k : ℕ} (hk : 0 < k) :
    signedPair (gaugeField f k) (gaugeField g k) ≤
      absolutePair (gaugeField f k) (gaugeField g k) := by
  obtain ⟨hf,B,hB,hFB⟩ := gaugeField_measurable_bound f hk
  obtain ⟨hg,C,_,hGC⟩ := gaugeField_measurable_bound g hk
  apply integral_mono (signedPair_integrable_of_ae_bound hB hf hg hFB hGC)
    (gaugeField_absolute_integrable f g hk)
  intro z
  exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (abs_sign_le _))

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical
open Scalar

lemma norm_absolutePair_lower {n : ℕ} (hn : 4 ≤ n) [NeZero n]
    (f g : Seminorm ℝ (Space n))
    (h2 : (harmonicSpace n 2).starProjection (toH n
      (restrictContinuous (fun x => f x^exponent n) ((seminorm_continuous n f).pow _))) = 0) :
    gaugeMoment f (exponent n)*gaugeMoment g (exponent n) -
      coefficient n*gaugeTail f (exponent n)*gaugeTail g (exponent n) ≤
      absolutePair (gaugeField f (exponent n)) (gaugeField g (exponent n))/cosineConstant n := by
  have hk : 0 < exponent n := by unfold exponent; split_ifs <;> norm_num
  have h := norm_sign_form (by omega) f g hk h2
  rw [coefficient_sign_factor hn, signedPair_gaugeField f g hk] at h
  exact h.trans (div_le_div_of_nonneg_right (signedPair_gaugeField_le_absolute f g hk)
    (cosineConstant_pos n).le)

/-- Spherical form of the full bilinear estimate, before construction of the
variational representing bodies. Both norms can be nonsmooth. -/
theorem normalized_norm_pair {n : ℕ} (hn : 4 ≤ n) [NeZero n]
    (f g : Seminorm ℝ (Space n)) (hf : ∀ u : Sphere n, 0 < f u) (hg : ∀ u : Sphere n, 0 < g u)
    (hfn : mean (fun u : Sphere n => (f u)⁻¹^n) = 1)
    (hgn : mean (fun u : Sphere n => (g u)⁻¹^n) = 1)
    (h2 : (harmonicSpace n 2).starProjection (toH n
      (restrictContinuous (fun x => f x^exponent n) ((seminorm_continuous n f).pow _))) = 0)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hsf : 1 ≤ s*gaugeMoment f (exponent n-1)) (htg : 1 ≤ t*gaugeMoment g (exponent n-1)) :
    cosineConstant n ≤ s*t*absolutePair (gaugeField f (exponent n)) (gaugeField g (exponent n)) ∧
    (s*t*absolutePair (gaugeField f (exponent n)) (gaugeField g (exponent n)) = cosineConstant n →
      (∀ u : Sphere n, f u = 1) ∧ (∀ u : Sphere n, g u = 1) ∧ s = 1 ∧ t = 1) := by
  let a := s*gaugeMoment f (exponent n)
  let b := t*gaugeMoment g (exponent n)
  let x := s*Real.sqrt (coefficient n)*gaugeTail f (exponent n)
  let y := t*Real.sqrt (coefficient n)*gaugeTail g (exponent n)
  obtain ⟨ha,hx,hx2,hxs⟩ := scaled_norm_energy hn f hf hfn hs hsf
  obtain ⟨hb,hy,hy2,hys⟩ := scaled_norm_energy hn g hg hgn ht htg
  have hlor := reverse_lorentz ha hb hx hy hx2 hy2
  have hid : a*b-x*y = s*t*(gaugeMoment f (exponent n)*gaugeMoment g (exponent n)-
      coefficient n*gaugeTail f (exponent n)*gaugeTail g (exponent n)) := by
    calc
      _ = s*t*(gaugeMoment f (exponent n)*gaugeMoment g (exponent n)-
          (Real.sqrt (coefficient n))^2*gaugeTail f (exponent n)*gaugeTail g (exponent n)) := by
        dsimp only [a,b,x,y]; ring
      _ = _ := by rw [Real.sq_sqrt (coefficient_pos n).le]
  have hlow : a*b-x*y ≤ s*t*
      (absolutePair (gaugeField f (exponent n)) (gaugeField g (exponent n))/cosineConstant n) := by
    rw [hid]
    exact mul_le_mul_of_nonneg_left (norm_absolutePair_lower hn f g h2) (mul_nonneg hs.le ht.le)
  have hbound : cosineConstant n ≤ s*t*absolutePair
      (gaugeField f (exponent n)) (gaugeField g (exponent n)) := by
    have h := hlor.trans hlow
    rw [← mul_div_assoc] at h
    simpa only [one_mul] using (le_div_iff₀ (cosineConstant_pos n)).mp h
  refine ⟨hbound,?_⟩
  intro heq
  have hupper : a*b-x*y ≤ 1 := by
    rw [← mul_div_assoc,heq,div_self (cosineConstant_pos n).ne'] at hlow
    exact hlow
  obtain ⟨ha1,hb1⟩ := reverse_lorentz_strict ha hb hx hy hx2 hy2 hxs hys (le_antisymm hupper hlor)
  obtain ⟨hf1,hs1⟩ := normalized_one_eq hn f hf hfn hs hsf ha1
  obtain ⟨hg1,ht1⟩ := normalized_one_eq hn g hg hgn ht htg hb1
  exact ⟨hf1,hg1,hs1,ht1⟩

end PettyProjection.Spherical
end

end OAI
