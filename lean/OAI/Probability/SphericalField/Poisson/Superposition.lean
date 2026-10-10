import Mathlib
import OAI.Probability.SphericalField.Poisson.FractionalMoments
import OAI.Probability.SphericalField.Gibbs.ReplicaCalculus
import OAI.Probability.SphericalField.Gibbs.Convexity

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
lemma poissonRandomMeasureLaw_superposition {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ ζ : Measure S) [SFinite κ] [SFinite ζ] :
    ((poissonRandomMeasureLaw κ).prod (poissonRandomMeasureLaw ζ)).map
      (fun p => p.1+p.2) = poissonRandomMeasureLaw (κ+ζ) := by
  have hm : Measurable (fun p : Measure S × Measure S => p.1+p.2) := by fun_prop
  apply measureLaw_eq_of_laplace
  intro f hf hf0
  rw [integral_map hm.aemeasurable (poissonLaplace_measurable hf).aestronglyMeasurable]
  have hsum (p : Measure S × Measure S) : poissonLaplace f (p.1+p.2) =
      poissonLaplace f p.1 * poissonLaplace f p.2 := by
    simp only [poissonLaplace,lintegral_add_measure,expNegENNReal_add]
  simp_rw [hsum]
  have hi (ν : Measure S) [SFinite ν] : Integrable (poissonLaplace f) (poissonRandomMeasureLaw ν) :=
    Integrable.of_bound (poissonLaplace_measurable hf).aestronglyMeasurable 1
      (ae_of_all _ fun η => by simpa only [Real.norm_eq_abs,abs_of_nonneg (poissonLaplace_bounds f η).1]
        using (poissonLaplace_bounds f η).2)
  rw [integral_prod _ ((hi κ).mul_prod (hi ζ))]
  simp_rw [integral_const_mul]
  rw [integral_mul_const,poissonRandomMeasureLaw_laplace κ hf hf0,
    poissonRandomMeasureLaw_laplace ζ hf hf0,poissonRandomMeasureLaw_laplace (κ+ζ) hf hf0,
    lintegral_add_measure,expNegENNReal_add]

lemma poissonRandomMeasureLaw_of_finite {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ : Measure S) [IsFiniteMeasure κ] :
    poissonRandomMeasureLaw κ = finitePoissonLaw (κ univ).toNNReal (finiteIntensityMarks κ) := by
  apply measureLaw_eq_of_laplace
  intro f hf hf0
  rw [poissonRandomMeasureLaw_laplace κ hf hf0,finitePoissonLaw_laplace_nonneg _ _ hf hf0]
  have hi : Integrable (fun x => 1 - Real.exp (-f x)) (finiteIntensityMarks κ) := by
    apply Integrable.of_bound (measurable_const.sub hf.neg.exp).aestronglyMeasurable 1
    exact ae_of_all _ fun x => by
      change |1-Real.exp (-f x)| ≤ 1
      rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hf0 x))))]
      linarith [Real.exp_pos (-f x)]
  congr 1
  calc
    _ = ((κ univ).toNNReal : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (1-Real.exp (-f x))
        ∂finiteIntensityMarks κ := by
      conv_lhs => rw [← finiteIntensityMarks_smul κ]
      rw [lintegral_smul_measure]
      rfl
    _ = _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hi
        (ae_of_all _ fun x => sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hf0 x)))),
        ENNReal.ofReal_mul (NNReal.coe_nonneg _),ENNReal.ofReal_coe_nnreal]

lemma aemeasurable_randomMeasure_lintegral_of_finite {Ω S : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] {P : Measure Ω} {A : Ω → Measure S}
    (hA : Measurable A) (hfinite : ∀ᵐ ω ∂P, A ω univ < ⊤)
    {H : Ω × S → ℝ≥0∞} (hH : Measurable H) :
    AEMeasurable (fun ω => ∫⁻ x, H (ω,x) ∂A ω) P := by
  have hm : Measurable (fun ω => ⨆ n : ℕ, ∫⁻ x, H (ω,x) ∂finiteMeasureCutKernel n (A ω)) := by
    apply Measurable.iSup
    intro n
    exact hH.lintegral_kernel_prod_right' (κ := (finiteMeasureCutKernel n).comap A hA)
  apply hm.aemeasurable.congr
  filter_upwards [hfinite] with ω hω
  apply le_antisymm
  · apply iSup_le
    intro n
    change (∫⁻ x, H (ω,x) ∂(if A ω univ ≤ n then A ω else 0)) ≤ _
    split_ifs <;> simp
  · obtain ⟨n,hn⟩ := ENNReal.exists_nat_gt hω.ne
    calc
      (∫⁻ x, H (ω,x) ∂A ω) = ∫⁻ x, H (ω,x) ∂finiteMeasureCutKernel n (A ω) := by
        change _ = ∫⁻ x, H (ω,x) ∂(if A ω univ ≤ n then A ω else 0)
        rw [ite_eq_left hn.le]
      _ ≤ _ := le_iSup (fun m : ℕ => ∫⁻ x, H (ω,x) ∂finiteMeasureCutKernel m (A ω)) n

lemma poissonRandomMeasureLaw_ae_restrict_finite {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ : Measure S) [SFinite κ] {E : Set S} (hE : MeasurableSet E) (hκ : κ E < ⊤) :
    ∀ᵐ η ∂poissonRandomMeasureLaw κ, (η.restrict E) univ < ⊤ := by
  have he : (∫⁻ η, η E ∂poissonRandomMeasureLaw κ) = κ E := by
    simpa only [lintegral_indicator hE,lintegral_one,Measure.restrict_apply_univ]
      using poissonRandomMeasureLaw_campbell κ (measurable_const.indicator hE :
        Measurable (E.indicator (fun _ : S => (1 : ℝ≥0∞))))
  simpa only [Measure.restrict_apply_univ] using
    ae_lt_top (Measure.measurable_coe hE) (he ▸ hκ.ne)

lemma poissonRandomMeasureLaw_ae_null {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ : Measure S) [SFinite κ] {E : Set S} (hE : MeasurableSet E) (hκ : κ E = 0) :
    ∀ᵐ η ∂poissonRandomMeasureLaw κ, η E = 0 := by
  have he : (∫⁻ η, η E ∂poissonRandomMeasureLaw κ) = 0 := by
    rw [← hκ]
    simpa only [lintegral_indicator hE,lintegral_one,Measure.restrict_apply_univ]
      using poissonRandomMeasureLaw_campbell κ (measurable_const.indicator hE :
        Measurable (E.indicator (fun _ : S => (1 : ℝ≥0∞))))
  exact (lintegral_eq_zero_iff (Measure.measurable_coe hE)).mp he

lemma stablePoissonTotal_rpow_integrable {b a : ℝ} (hb0 : 0 < b) (hb1 : b < 1)
    (hab : a < b) : Integrable (fun η => stablePoissonTotal η ^ a)
      (poissonRandomMeasureLaw (stableLogIntensity b)) := by
  by_cases ha : 0 ≤ a
  · exact stablePoissonTotal_fractional_integrable hb0 hb1 ha hab
  · have ha' : 0 < -a := neg_pos.mpr (lt_of_not_ge ha)
    simpa only [neg_neg] using stablePoissonTotal_negative_integrable hb0 hb1 ha'

lemma log_sq_le_two_rpow {x ε : ℝ} (hx : 0 < x) (hε : 0 < ε) :
    (Real.log x)^2 ≤ (x^(2*ε)+x^(-(2*ε)))/ε^2 := by
  have hpow : (x^ε/ε)^2 = x^(2*ε)/ε^2 := by
    rw [div_pow,← Real.rpow_two,← Real.rpow_mul hx.le]
    congr 2
    ring
  have hinvpow : ((x⁻¹)^ε/ε)^2 = x^(-(2*ε))/ε^2 := by
    rw [div_pow,← Real.rpow_two,← Real.rpow_mul (inv_nonneg.mpr hx.le),
      Real.inv_rpow hx.le,← Real.rpow_neg hx.le]
    congr 2
    ring
  by_cases hl : 0 ≤ Real.log x
  · have hh := pow_le_pow_left₀ hl (Real.log_le_rpow_div hx.le hε) 2
    rw [hpow] at hh
    exact hh.trans (div_le_div_of_nonneg_right (le_add_of_nonneg_right (Real.rpow_nonneg hx.le _)) (sq_nonneg ε))
  · have hh := pow_le_pow_left₀ (le_of_lt (neg_pos.mpr (lt_of_not_ge hl)))
      (show -Real.log x ≤ (x⁻¹)^ε/ε by
        simpa only [Real.log_inv] using Real.log_le_rpow_div (inv_nonneg.mpr hx.le) hε) 2
    rw [neg_sq,hinvpow] at hh
    exact hh.trans (div_le_div_of_nonneg_right (le_add_of_nonneg_left (Real.rpow_nonneg hx.le _)) (sq_nonneg ε))

lemma stablePoissonTotal_weighted_log_sq_integrable {b a : ℝ} (hb0 : 0 < b) (hb1 : b < 1)
    (hab : a < b) : Integrable (fun η => stablePoissonTotal η ^ a *
      (Real.log (stablePoissonTotal η))^2) (poissonRandomMeasureLaw (stableLogIntensity b)) := by
  let ε : ℝ := (b-a)/4
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hplus : a+2*ε < b := by dsimp [ε]; linarith
  have hminus : a-2*ε < b := by linarith
  have hI := ((stablePoissonTotal_rpow_integrable hb0 hb1 hplus).add
    (stablePoissonTotal_rpow_integrable hb0 hb1 hminus)).div_const (ε^2)
  apply hI.mono' ((stablePoissonTotal_measurable.pow_const a).mul
    (stablePoissonTotal_measurable.log.pow_const (2 : ℕ))).aestronglyMeasurable
  filter_upwards [stablePoissonTotal_pos hb0 hb1] with η hη
  change |stablePoissonTotal η^a*(Real.log (stablePoissonTotal η))^2| ≤
    (stablePoissonTotal η^(a+2*ε)+stablePoissonTotal η^(a-2*ε))/ε^2
  rw [abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hη.le _) (sq_nonneg _))]
  calc
    _ ≤ stablePoissonTotal η ^ a * ((stablePoissonTotal η ^ (2*ε)+
        stablePoissonTotal η ^ (-(2*ε)))/ε^2) :=
      mul_le_mul_of_nonneg_left (log_sq_le_two_rpow hη hε) (Real.rpow_nonneg hη.le _)
    _ = _ := by
      rw [← mul_div_assoc,mul_add,← Real.rpow_add hη,← Real.rpow_add hη]
      rfl

lemma stablePoissonTotal_log_memLp_two {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    MemLp (fun η => Real.log (stablePoissonTotal η)) 2
      (poissonRandomMeasureLaw (stableLogIntensity b)) := by
  apply (memLp_two_iff_integrable_sq stablePoissonTotal_measurable.log.aestronglyMeasurable).mpr
  simpa only [Real.rpow_zero,one_mul] using
    stablePoissonTotal_weighted_log_sq_integrable (a := 0) hb0 hb1 hb0

end SphericalPerceptron

namespace SphericalPerceptron
lemma quadratic_contact_remainders {A : ℝ → ℝ} {u a c s dA : ℝ}
    (hd : HasDerivAt A dA u)
    (hmin : IsLocalMin (fun t => c*(t-a)^2-A t) u)
    (hp : c*(u-a)^2-A u ≤ c*(u+s-a)^2-A (u+s))
    (hm : c*(u-a)^2-A u ≤ c*(u-s-a)^2-A (u-s)) :
    A (u+s)-A u-s*dA ≤ c*s^2 ∧ A (u-s)-A u+s*dA ≤ c*s^2 := by
  have he := hmin.hasDerivAt_eq_zero
    (((((hasDerivAt_id u).sub_const a).pow 2).const_mul c).sub hd)
  norm_num only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] at he
  constructor <;> nlinarith [congrArg (fun t : ℝ => t*s) he]

lemma integral_convex_contact_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {f : Ω → ℝ → ℝ} {A : ℝ → ℝ}
    {d : Ω → ℝ} {u s dA C δ : ℝ} (hs : 0 < s)
    (hdm : AEStronglyMeasurable d P)
    (hf : ∀ᵐ ω ∂P, ConvexOn ℝ univ (f ω) ∧ HasDerivAt (f ω) (d ω) u)
    (hp : A (u+s)-A u-s*dA ≤ C*s^2) (hm : A (u-s)-A u+s*dA ≤ C*s^2)
    (hip : Integrable (fun ω => f ω (u+s)) P)
    (hi0 : Integrable (fun ω => f ω u) P)
    (him : Integrable (fun ω => f ω (u-s)) P)
    (hbp : (∫ ω, |f ω (u+s)-A (u+s)| ∂P) ≤ δ)
    (hb0 : (∫ ω, |f ω u-A u| ∂P) ≤ δ)
    (hbm : (∫ ω, |f ω (u-s)-A (u-s)| ∂P) ≤ δ) :
    (∫ ω, |d ω-dA| ∂P) ≤ C*s+4*δ/s := by
  have ip := (hip.sub (integrable_const (A (u+s)))).abs
  have i0 := (hi0.sub (integrable_const (A u))).abs
  have im := (him.sub (integrable_const (A (u-s)))).abs
  let B := fun ω => C*s+(|f ω (u+s)-A (u+s)|+2*|f ω u-A u|+|f ω (u-s)-A (u-s)|)/s
  have hB : Integrable B P := (integrable_const (C*s)).add ((ip.add (i0.const_mul 2) |>.add im).div_const s)
  have hbound : ∀ᵐ ω ∂P, |d ω-dA| ≤ B ω := hf.mono fun ω hω =>
    convex_contact_derivative_bound hs hω.1 hω.2 hp hm
  have hi : Integrable (fun ω => |d ω-dA|) P := hB.mono'
    (by simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hdm.sub aestronglyMeasurable_const).norm) (hbound.mono fun ω hω => by simpa using hω)
  calc
    _ ≤ ∫ ω, B ω ∂P := integral_mono_ae hi hB hbound
    _ = C*s+((∫ ω, |f ω (u+s)-A (u+s)| ∂P)+
        2*(∫ ω, |f ω u-A u| ∂P)+(∫ ω, |f ω (u-s)-A (u-s)| ∂P))/s := by
      have he := integral_add (integrable_const (C*s)) ((ip.add (i0.const_mul 2) |>.add im).div_const s)
      have he' := integral_add (ip.add (i0.const_mul 2)) im
      have he'' := integral_add ip (i0.const_mul 2)
      simp only [Pi.add_apply,Pi.sub_apply] at he he' he''
      dsimp only [B]
      rw [he,integral_div,he',he'']
      simp [integral_const_mul]
    _ ≤ _ := by
      apply add_le_add_right
      apply div_le_div_of_nonneg_right _ hs.le
      linarith

lemma integral_centered_abs_le_sqrt_variance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : MemLp X 2 P) :
    (∫ ω, |X ω-∫ η, X η ∂P| ∂P) ≤ Real.sqrt (variance X P) := by
  have hC : MemLp (fun ω => X ω-∫ η, X η ∂P) 2 P := hX.sub (memLp_const _)
  have hA := hC.norm
  have hv := variance_nonneg (fun ω => |X ω-∫ η, X η ∂P|) P
  rw [variance_eq_sub (by simpa only [Real.norm_eq_abs] using hA)] at hv
  simp only [Pi.pow_apply,sq_abs] at hv
  rw [← variance_eq_integral hX.aestronglyMeasurable.aemeasurable] at hv
  apply (Real.le_sqrt (integral_nonneg fun _ => abs_nonneg _) (variance_nonneg X P)).mpr
  linarith

end SphericalPerceptron

namespace SphericalPerceptron
@[fun_prop] lemma measurable_measure_restrict {S : Type*} [MeasurableSpace S]
    {E : Set S} (hE : MeasurableSet E) : Measurable (fun η : Measure S => η.restrict E) := by
  apply Measure.measurable_of_measurable_coe
  intro t ht
  simp only [Measure.restrict_apply ht]
  exact Measure.measurable_coe (ht.inter hE)

end SphericalPerceptron
end
end

end OAI
