import Mathlib
import OAI.Probability.Subsphere.Mixture.Latitude

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma block_classification (V : Submodule ℝ E) [Nontrivial V] [Nontrivial Vᗮ]
    (μ : Measure E) [SFinite μ] (hunit : ∀ᵐ x ∂μ, ‖x‖ = 1)
    (hinv : ∀ (u : Orthogonal V) (w : Orthogonal Vᗮ), MeasurePreserving (blockIso V u w) μ μ) :
    μ = mixtureLaw V (μ.map (perpCoordinate V)) := by
  apply Measure.ext_of_lintegral
  intro f hf
  let η := (SubsphereRegression.ambientSphereLaw (E := V)).prod
    (SubsphereRegression.ambientSphereLaw (E := Vᗮ))
  have hPhi : Measurable (fun q : ℝ => ∫⁻ z : V × Vᗮ, f (mixtureSampler V (q,z)) ∂η) :=
    Measurable.lintegral_prod_right (hf.comp (measurable_mixtureSampler V))
  have hmix : (∫⁻ x, f x ∂mixtureLaw V (μ.map (perpCoordinate V))) =
      ∫⁻ x, ∫⁻ z : V × Vᗮ, f (mixtureSampler V (perpCoordinate V x,z)) ∂η ∂μ := by
    rw [mixtureLaw,lintegral_map hf (measurable_mixtureSampler V)]
    rw [lintegral_prod (fun z : ℝ × (V × Vᗮ) => f (mixtureSampler V z))
      (hf.comp (measurable_mixtureSampler V)).aemeasurable]
    exact lintegral_map hPhi (measurable_perpCoordinate V)
  rw [hmix]
  have hm : Measurable (fun z : E × (Orthogonal V × Orthogonal Vᗮ) =>
      f (blockIso V z.2.1 z.2.2 z.1)) :=
    hf.comp ((continuous_blockIso V).comp continuous_swap).measurable
  calc
    _ = ∫⁻ z : Orthogonal V × Orthogonal Vᗮ, ∫⁻ x, f (blockIso V z.1 z.2 x) ∂μ
        ∂(orthogonalLaw (E := V)).prod (orthogonalLaw (E := Vᗮ)) := by
      simp_rw [(hinv _ _).lintegral_comp hf]
      simp
    _ = ∫⁻ x, ∫⁻ z : Orthogonal V × Orthogonal Vᗮ, f (blockIso V z.1 z.2 x)
        ∂(orthogonalLaw (E := V)).prod (orthogonalLaw (E := Vᗮ)) ∂μ :=
      (lintegral_lintegral_swap hm.aemeasurable).symm
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [hunit] with x hx
      exact block_average_unit V hx hf

lemma mixtureLaw_mono (V : Submodule ℝ E) [Nontrivial V] [Nontrivial Vᗮ]
    {ρ τ : Measure ℝ} (h : ρ ≤ τ) : mixtureLaw V ρ ≤ mixtureLaw V τ :=
  Measure.map_mono (Measure.prod_mono h le_rfl) (measurable_mixtureSampler V)

lemma mixtureLaw_add (V : Submodule ℝ E) [Nontrivial V] [Nontrivial Vᗮ]
    (ρ τ : Measure ℝ) [SFinite ρ] [SFinite τ] : mixtureLaw V (ρ+τ) = mixtureLaw V ρ+mixtureLaw V τ := by
  simp only [mixtureLaw,Measure.add_prod,Measure.map_add _ _ (measurable_mixtureSampler V)]

lemma mixtureLaw_smul (V : Submodule ℝ E) [Nontrivial V] [Nontrivial Vᗮ]
    (c : ℝ≥0∞) (ρ : Measure ℝ) : mixtureLaw V (c • ρ) = c • mixtureLaw V ρ := by
  simp only [mixtureLaw,Measure.prod_smul_left,
    Measure.map_smul _ (measurable_mixtureSampler V).aemeasurable]

lemma mixtureLaw_domination (V : Submodule ℝ E) [Nontrivial V] [Nontrivial Vᗮ]
    (c : ℝ≥0∞) {ρ τ₀ τ₁ : Measure ℝ} [SFinite τ₀] [SFinite τ₁]
    (h : ρ ≤ c • (τ₀+τ₁)) : mixtureLaw V ρ ≤ c • (mixtureLaw V τ₀+mixtureLaw V τ₁) := by
  simpa only [mixtureLaw_smul,mixtureLaw_add] using mixtureLaw_mono V h

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent

private def betaRaw (a b x : ℝ) : ℝ≥0∞ :=
  if 0 < x ∧ x < 1 then ENNReal.ofReal (x ^ (a - 1) * (1 - x) ^ (b - 1)) else 0

private lemma betaRaw_eq (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) :
    betaRaw a b x = ENNReal.ofReal (beta a b) * betaPDF a b x := by
  by_cases hx : 0 < x ∧ x < 1
  · simp only [betaRaw, betaPDF, betaPDFReal, ite_eq_left hx]
    rw [← ENNReal.ofReal_mul (beta_pos ha hb).le]
    congr 1
    field_simp [(beta_pos ha hb).ne']
  · simp [betaRaw, betaPDF, betaPDFReal, hx]

private lemma lintegral_betaRaw (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∫⁻ x, betaRaw a b x = ENNReal.ofReal (beta a b) := by
  simp_rw [betaRaw_eq a b _ ha hb]
  rw [lintegral_const_mul' _ _]
  · simp [lintegral_betaPDF_eq_one ha hb]
  · exact ENNReal.ofReal_ne_top

lemma beta_antitone_left {a A b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : a ≤ A) :
    beta A b ≤ beta a b := by
  apply (ENNReal.ofReal_le_ofReal_iff (beta_pos ha hb).le).1
  rw [← lintegral_betaRaw A b (lt_of_lt_of_le ha h) hb, ← lintegral_betaRaw a b ha hb]
  apply lintegral_mono
  intro x
  by_cases hx : 0 < x ∧ x < 1
  · simp only [betaRaw, ite_eq_left hx]
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
    exact Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2.le (by linarith)
  · simp [betaRaw, hx]

lemma beta_antitone_right {a b B : ℝ} (ha : 0 < a) (hb : 0 < b) (h : b ≤ B) :
    beta a B ≤ beta a b := by
  have hcomm (u v : ℝ) : beta u v = beta v u := by unfold beta; rw [mul_comm, add_comm]
  rw [hcomm a B, hcomm a b]
  exact beta_antitone_left hb ha h

private lemma rpow_decrease_shift {x a A D : ℝ} (hx : (1 / 2 : ℝ) ≤ x)
    (ha : a ≤ A) (hD : A - a ≤ D) :
    x ^ (a - 1) ≤ (2 : ℝ) ^ D * x ^ (A - 1) := by
  have hx0 : 0 < x := by linarith
  have hfactor : x ^ (a - A) ≤ (2 : ℝ) ^ D := by
    calc
      x ^ (a - A) ≤ (1 / 2 : ℝ) ^ (a - A) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hx (by linarith)
      _ = (2 : ℝ) ^ (A - a) := by
        rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
        congr 1
        ring
      _ ≤ (2 : ℝ) ^ D := Real.rpow_le_rpow_of_exponent_le (by norm_num) hD
  calc
    x ^ (a - 1) = x ^ (a - A) * x ^ (A - 1) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring
    _ ≤ (2 : ℝ) ^ D * x ^ (A - 1) :=
      mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg hx0.le _)

lemma betaPDFReal_domination_right_half {a A b D x : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hA : a ≤ A) (hD : A - a ≤ D)
    (hx : (1 / 2 : ℝ) ≤ x) :
    betaPDFReal a b x ≤ (2 : ℝ) ^ D * betaPDFReal A b x := by
  by_cases hx1 : x < 1
  · have hxx : 0 < x ∧ x < 1 := ⟨by linarith, hx1⟩
    simp only [betaPDFReal, ite_eq_left hxx]
    have hbeta : 1 / beta a b ≤ 1 / beta A b :=
      one_div_le_one_div_of_le (beta_pos (lt_of_lt_of_le ha hA) hb)
        (beta_antitone_left ha hb hA)
    have hp := rpow_decrease_shift hx hA hD
    have hxpow : 0 ≤ x ^ (a - 1) := Real.rpow_nonneg hxx.1.le _
    have hbpow : 0 ≤ (1 - x) ^ (b - 1) := Real.rpow_nonneg (by linarith) _
    calc
      _ ≤ ((1 / beta A b) * ((2 : ℝ) ^ D * x ^ (A - 1))) * (1 - x) ^ (b - 1) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hbeta hp hxpow (le_of_lt (one_div_pos.2 (beta_pos (lt_of_lt_of_le ha hA) hb)))) hbpow
      _ = _ := by ring
  · have hxx : ¬ (0 < x ∧ x < 1) := by tauto
    simp [betaPDFReal, hxx]

lemma betaPDFReal_domination_left_half {a b B D x : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hB : b ≤ B) (hD : B - b ≤ D)
    (hx : x ≤ (1 / 2 : ℝ)) :
    betaPDFReal a b x ≤ (2 : ℝ) ^ D * betaPDFReal a B x := by
  by_cases hxx : 0 < x ∧ x < 1
  · simp only [betaPDFReal, ite_eq_left hxx]
    have hbeta : 1 / beta a b ≤ 1 / beta a B :=
      one_div_le_one_div_of_le (beta_pos ha (lt_of_lt_of_le hb hB))
        (beta_antitone_right ha hb hB)
    have hp := rpow_decrease_shift (x := 1 - x) (by linarith) hB hD
    have hxpow : 0 ≤ x ^ (a - 1) := Real.rpow_nonneg hxx.1.le _
    have hbpow : 0 ≤ (1 - x) ^ (b - 1) := Real.rpow_nonneg (by linarith [hxx.2]) _
    calc
      _ ≤ ((1 / beta a B) * x ^ (a - 1)) * ((2 : ℝ) ^ D * (1 - x) ^ (B - 1)) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hbeta hxpow) hp hbpow
          (mul_nonneg (le_of_lt (one_div_pos.2 (beta_pos ha (lt_of_lt_of_le hb hB)))) hxpow)
      _ = _ := by ring
  · simp [betaPDFReal, hxx]

theorem betaMeasure_two_component {a A b B D : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hA : a ≤ A) (hB : b ≤ B)
    (hAD : A - a ≤ D) (hBD : B - b ≤ D) :
    betaMeasure a b ≤ ENNReal.ofReal ((2 : ℝ) ^ D) •
      (betaMeasure A b + betaMeasure a B) := by
  have hpdf : betaPDF a b ≤ fun x => ENNReal.ofReal ((2 : ℝ) ^ D) *
      (betaPDF A b x + betaPDF a B x) := by
    intro x
    rcases le_total (1 / 2 : ℝ) x with hx | hx
    · have h := betaPDFReal_domination_right_half ha hb hA hAD hx
      have hh := ENNReal.ofReal_le_ofReal h
      rw [ENNReal.ofReal_mul (by positivity)] at hh
      exact hh.trans (mul_le_mul' le_rfl (le_add_right le_rfl))
    · have h := betaPDFReal_domination_left_half ha hb hB hBD hx
      have hh := ENNReal.ofReal_le_ofReal h
      rw [ENNReal.ofReal_mul (by positivity)] at hh
      exact hh.trans (mul_le_mul' le_rfl (le_add_left le_rfl))
  have hm : Measurable (betaPDF A b) := (measurable_betaPDFReal A b).ennreal_ofReal
  unfold betaMeasure
  rw [← withDensity_add_left hm,
    ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  exact withDensity_mono (Filter.Eventually.of_forall hpdf)

end SubsphereCurrent
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The full geometric two-component domination, not just a scalar-density bound. -/
theorem directionLaw_domination (V N : Submodule ℝ E) (hVN : V ≤ N)
    (hj : 1 ≤ Module.finrank ℝ V) (hjn : Module.finrank ℝ V < Module.finrank ℝ N)
    (hnD : Module.finrank ℝ N < Module.finrank ℝ E) (e : Metric.sphere (0 : V) 1) :
    directionLaw V N ≤ (2 : ℝ≥0∞)^Module.finrank ℝ E •
      (SubsphereRegression.ambientSphereLaw + latitudeLaw V e
        (((Module.finrank ℝ N : ℝ)-(Module.finrank ℝ V : ℝ))/2)
        (((Module.finrank ℝ E : ℝ)-(Module.finrank ℝ N : ℝ))/2)) := by
  have hk := V.finrank_add_finrank_orthogonal
  have hr := latitude_rank V e
  let : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (M := E) (by omega)
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℝ) (M := V) (by omega)
  let : Nontrivial Vᗮ := Module.nontrivial_of_finrank_pos (R := ℝ) (M := Vᗮ) (by omega)
  let : Nontrivial N := Module.nontrivial_of_finrank_pos (R := ℝ) (M := N) (by omega)
  let : Nontrivial (latitudeSpace V e) := Module.nontrivial_of_finrank_pos
    (R := ℝ) (M := latitudeSpace V e) (by omega)
  let a := ((Module.finrank ℝ N : ℝ)-(Module.finrank ℝ V : ℝ))/2
  let delta := ((Module.finrank ℝ E : ℝ)-(Module.finrank ℝ N : ℝ))/2
  let A := ((Module.finrank ℝ E : ℝ)-(Module.finrank ℝ V : ℝ))/2
  let b := (Module.finrank ℝ V : ℝ)/2
  let B := delta+((Module.finrank ℝ V : ℝ)-1)/2
  have hjR : (1 : ℝ) ≤ Module.finrank ℝ V := by exact_mod_cast hj
  have hjnR : (Module.finrank ℝ V : ℝ) < Module.finrank ℝ N := by exact_mod_cast hjn
  have hnDR : (Module.finrank ℝ N : ℝ)+1 ≤ Module.finrank ℝ E := by
    exact_mod_cast (Nat.add_one_le_iff.mpr hnD)
  have hdimR : (0 : ℝ) ≤ Module.finrank ℝ E := by positivity
  have ha : 0 < a := by dsimp [a]; linarith
  have hd : 0 < delta := by dsimp [delta]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  have hA : a ≤ A := by dsimp [a,A]; linarith
  have hB : b ≤ B := by dsimp [b,B,delta]; linarith
  have hshape : a+delta = A := by dsimp [a,delta,A]; ring
  have hAb : (Module.finrank ℝ Vᗮ : ℝ)/2 = A := by
    have hkR : (Module.finrank ℝ V : ℝ)+(Module.finrank ℝ Vᗮ : ℝ) = Module.finrank ℝ E := by
      exact_mod_cast hk
    dsimp [A]
    linarith
  have hbb : (Module.finrank ℝ Vᗮᗮ : ℝ)/2 = b := by
    have heq : Module.finrank ℝ Vᗮᗮ = Module.finrank ℝ V :=
      congrArg (fun U : Submodule ℝ E => Module.finrank ℝ U) (Submodule.orthogonal_orthogonal V)
    rw [heq]
  have huniBeta : MeasurePreserving (perpCoordinate V) SubsphereRegression.ambientSphereLaw
      (betaMeasure A b) := by
    let : Nontrivial Vᗮᗮ := by simpa using (inferInstance : Nontrivial V)
    change MeasurePreserving (fun x : E => ‖Vᗮ.orthogonalProjectionOnto x‖^2) _ _
    simpa only [hAb,hbb] using sphere_projection_beta Vᗮ
  have hlatBeta : MeasurePreserving (perpCoordinate V) (latitudeLaw V e a delta)
      (betaMeasure a B) := by
    by_cases hj1 : Module.finrank ℝ V = 1
    · have hB1 : B = delta := by dsimp [B]; rw [hj1]; norm_num
      rw [hB1]
      exact latitudeLaw_beta_one V e hj1 (by omega) ha hd
    · exact latitudeLaw_beta_gt_one V e (by omega) (hjn.trans hnD) ha hd hshape
  let : IsProbabilityMeasure (latitudeLaw V e a delta) := latitudeLaw_probability V e ha hd
  let : IsProbabilityMeasure (betaMeasure A b) := isProbabilityMeasureBeta (ha.trans_le hA) hb
  let : IsProbabilityMeasure (betaMeasure a B) := isProbabilityMeasureBeta ha (hb.trans_le hB)
  have hdir : directionLaw V N = mixtureLaw V (betaMeasure a b) := by
    rw [block_classification V (directionLaw V N) (directionLaw_unit V N)
      (directionLaw_invariant V N hVN), (directionLaw_beta V N hVN (by omega) hjn).map_eq]
  have huni : SubsphereRegression.ambientSphereLaw = mixtureLaw V (betaMeasure A b) := by
    rw [block_classification V SubsphereRegression.ambientSphereLaw
      SubsphereRegression.ambientSphereLaw_ae_norm
      (fun u w => SubsphereRegression.ambientSphereLaw_isometry (blockIso V u w)),huniBeta.map_eq]
  have hlat : latitudeLaw V e a delta = mixtureLaw V (betaMeasure a B) := by
    rw [block_classification V (latitudeLaw V e a delta) (latitudeLaw_unit V e ha hd)
      (latitudeLaw_invariant V e ha hd),hlatBeta.map_eq]
  have hscalar : betaMeasure a b ≤ (2 : ℝ≥0∞)^Module.finrank ℝ E •
      (betaMeasure A b+betaMeasure a B) := by
    have hAD : A-a ≤ (Module.finrank ℝ E : ℝ) := by dsimp [A,a]; linarith
    have hBD : B-b ≤ (Module.finrank ℝ E : ℝ) := by dsimp [B,b,delta]; linarith
    have h := SubsphereCurrent.betaMeasure_two_component ha hb hA hB hAD hBD
    simpa only [Real.rpow_natCast, ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_ofNat] using h
  change directionLaw V N ≤ _ • (SubsphereRegression.ambientSphereLaw + latitudeLaw V e a delta)
  rw [hdir,huni,hlat]
  exact mixtureLaw_domination V _ hscalar

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory Set
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

lemma ambientSphereLaw_transport (e : E ≃ₗᵢ[ℝ] F) :
    MeasurePreserving e SubsphereRegression.ambientSphereLaw SubsphereRegression.ambientSphereLaw := by
  have hs : MeasurePreserving (Polar.sphereMap e) (SubsphereRegression.sphereLaw (E := E))
      (SubsphereRegression.sphereLaw (E := F)) := Polar.sphereMap_preserving e
  refine ⟨e.continuous.measurable,?_⟩
  rw [SubsphereRegression.ambientSphereLaw,SubsphereRegression.ambientSphereLaw,
    Measure.map_map e.continuous.measurable (by fun_prop),← hs.map_eq,
    Measure.map_map (by fun_prop) hs.measurable]
  rfl

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma block_bottom_haar [Nontrivial E] {x : E} (hx : ‖x‖ = 1) :
    MeasurePreserving (fun w : Orthogonal (⊥ : Submodule ℝ E)ᗮ => blockIso ⊥ 1 w x)
      orthogonalLaw SubsphereRegression.ambientSphereLaw := by
  let K : Submodule ℝ E := (⊥ : Submodule ℝ E)ᗮ
  have hK : K = ⊤ := Submodule.bot_orthogonal_eq_top
  let e := LinearIsometryEquiv.ofTop E K hK
  let : Nontrivial K := e.symm.injective.nontrivial
  let xK : K := ⟨x,by simp [K]⟩
  have h := (ambientSphereLaw_transport e).comp (haar_eval_preserving (show ‖xK‖ = 1 from hx))
  convert h using 1
  funext w
  exact blockIso_on_right ⊥ 1 w xK

lemma directionLaw_bottom (N : Submodule ℝ E) [Nontrivial N] [Nontrivial E] :
    directionLaw ⊥ N = SubsphereRegression.ambientSphereLaw := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hm := measurable_directionSampler (⊥ : Submodule ℝ E) N
  rw [directionLaw,lintegral_map hf hm]
  rw [lintegral_prod_symm (fun z : Orthogonal (⊥ : Submodule ℝ E)ᗮ × N =>
    f (blockIso ⊥ 1 z.1 (z.2 : E))) (hf.comp hm).aemeasurable]
  calc
    _ = ∫⁻ _x : N, (∫⁻ y, f y ∂SubsphereRegression.ambientSphereLaw)
        ∂SubsphereRegression.ambientSphereLaw := by
      apply lintegral_congr_ae
      filter_upwards [SubsphereRegression.ambientSphereLaw_ae_norm (E := N)] with x hx
      exact (block_bottom_haar (show ‖(x : E)‖ = 1 from hx)).lintegral_comp hf
    _ = _ := by simp

lemma measurable_directionJointSampler (V N : Submodule ℝ E) (t : ℕ) :
    Measurable (fun z : Orthogonal Vᗮ × (Fin t → N) => fun i => blockIso V 1 z.1 (z.2 i : E)) := by
  apply Measurable.of_eval
  intro i
  exact ((continuous_blockIso V).comp
    ((continuous_const.prodMk continuous_fst).prodMk
      (continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd)))).measurable

lemma directionJointLaw_top (V : Submodule ℝ E) (t : ℕ) [Nontrivial E] :
    directionJointLaw V ⊤ t = Measure.pi (fun _ : Fin t => SubsphereRegression.ambientSphereLaw) := by
  let : Nontrivial (⊤ : Submodule ℝ E) :=
    (LinearIsometryEquiv.ofTop E (⊤ : Submodule ℝ E) rfl).symm.injective.nontrivial
  apply Measure.ext_of_lintegral
  intro f hf
  have hm := measurable_directionJointSampler V (⊤ : Submodule ℝ E) t
  rw [directionJointLaw,lintegral_map hf hm]
  rw [lintegral_prod (fun z : Orthogonal Vᗮ × (Fin t → (⊤ : Submodule ℝ E)) =>
    f (fun i => blockIso V 1 z.1 (z.2 i : E))) (hf.comp hm).aemeasurable]
  have h (w : Orthogonal Vᗮ) :
      (∫⁻ x : Fin t → (⊤ : Submodule ℝ E), f (fun i => blockIso V 1 w (x i : E))
        ∂Measure.pi (fun _ => SubsphereRegression.ambientSphereLaw)) =
      ∫⁻ x : Fin t → E, f x ∂Measure.pi (fun _ => SubsphereRegression.ambientSphereLaw) := by
    let e := (LinearIsometryEquiv.ofTop E (⊤ : Submodule ℝ E) rfl).trans (blockIso V 1 w)
    exact (measurePreserving_pi (fun _ : Fin t => SubsphereRegression.ambientSphereLaw)
      (fun _ => SubsphereRegression.ambientSphereLaw)
      (fun _ => ambientSphereLaw_transport e)).lintegral_comp hf
  simp_rw [h]
  simp

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture

theorem mixture_estimate (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : MixtureEstimate E := by
  refine ⟨directionLaw_domination,?_,?_⟩
  · intro N hN
    let : Nontrivial N := Module.nontrivial_of_finrank_pos (R := ℝ) (M := N) (by omega)
    have hNE := Submodule.finrank_le N
    let : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (M := E) (by omega)
    exact directionLaw_bottom N
  · intro V t hE
    let : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (M := E) (by omega)
    exact directionJointLaw_top V t

end SubsphereCurrent.Mixture
end
end

end OAI
