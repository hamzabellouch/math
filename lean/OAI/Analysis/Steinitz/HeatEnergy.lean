import OAI.Analysis.Steinitz.PathLaws

namespace OAI

/-! Survival-energy estimates and simultaneous diagonal separation. -/

section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators Pointwise
namespace GaussianKernel
variable {ι : Type*} [Fintype ι]

lemma pdf_scale {s : ℝ≥0} (hs : 0<s) (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal 0 (s^2*v) ((s:ℝ)*x) = (s:ℝ)⁻¹*gaussianPDFReal 0 v x := by
  have hs' : 0<(s:ℝ) := hs
  have he : 2*Real.pi*((s:ℝ)^2*(v:ℝ))=(s:ℝ)^2*(2*Real.pi*(v:ℝ)) := by ring
  unfold gaussianPDFReal
  simp only [sub_zero,NNReal.coe_mul,NNReal.coe_pow,he,Real.sqrt_mul (sq_nonneg (s:ℝ)),
    Real.sqrt_sq hs'.le,mul_inv_rev]
  have hx : -(((s:ℝ)*x)^2)/(2*((s:ℝ)^2*(v:ℝ))) = -(x^2)/(2*(v:ℝ)) := by
    rw [mul_pow]
    field_simp
  rw [hx]
  ring

lemma density_scale {s : ℝ≥0} (hs : 0<s) (v : ι → ℝ≥0) (x : EuclideanSpace ℝ ι) :
    density (fun i => s^2*v i) ((s:ℝ) • x) = ((s:ℝ)^(Fintype.card ι))⁻¹*density v x := by
  simp only [density,PiLp.smul_apply,smul_eq_mul,pdf_scale hs,Finset.prod_mul_distrib,
    Finset.prod_const,Finset.card_univ,inv_pow]

lemma chainWeight_scale {s : ℝ≥0} (hs : 0<s) (v : ι → ℝ≥0) (n : ℕ)
    (p : Fin (n+1) → EuclideanSpace ℝ ι) :
    HeatL2.chainWeight (kernel (fun i => s^2*v i)) n ((s:ℝ) • p) =
      (((s:ℝ)^(Fintype.card ι))⁻¹)^n*HeatL2.chainWeight (kernel v) n p := by
  rw [HeatL2.chainWeight_prod,HeatL2.chainWeight_prod]
  change (∏ t : Fin n,density (fun i => s^2*v i) ((s:ℝ)•p t.succ-(s:ℝ)•p t.castSucc))=_
  simp only [← smul_sub,density_scale hs,Finset.prod_mul_distrib,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin]
  rfl

omit [Fintype ι] in
lemma pi_smul {T : Type*} (s : ℝ) (hs : s≠0) (D : Set (EuclideanSpace ℝ ι)) :
    (univ.pi (fun _ : T => s • D))=s • (univ.pi (fun _ : T => D)) := by
  ext p
  rw [mem_smul_set_iff_inv_smul_mem₀ hs]
  simp only [mem_pi,mem_univ,forall_const,Pi.smul_apply]
  exact forall_congr' fun t => mem_smul_set_iff_inv_smul_mem₀ hs D (p t)

lemma pathMass_scale {s : ℝ≥0} (hs : 0<s) (v : ι → ℝ≥0)
    (D : Set (EuclideanSpace ℝ ι)) (_hD : MeasurableSet D)
    [IsFiniteMeasure (volume.restrict D)] [IsFiniteMeasure (volume.restrict ((s:ℝ) • D))]
    (n : ℕ) :
    HeatL2.pathMass (μ := volume.restrict ((s:ℝ) • D)) (kernel (fun i => s^2*v i)) n =
      (s:ℝ)^(Fintype.card ι)*HeatL2.pathMass (μ := volume.restrict D) (kernel v) n := by
  classical
  have hs' : 0<(s:ℝ) := hs
  let P : Set (Fin (n+1) → EuclideanSpace ℝ ι) := univ.pi (fun _ => D)
  have hh := Measure.setIntegral_comp_smul_of_pos volume
    (HeatL2.chainWeight (kernel (fun i => s^2*v i)) n) P hs'
  simp only [chainWeight_scale hs,integral_const_mul,smul_eq_mul] at hh
  have hdim : Module.finrank ℝ (Fin (n+1) → EuclideanSpace ℝ ι) = (n+1)*Fintype.card ι := by
    simp [Module.finrank_pi_fintype]
  rw [hdim,show P=univ.pi (fun _ : Fin (n+1) => D) from rfl,← pi_smul (s:ℝ) hs'.ne'] at hh
  simp only [volume_pi,Measure.restrict_pi_pi,← HeatL2.pathMass_pi] at hh
  have hn : (s:ℝ)^((n+1)*Fintype.card ι)≠0 := pow_ne_zero _ hs'.ne'
  apply (mul_left_cancel₀ (a := ((s:ℝ)^((n+1)*Fintype.card ι))⁻¹) (inv_ne_zero hn))
  rw [← hh]
  rw [Nat.mul_comm (n+1),pow_mul,pow_succ,mul_inv_rev,← inv_pow]
  calc
    _ = (((s:ℝ)^(Fintype.card ι))^n)⁻¹*HeatL2.pathMass (μ := volume.restrict D) (kernel v) n *
        (((s:ℝ)^(Fintype.card ι))⁻¹*((s:ℝ)^(Fintype.card ι))) := by
      rw [inv_mul_cancel₀ (pow_ne_zero _ hs'.ne'),mul_one]
      simp only [inv_pow]
    _ = _ := by ring

end GaussianKernel

end

section

open MeasureTheory FourierTransform Set Filter ComplexConjugate
open scoped ENNReal ComplexInnerProductSpace
namespace HeatL2
section Rate
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma energy_smul (w : E → ℝ) (c : ℂ) (f : Lp ℂ 2 (volume : Measure E)) :
    energy w (c • f) = ‖c‖^2 * energy w f := by
  unfold energy
  rw [fourier_smul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul c (𝓕 f)] with x hx
  simp only [hx, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  ring

lemma supported_smul (D : Set E) {f : Lp ℂ 2 (volume : Measure E)}
    (hf : f ∈ supported D) (c : ℂ) : c • f ∈ supported D := by
  filter_upwards [hf, Lp.coeFn_smul c f] with x hx he hn
  simp only [he, Pi.smul_apply, hx hn, smul_zero]

lemma form_le_norm (D : Set E) (hD : MeasurableSet D)
    (w : E → ℝ) (hw : AEStronglyMeasurable w volume) (hn : ∀ x, 0 ≤ w x)
    {f : Lp ℂ 2 (volume : Measure E)} (hf : f ∈ supported D) :
    ‖f‖^2 - energy w f ≤ ‖compressedHeat D hD w hw hn‖ * ‖f‖^2 := by
  have hh := (positive_norm_le_iff _ (compressedHeat_positive D hD w hw hn)
    (norm_nonneg _)).mp le_rfl f
  rwa [compressedHeat_inner, (mask_eq_self_iff D hD f).mpr hf] at hh

lemma normalized_energy_lt (D : Set E) (w : E → ℝ)
    {f : Lp ℂ 2 (volume : Measure E)} (hfD : f ∈ supported D) (hfn : f ≠ 0)
    {C : ℝ} (hf : energy w f < C*‖f‖^2) :
    ∃ g : Lp ℂ 2 (volume : Measure E), g ∈ supported D ∧ ‖g‖=1 ∧ energy w g < C := by
  let c : ℂ := (‖f‖⁻¹ : ℝ)
  have hc : ‖c‖ = ‖f‖⁻¹ := by simp [c]
  have hnz : ‖f‖ ≠ 0 := norm_ne_zero_iff.mpr hfn
  have hnorm : ‖c • f‖ = 1 := by rw [norm_smul, hc, inv_mul_cancel₀ hnz]
  refine ⟨c • f, supported_smul D hfD c, hnorm, ?_⟩
  rw [energy_smul, hc]
  have hp : 0 < (‖f‖⁻¹)^2 := sq_pos_of_pos (inv_pos.mpr (norm_pos_iff.mpr hfn))
  calc
    _ < (‖f‖⁻¹)^2 * (C*‖f‖^2) := mul_lt_mul_of_pos_left hf hp
    _ = C*((‖f‖⁻¹)^2*‖f‖^2) := by ring
    _ = C := by rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hnz), mul_one]

lemma exists_supported_energy_lt (D : Set E) (hD : MeasurableSet D)
    (w : E → ℝ) (hw : AEStronglyMeasurable w volume) (hn : ∀ x, 0 ≤ w x)
    {C : ℝ} (hC : 0 ≤ C) (h : C < ‖compressedHeat D hD w hw hn‖) :
    ∃ f : Lp ℂ 2 (volume : Measure E), f ∈ supported D ∧ ‖f‖ = 1 ∧ energy w f < 1-C := by
  obtain ⟨g,hg⟩ := positive_exists_form_gt _ (compressedHeat_positive D hD w hw hn) hC h
  rw [compressedHeat_inner] at hg
  let f := mask D hD g
  change C * ‖g‖^2 < ‖f‖^2 - energy w f at hg
  have hfg : ‖f‖^2 ≤ ‖g‖^2 := sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr (mask_norm_le D hD g)
  have hf : energy w f < (1-C)*‖f‖^2 := by
    have hh := mul_le_mul_of_nonneg_left hfg hC
    nlinarith
  have hfn : f ≠ 0 := by
    intro he
    have := energy_nonneg w hn f
    rw [he, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] at hf
    rw [he] at this
    linarith
  exact normalized_energy_lt D w
    ((mask_eq_self_iff D hD f).mp (mask_idempotent D hD g)) hfn hf

lemma exists_energy_lt_of_exp_le (D : Set E) (hD : MeasurableSet D)
    (w : E → ℝ) (hw : AEStronglyMeasurable w volume) (hn : ∀ x, 0 ≤ w x)
    {c : ℝ} (h : Real.exp (-c) ≤ ‖compressedHeat D hD w hw hn‖)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : Lp ℂ 2 (volume : Measure E), f ∈ supported D ∧ ‖f‖ = 1 ∧ energy w f < c+ε := by
  have he : Real.exp (-(c+ε/2)) < ‖compressedHeat D hD w hw hn‖ := by
    apply lt_of_lt_of_le _ h
    apply Real.exp_lt_exp.mpr
    linarith
  obtain ⟨f,hf,hnf,hef⟩ := exists_supported_energy_lt D hD w hw hn
    (Real.exp_pos (-(c+ε/2))).le he
  refine ⟨f,hf,hnf,hef.trans_le ?_⟩
  have hbound := loss_le_self (c+ε/2)
  dsimp [loss] at hbound
  linarith

lemma compressed_norm_le_of_energy (D : Set E) (hD : MeasurableSet D)
    (w : E → ℝ) (hw : AEStronglyMeasurable w volume) (hn : ∀ x, 0 ≤ w x)
    {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ f : Lp ℂ 2 (volume : Measure E), f ∈ supported D →
      ‖f‖=1 → 1 - energy w f ≤ C) :
    ‖compressedHeat D hD w hw hn‖ ≤ C := by
  by_contra! hg
  obtain ⟨f,hf,hfn,hfe⟩ := exists_supported_energy_lt D hD w hw hn hC hg
  linarith [h f hf hfn]

lemma compressed_norm_mono_symbol (D : Set E) (hD : MeasurableSet D)
    (w v : E → ℝ) (hw : AEStronglyMeasurable w volume) (hv : AEStronglyMeasurable v volume)
    (hwn : ∀ x, 0 ≤ w x) (hvn : ∀ x, 0 ≤ v x) (h : ∀ x, w x ≤ v x) :
    ‖compressedHeat D hD v hv hvn‖ ≤ ‖compressedHeat D hD w hw hwn‖ := by
  apply compressed_norm_le_of_energy D hD v hv hvn (norm_nonneg _)
  intro f hf hfn
  have hE : energy w f ≤ energy v f := by
    rw [energy,energy]
    apply integral_mono (integrable_energy w hw hwn f) (integrable_energy v hv hvn f)
    intro x
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact sub_le_sub_left (Real.exp_le_exp.mpr (neg_le_neg (h x))) 1
  have hh := form_le_norm D hD w hw hwn hf
  rw [hfn, one_pow, mul_one] at hh
  linarith

lemma compressed_norm_mono_domain (D F : Set E) (hD : MeasurableSet D) (hF : MeasurableSet F)
    (hDF : D ⊆ F) (w : E → ℝ) (hw : AEStronglyMeasurable w volume) (hn : ∀ x, 0 ≤ w x) :
    ‖compressedHeat D hD w hw hn‖ ≤ ‖compressedHeat F hF w hw hn‖ := by
  apply compressed_norm_le_of_energy D hD w hw hn (norm_nonneg _)
  intro f hf hfn
  have hfF : f ∈ supported F := by
    change ∀ᵐ x, x ∉ F → f x = 0
    change ∀ᵐ x, x ∉ D → f x = 0 at hf
    filter_upwards [hf] with x hx hnot
    exact hx (fun hxd => hnot (hDF hxd))
  simpa only [hfn,one_pow,mul_one] using form_le_norm F hF w hw hn hfF

lemma compressed_norm_rpow (D : Set E) (hD : MeasurableSet D)
    (w : E → ℝ) (hw : Measurable w) (hn : ∀ x, 0 ≤ w x)
    {t η : ℝ} (hη : 0 < η) (hηt : η ≤ t) :
    ‖compressedHeat D hD (fun ξ => η*w ξ) (hw.const_mul η).aestronglyMeasurable
      (fun ξ => mul_nonneg hη.le (hn ξ))‖ ^ (t/η) ≤
    ‖compressedHeat D hD (fun ξ => t*w ξ) (hw.const_mul t).aestronglyMeasurable
      (fun ξ => mul_nonneg (hη.le.trans hηt) (hn ξ))‖ := by
  let A := compressedHeat D hD (fun ξ => η*w ξ) (hw.const_mul η).aestronglyMeasurable
    (fun ξ => mul_nonneg hη.le (hn ξ))
  let B := compressedHeat D hD (fun ξ => t*w ξ) (hw.const_mul t).aestronglyMeasurable
    (fun ξ => mul_nonneg (hη.le.trans hηt) (hn ξ))
  have hpow : 0 < t/η := div_pos (hη.trans_le hηt) hη
  apply (Real.le_rpow_inv_iff_of_pos (norm_nonneg A) (norm_nonneg B) hpow).mp
  apply compressed_norm_le_of_energy D hD _ _ _ (Real.rpow_nonneg (norm_nonneg B) _)
  intro f hf hfn
  have hh := heat_form_rpow w hw hn hη hηt f hfn
  have hb := form_le_norm D hD (fun ξ => t*w ξ) (hw.const_mul t).aestronglyMeasurable
    (fun ξ => mul_nonneg (hη.le.trans hηt) (hn ξ)) hf
  rw [hfn, one_pow, mul_one] at hb
  simp only [heat_inner, hfn, one_pow] at hh
  have ha : 0 ≤ 1-energy (fun ξ => η*w ξ) f := by
    have := energy_le_norm_sq (fun ξ => η*w ξ) (hw.const_mul η).aestronglyMeasurable
      (fun ξ => mul_nonneg hη.le (hn ξ)) f
    rw [hfn,one_pow] at this
    linarith
  exact (Real.le_rpow_inv_iff_of_pos ha (norm_nonneg B) hpow).mpr (hh.trans hb)

lemma heat_form_pos (w : E → ℝ) (hw : AEStronglyMeasurable w volume) (hn : ∀ x, 0 ≤ w x)
    {f : Lp ℂ 2 (volume : Measure E)} (hf : f ≠ 0) :
    0 < (⟪f, heat w hw hn f⟫).re := by
  rw [heat_inner_integral]
  have hi : Integrable (fun ξ => Real.exp (-w ξ) * ‖(𝓕 f) ξ‖^2) := by
    apply integrable_weight _ (Real.continuous_exp.comp_aestronglyMeasurable hw.neg)
      (C := 1) _ (𝓕 f)
    exact Eventually.of_forall fun ξ => by
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hn ξ))
  have hp ξ : 0 ≤ Real.exp (-w ξ) * ‖(𝓕 f) ξ‖^2 := by positivity
  apply lt_of_le_of_ne (integral_nonneg hp)
  intro he
  have ha := (integral_eq_zero_iff_of_nonneg hp hi).mp he.symm
  have hsq : (fun ξ => ‖(𝓕 f) ξ‖^2) =ᵐ[volume] 0 := by
    filter_upwards [ha] with ξ hξ
    exact (mul_eq_zero.mp hξ).resolve_left (Real.exp_ne_zero _)
  have hz : ‖f‖^2 = 0 := by
    rw [← Lp.norm_fourier_eq f, norm_sq_integral, integral_congr_ae hsq]
    simp only [Pi.zero_apply, integral_zero]
  exact (sq_pos_of_pos (norm_pos_iff.mpr hf)).ne' hz

lemma compressed_norm_pos_of_supported (D : Set E) (hD : MeasurableSet D)
    (w : E → ℝ) (hw : AEStronglyMeasurable w volume) (hn : ∀ x, 0 ≤ w x)
    {f : Lp ℂ 2 (volume : Measure E)} (hf : f ∈ supported D) (hfn : f ≠ 0) :
    0 < ‖compressedHeat D hD w hw hn‖ := by
  have hh := form_le_norm D hD w hw hn hf
  have hp := heat_form_pos w hw hn hfn
  rw [heat_inner] at hp
  have : 0 < ‖compressedHeat D hD w hw hn‖ * ‖f‖^2 := hp.trans_le hh
  exact pos_of_mul_pos_left this (sq_nonneg _)

lemma oneLp_norm_sq {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ] :
    ‖(oneLp : Lp ℂ 2 μ)‖^2 = (μ univ).toReal := by
  rw [norm_sq_integral]
  calc
    _ = ∫ _ : X, (1:ℝ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [oneLp_coe (μ := μ)] with x hx
      simp only [hx, norm_one, one_pow]
    _ = _ := by simp [Measure.real]

lemma compressed_norm_pos (D : Set E) (hD : MeasurableSet D)
    [IsFiniteMeasure (volume.restrict D)] (hDp : 0 < volume D)
    (w : E → ℝ) (hw : AEStronglyMeasurable w volume) (hn : ∀ x, 0 ≤ w x) :
    0 < ‖compressedHeat D hD w hw hn‖ := by
  apply compressed_norm_pos_of_supported D hD w hw hn (extendLp_supported D hD oneLp)
  intro hz
  have he := extendLp_norm D hD (oneLp : Lp ℂ 2 (volume.restrict D))
  rw [hz, norm_zero] at he
  have hp : (0:ℝ) < (volume D).toReal :=
    ENNReal.toReal_pos hDp.ne' (by simpa only [Measure.restrict_apply_univ] using (measure_ne_top (volume.restrict D) univ))
  have hs := oneLp_norm_sq (μ := volume.restrict D)
  rw [Measure.restrict_apply_univ, ← he, zero_pow (by decide : 2 ≠ 0)] at hs
  linarith

end Rate
end HeatL2

end

section

open Set Finset

namespace EuclideanSteinitz

lemma functional_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : (ι → ℝ) →L[ℝ] ℝ) (x : ι → ℝ) :
    L x = ∑ i, L (Pi.single i 1) * x i := by
  have he : x = ∑ i, x i • Pi.single i 1 := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply, apply_ite]
  conv_lhs => rw [he, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, smul_eq_mul, mul_comm]

lemma simultaneous_approx {ι F : Type*} [Fintype ι] [Nonempty F]
    (E : F → ι → ℝ) (c : ℝ)
    (hconv : ∀ f g : F, ∀ t ∈ Icc (0:ℝ) 1, ∃ h : F,
       ∀ i, E h i ≤ t * E f i + (1-t) * E g i)
    (hweighted : ∀ q : ι → ℝ, (∀ i, 0 ≤ q i) → ∀ δ > 0,
       ∃ f : F, ∑ i, q i * E f i < c * ∑ i, q i + δ)
    (ε : ℝ) (hε : 0 < ε) : ∃ f : F, ∀ i, E f i < c + ε := by
  classical
  let A : Set (ι → ℝ) := {u | ∃ f : F, ∀ i, E f i < u i}
  have hA : Convex ℝ A := by
    intro u hu v hv a b ha hb hab
    obtain ⟨f, hf⟩ := hu
    obtain ⟨g, hg⟩ := hv
    obtain ⟨h, hh⟩ := hconv f g a ⟨ha, by linarith⟩
    refine ⟨h, fun i => ?_⟩
    have hstrict : a * E f i + b * E g i < a * u i + b * v i := by
      rcases eq_or_lt_of_le ha with hzero | hap
      · have ha0 : a = 0 := hzero.symm
        simp only [ha0, zero_add] at hab
        simp only [ha0, zero_mul, zero_add, hab, one_mul]
        exact hg i
      · have hf' := mul_lt_mul_of_pos_left (hf i) hap
        have hg' := mul_le_mul_of_nonneg_left (hg i).le hb
        linarith
    change E h i < a * u i + b * v i
    have : 1-a=b := by linarith
    rw [this] at hh
    exact (hh i).trans_lt hstrict
  have hAo : IsOpen A := by
    have he : A = ⋃ f : F, ⋂ i : ι, {u : ι → ℝ | E f i < u i} := by
      ext u
      simp only [A, mem_ofPred_eq, mem_iUnion, mem_iInter]
    rw [he]
    apply isOpen_iUnion
    intro f
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_lt continuous_const (continuous_apply i)
  let x : ι → ℝ := fun _ => c+ε
  by_contra hn
  have hx : x ∉ A := hn
  obtain ⟨L, hL⟩ := geometric_hahn_banach_point_open hA hAo hx
  let q : ι → ℝ := fun i => L (Pi.single i 1)
  have hne : A.Nonempty := by
    obtain ⟨f⟩ := ‹Nonempty F›
    exact ⟨fun i => E f i+1, f, fun _ => by linarith⟩
  obtain ⟨u, hu⟩ := hne
  have hq : ∀ i, 0 ≤ q i := by
    intro i
    by_contra hneg
    have hqi : q i < 0 := lt_of_not_ge hneg
    let r := (L u - L x + 1) / (-q i)
    have hr : 0 ≤ r := by
      apply div_nonneg
      · linarith [hL u hu]
      · exact neg_nonneg.mpr hqi.le
    have huv : u + r • Pi.single i 1 ∈ A := by
      obtain ⟨f, hf⟩ := hu
      refine ⟨f, fun j => (hf j).trans_le ?_⟩
      change u j ≤ u j + r * (Pi.single i (1:ℝ) : ι → ℝ) j
      have hs : 0 ≤ (Pi.single i (1:ℝ) : ι → ℝ) j := by simp only [Pi.single_apply]; split_ifs <;> norm_num
      exact le_add_of_nonneg_right (mul_nonneg hr hs)
    have hxv := hL _ huv
    rw [map_add, map_smul, smul_eq_mul] at hxv
    change L x < L u + r * q i at hxv
    have hri : r * q i = -(L u-L x+1) := by
      dsimp [r]
      field_simp [ne_of_lt hqi]
    linarith
  have hsum : 0 < ∑ i, q i := by
    have hnon := Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hq i)
    by_contra hzero
    have hz : ∑ i, q i = 0 := le_antisymm (le_of_not_gt hzero) hnon
    have hqi : ∀ i, q i = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ (Finset.univ : Finset ι)) => hq j)).mp hz i (mem_univ _)
    have hLu : L u = 0 := by rw [functional_eq_sum]; simp only [← show ∀ i, q i = L (Pi.single i 1) from fun _ => rfl, hqi, zero_mul, Finset.sum_const_zero]
    have hLx : L x = 0 := by rw [functional_eq_sum]; simp only [← show ∀ i, q i = L (Pi.single i 1) from fun _ => rfl, hqi, zero_mul, Finset.sum_const_zero]
    linarith [hL u hu]
  obtain ⟨f, hf⟩ := hweighted q hq (ε*(∑ i, q i)/2) (by positivity)
  let v : ι → ℝ := fun i => E f i + ε/2
  have hv : v ∈ A := ⟨f, fun _ => by dsimp [v]; linarith⟩
  have hvx := hL v hv
  have hLx : L x = (c+ε) * ∑ i, q i := by
    rw [functional_eq_sum]
    change (∑ i, q i * (c+ε)) = _
    rw [← Finset.sum_mul, mul_comm]
  have hLv : L v = (∑ i, q i * E f i) + (ε/2) * ∑ i, q i := by
    rw [functional_eq_sum]
    change (∑ i, q i * (E f i+ε/2)) = _
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
    ring
  rw [hLx, hLv] at hvx
  linarith

end EuclideanSteinitz

end

section

open MeasureTheory FourierTransform Set Filter ComplexConjugate
open scoped ENNReal NNReal ComplexInnerProductSpace
namespace HeatL2
section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

lemma mixture_gaussian_energy_le (A : F →L[ℝ] E) (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (f g : Lp ℂ 2 (volume : Measure E)) :
    energy (gaussianSymbol A) (mixture t ht ht' f g) ≤
      t * energy (gaussianSymbol A) f + (1-t) * energy (gaussianSymbol A) g := by
  simp only [gaussian_energy_difference]
  have hh := integral_mono
    (integrable_difference_sq A (ProbabilityTheory.stdGaussian F) (mixture t ht ht' f g))
    (((integrable_difference_sq A (ProbabilityTheory.stdGaussian F) f).const_mul t).add
      ((integrable_difference_sq A (ProbabilityTheory.stdGaussian F) g).const_mul (1-t)))
    (fun z => mixture_translation_sq_le t ht ht' f g (A z))
  simp only [Pi.add_apply] at hh
  rw [integral_add ((integrable_difference_sq A _ f).const_mul t)
      ((integrable_difference_sq A _ g).const_mul (1-t)), integral_const_mul, integral_const_mul] at hh
  linarith

end

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma mixture_diagonal_energy_le (v : ι → ℝ≥0) (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (f g : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) :
    energy (GaussianKernel.symbol v) (mixture t ht ht' f g) ≤
      t * energy (GaussianKernel.symbol v) f + (1-t) * energy (GaussianKernel.symbol v) g := by
  rw [← GaussianKernel.symbol_eq]
  exact mixture_gaussian_energy_le _ t ht ht' f g

end
end HeatL2

end

section

open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexInnerProductSpace
namespace HeatL2
namespace Diagonal
variable {ι : Type*} [Fintype ι]

noncomputable def coordSymbol (i : ι) (ξ : EuclideanSpace ℝ ι) : ℝ := (2*Real.pi*ξ i)^2
omit [Fintype ι] in
lemma coordSymbol_nonneg (i : ι) (ξ : EuclideanSpace ℝ ι) : 0 ≤ coordSymbol i ξ := sq_nonneg _
omit [Fintype ι] in
lemma coordSymbol_continuous (i : ι) : Continuous (coordSymbol i) := by
  unfold coordSymbol
  fun_prop

lemma symbol_single [DecidableEq ι] (i : ι) (η : ℝ≥0) :
    GaussianKernel.symbol (Pi.single i (2*η)) = fun ξ => (η:ℝ)*coordSymbol i ξ := by
  ext ξ
  simp only [GaussianKernel.symbol, coordSymbol, Pi.single_apply, apply_ite,
    NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

def Bound (D : Set (EuclideanSpace ℝ ι)) (hD : MeasurableSet D) (c : ℝ) : Prop :=
  ∀ v : ι → ℝ≥0, Real.exp (-(c/2) * ∑ i, (v i:ℝ)) ≤
    ‖compressedHeat D hD (GaussianKernel.symbol v)
      (GaussianKernel.symbol_continuous v).aestronglyMeasurable (GaussianKernel.symbol_nonneg v)‖

lemma exists_unit_of_bound {D : Set (EuclideanSpace ℝ ι)} {hD : MeasurableSet D} {c : ℝ}
    (h : Bound D hD c) :
    ∃ f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)), f ∈ supported D ∧ ‖f‖ = 1 := by
  have hb := h 0
  simp only [Pi.zero_apply, NNReal.coe_zero, Finset.sum_const_zero, mul_zero] at hb
  obtain ⟨f,hf,hn,_⟩ := exists_energy_lt_of_exp_le D hD _
    (GaussianKernel.symbol_continuous 0).aestronglyMeasurable
    (GaussianKernel.symbol_nonneg 0) (c := 0) (by simpa only [neg_zero] using hb) (ε := 1) (by norm_num)
  exact ⟨f,hf,hn⟩

lemma symbol_mean (η : ℝ) (hη : 0 ≤ η) (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i) :
    GaussianKernel.symbol (fun i => ⟨2*η*q i, mul_nonneg (mul_nonneg (by norm_num) hη) (hq i)⟩) =
      fun ξ => ∑ i, q i * (η*coordSymbol i ξ) := by
  ext ξ
  unfold GaussianKernel.symbol coordSymbol
  change (∑ i, (2*η*q i)*(2*Real.pi*ξ i)^2)/2 = _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma coord_mixture_energy_le [DecidableEq ι] (i : ι) (η : ℝ) (hη : 0 ≤ η)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1)
    (f g : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) :
    energy (fun ξ => η*coordSymbol i ξ) (mixture t ht.1 ht.2 f g) ≤
      t*energy (fun ξ => η*coordSymbol i ξ) f +
        (1-t)*energy (fun ξ => η*coordSymbol i ξ) g := by
  let ηn : ℝ≥0 := ⟨η,hη⟩
  have hh := mixture_diagonal_energy_le (Pi.single i (2*ηn)) t ht.1 ht.2 f g
  rw [symbol_single i ηn] at hh
  exact hh

lemma simultaneous_coordinate_energy {D : Set (EuclideanSpace ℝ ι)} {hD : MeasurableSet D}
    {c : ℝ} (hB : Bound D hD c) {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∃ f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)),
      f ∈ supported D ∧ ‖f‖ = 1 ∧ ∀ i, energy (fun ξ => η*coordSymbol i ξ) f < η*(c+ε) := by
  classical
  let F := {f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)) | f ∈ supported D ∧ ‖f‖ = 1}
  obtain ⟨f₀,hf₀,hn₀⟩ := exists_unit_of_bound hB
  let fzero : F := ⟨f₀,hf₀,hn₀⟩
  let : Nonempty F := ⟨fzero⟩
  let E : F → ι → ℝ := fun f i => energy (fun ξ => η*coordSymbol i ξ) f.val
  have hconv : ∀ f g : F, ∀ t ∈ Icc (0:ℝ) 1, ∃ h : F,
      ∀ i, E h i ≤ t*E f i+(1-t)*E g i := by
    intro f g t ht
    let m := mixture t ht.1 ht.2 f.val g.val
    have hm : ‖m‖=1 := by
      have hh := mixture_norm_sq t ht.1 ht.2 f.val g.val
      rw [f.property.2,g.property.2,one_pow] at hh
      change ‖m‖^2 = _ at hh
      nlinarith [norm_nonneg m]
    refine ⟨⟨m,mixture_supported D t ht.1 ht.2 f.val g.val f.property.1 g.property.1,hm⟩,?_⟩
    intro i
    exact coord_mixture_energy_le i η hη.le t ht f.val g.val
  have hweighted : ∀ q : ι → ℝ, (∀ i,0 ≤ q i) → ∀ δ > 0,
      ∃ f : F, ∑ i, q i*E f i < (η*c)*∑ i,q i+δ := by
    intro q hq δ hδ
    let S := ∑ i,q i
    have hSn : 0 ≤ S := Finset.sum_nonneg (fun i _ => hq i)
    by_cases hS : S=0
    · have hq0 : ∀ i,q i=0 := fun i =>
        (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hq j)).mp hS i (Finset.mem_univ i)
      refine ⟨fzero,?_⟩
      simpa only [hq0,zero_mul,Finset.sum_const_zero,mul_zero,zero_add] using hδ
    have hSp : 0 < S := lt_of_le_of_ne hSn (Ne.symm hS)
    let p : ι → ℝ := fun i => q i/S
    have hp : ∀ i,0 ≤ p i := fun i => div_nonneg (hq i) hSn
    have hpsum : ∑ i,p i=1 := by
      dsimp [p]
      rw [← Finset.sum_div]
      exact div_self hS
    let v : ι → ℝ≥0 := fun i => ⟨2*η*p i,mul_nonneg (mul_nonneg (by norm_num) hη.le) (hp i)⟩
    have hvsum : ∑ i,(v i:ℝ)=2*η := by
      change (∑ i,(2*η)*p i)=2*η
      rw [← Finset.mul_sum,hpsum,mul_one]
    have hv := hB v
    rw [hvsum] at hv
    have he : -(c/2)*(2*η)=-(η*c) := by ring
    rw [he] at hv
    obtain ⟨f,hf,hn,henergy⟩ := exists_energy_lt_of_exp_le D hD (GaussianKernel.symbol v)
      (GaussianKernel.symbol_continuous v).aestronglyMeasurable (GaussianKernel.symbol_nonneg v)
      hv (div_pos hδ hSp)
    have hmean := energy_mean_ge Finset.univ p (fun i ξ => η*coordSymbol i ξ)
      (fun i _ => hp i) hpsum
      (fun i _ => ((coordSymbol_continuous i).const_mul η).aestronglyMeasurable)
      (fun i _ ξ => mul_nonneg hη.le (coordSymbol_nonneg i ξ)) f
    have hve : GaussianKernel.symbol v = fun ξ => ∑ i,p i*(η*coordSymbol i ξ) :=
      symbol_mean η hη.le p hp
    rw [← hve] at hmean
    have hsum : ∑ i,q i*energy (fun ξ => η*coordSymbol i ξ) f =
        S*(∑ i,p i*energy (fun ξ => η*coordSymbol i ξ) f) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [p]
      field_simp
    refine ⟨⟨f,hf,hn⟩,?_⟩
    change (∑ i,q i*energy (fun ξ => η*coordSymbol i ξ) f) < (η*c)*S+δ
    rw [hsum]
    have hh := mul_lt_mul_of_pos_left (hmean.trans_lt henergy) hSp
    have hcancel : S*(η*c+δ/S)=(η*c)*S+δ := by field_simp
    exact hh.trans_eq hcancel
  obtain ⟨f,hf⟩ := EuclideanSteinitz.simultaneous_approx E (η*c) hconv hweighted (η*ε)
    (mul_pos hη hε)
  refine ⟨f.val,f.property.1,f.property.2,fun i => ?_⟩
  simpa only [mul_add] using hf i

end Diagonal
end HeatL2

end

section

open MeasureTheory Set Filter
open scoped NNReal Topology
namespace HeatL2.Diagonal
variable {ι : Type*} [Fintype ι]

lemma symbol_mono {v w : ι → ℝ≥0} (h : ∀ i,v i≤w i) (ξ : EuclideanSpace ℝ ι) :
    GaussianKernel.symbol v ξ ≤ GaussianKernel.symbol w ξ := by
  unfold GaussianKernel.symbol
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (h i) (sq_nonneg _)) (by norm_num)

lemma bound_of_positive {D : Set (EuclideanSpace ℝ ι)} {hD : MeasurableSet D} {c : ℝ}
    (h : ∀ v : ι → ℝ≥0, (∀ i,0<v i) → Real.exp (-(c/2)*∑ i,(v i:ℝ)) ≤
      ‖compressedHeat D hD (GaussianKernel.symbol v)
        (GaussianKernel.symbol_continuous v).aestronglyMeasurable (GaussianKernel.symbol_nonneg v)‖) :
    Bound D hD c := by
  intro v
  have ht : Tendsto (fun ε : ℝ => Real.exp (-(c/2)*∑ i,((v i:ℝ)+ε))) (𝓝[>] 0)
      (𝓝 (Real.exp (-(c/2)*∑ i,(v i:ℝ)))) := by
    have hh : Continuous (fun ε : ℝ => Real.exp (-(c/2)*∑ i,((v i:ℝ)+ε))) := by fun_prop
    simpa using (hh.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : 0<ε := hε
  let w : ι → ℝ≥0 := fun i => ⟨(v i:ℝ)+ε,by positivity⟩
  have hp := h w (fun i => by change 0<(v i:ℝ)+ε; positivity)
  exact hp.trans (compressed_norm_mono_symbol D hD _ _
    (GaussianKernel.symbol_continuous v).aestronglyMeasurable
    (GaussianKernel.symbol_continuous w).aestronglyMeasurable
    (GaussianKernel.symbol_nonneg v) (GaussianKernel.symbol_nonneg w)
    (symbol_mono (fun i => by change (v i:ℝ)≤(v i:ℝ)+ε; linarith)))

lemma Bound.mono_const {D : Set (EuclideanSpace ℝ ι)} {hD : MeasurableSet D} {c d : ℝ}
    (h : Bound D hD c) (hcd : c≤d) : Bound D hD d := by
  intro v
  exact (Real.exp_le_exp.mpr (by
    have hh : 0≤∑ i,(v i:ℝ) := Finset.sum_nonneg fun i _ => (v i).coe_nonneg
    nlinarith)).trans (h v)

end HeatL2.Diagonal

end

section

open Matrix MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace NNReal ENNReal Pointwise
namespace GaussianAR
open GaussianKernel HeatL2 GaussianTail
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma scaled_kernel_norm_of_survival {s : ℝ≥0} (hs : 0<s)
    (r : ι → ℝ) (hr : ∀ i,0<r i) (hr1 : ∀ i,r i<1)
    (w : ι → ℝ≥0) (hw : ∀ i,(w i:ℝ)=(1-(r i)^2)/r i)
    (D : Set (EuclideanSpace ℝ ι)) (hD : MeasurableSet D)
    [IsFiniteMeasure (volume.restrict D)] [IsFiniteMeasure (volume.restrict ((s:ℝ) • D))]
    (a b : ℝ) (hsurv : ∀ n : ℕ, Real.exp (-a-b*n) ≤
      (stdGaussian (EuclideanSpace ℝ (Fin (n+1)×ι))).real
        {x | ∀ t : Fin (n+1), matrixMap (evaluation r n t) x ∈ D}) :
    Real.exp (-b) / (∏ i,(Real.sqrt (r i))⁻¹) ≤
      ‖kernelOp (μ := volume.restrict ((s:ℝ) • D)) (kernel (fun i => s^2*w i))‖ := by
  have hρ : 0 < density (fun _ : ι => 1) 0 := density_pos _ (fun _ => by simp) _
  have hc : 0 < ∏ i,(Real.sqrt (r i))⁻¹ := Finset.prod_pos fun i _ =>
    inv_pos.mpr (Real.sqrt_pos.mpr (hr i))
  have hs' : 0<(s:ℝ) := hs
  apply norm_lower_of_pathMass_lower (kernel (fun i => s^2*w i)) (by positivity)
    (c := (s:ℝ)^(Fintype.card ι)*Real.exp (-a)/density (fun _ : ι => 1) 0) (by positivity)
  intro n
  rw [pathMass_scale hs w D hD n]
  have hn := (hsurv n).trans (survival_le_pathMass r hr hr1 w hw D hD n)
  have hex : Real.exp (-a-b*n)=Real.exp (-a)*(Real.exp (-b))^n := by
    rw [show -a-b*(n:ℝ)= -a+(-b)*n by ring,Real.exp_add,mul_comm (-b),Real.exp_nat_mul]
  rw [hex] at hn
  have hl : Real.exp (-a)/density (fun _ : ι => 1) 0 *
      (Real.exp (-b)/(∏ i,(Real.sqrt (r i))⁻¹))^n ≤ pathMass (μ := volume.restrict D) (kernel w) n := by
    apply (mul_le_mul_iff_left₀ (mul_pos hρ (pow_pos hc n))).mp
    convert hn using 1
    · calc
        _ = (Real.exp (-a)/density (fun _ : ι => 1) 0 * density (fun _ : ι => 1) 0) *
            ((Real.exp (-b))^n/(∏ i,(Real.sqrt (r i))⁻¹)^n * (∏ i,(Real.sqrt (r i))⁻¹)^n) := by
          rw [div_pow]; ring
        _ = _ := by rw [div_mul_cancel₀ _ hρ.ne',div_mul_cancel₀ _ (pow_ne_zero n hc.ne')]
    · ring
  simpa only [div_eq_mul_inv,mul_assoc] using
    mul_le_mul_of_nonneg_left hl (pow_nonneg hs'.le (Fintype.card ι))

lemma decay_sqrt_bound {q : ℝ} (_hq : 0 ≤ q) :
    (Real.sqrt ((1+q)⁻¹))⁻¹ ≤ Real.exp (q/2) := by
  rw [Real.sqrt_inv,inv_inv,Real.exp_half]
  exact Real.sqrt_le_sqrt (by linarith [Real.add_one_le_exp q])

lemma dilated_bound_of_survival {s : ℝ≥0} (hs : 0<s)
    (D : Set (EuclideanSpace ℝ ι)) (hD : MeasurableSet D)
    (hDs : MeasurableSet ((s:ℝ) • D))
    [IsFiniteMeasure (volume.restrict D)] [IsFiniteMeasure (volume.restrict ((s:ℝ) • D))]
    (B : ℝ) (hsurv : ∀ q : ι → ℝ, (∀ i,0<q i) → ∃ a : ℝ, ∀ n : ℕ,
      Real.exp (-a-B*(∑ i,q i)*n) ≤
      (stdGaussian (EuclideanSpace ℝ (Fin (n+1)×ι))).real
        {x | ∀ t : Fin (n+1),matrixMap (evaluation (fun i => (1+q i)⁻¹) n t) x ∈ D}) :
    HeatL2.Diagonal.Bound ((s:ℝ) • D) hDs ((2*B+1)/(s:ℝ)^2) := by
  apply HeatL2.Diagonal.bound_of_positive
  intro v hv
  have hs' : 0<(s:ℝ) := hs
  let q : ι → ℝ := fun i => (v i:ℝ)/(s:ℝ)^2
  have hq : ∀ i,0<q i := fun i => div_pos (hv i) (sq_pos_of_pos hs')
  let r : ι → ℝ := fun i => (1+q i)⁻¹
  have hr : ∀ i,0<r i := fun i => inv_pos.mpr (by linarith [hq i])
  have hr1 : ∀ i,r i<1 := fun i => (inv_lt_one₀ (by linarith [hq i])).mpr (by linarith [hq i])
  let w : ι → ℝ≥0 := fun i => ⟨(1-(r i)^2)/r i,div_nonneg (by nlinarith [hr i,hr1 i]) (hr i).le⟩
  have hw : ∀ i,0<w i := fun i => by change 0<(1-(r i)^2)/r i; exact div_pos (by nlinarith [hr i,hr1 i]) (hr i)
  have hvar : ∀ i,v i≤ s^2*w i := by
    intro i
    change (v i:ℝ)≤(s:ℝ)^2*((1-(r i)^2)/r i)
    have he : (1-(r i)^2)/r i=q i*(2+q i)/(1+q i) := by
      dsimp only [r]
      field_simp [ne_of_gt (show 0<1+q i by linarith [hq i])]
      ring
    rw [he]
    have hqq : q i ≤ q i*(2+q i)/(1+q i) := by
      apply (le_div_iff₀ (by linarith [hq i])).mpr
      nlinarith [hq i]
    have hh := mul_le_mul_of_nonneg_left hqq (sq_nonneg (s:ℝ))
    simpa only [q,mul_div_cancel₀ _ (ne_of_gt (sq_pos_of_pos hs'))] using hh
  obtain ⟨a,ha⟩ := hsurv q hq
  have hn := scaled_kernel_norm_of_survival hs r hr hr1 w (fun _ => rfl) D hD a
    (B*(∑ i,q i)) (by simpa only [mul_assoc] using ha)
  rw [kernel_norm_eq _ (fun i => mul_ne_zero (pow_ne_zero _ hs.ne') (ne_of_gt (hw i))) _ hDs] at hn
  have hc : ∏ i,(Real.sqrt (r i))⁻¹ ≤ Real.exp ((∑ i,q i)/2) := by
    calc
      _ ≤ ∏ i,Real.exp (q i/2) := Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ => decay_sqrt_bound (hq i).le)
      _ = _ := by rw [← Real.exp_sum]; congr 1; rw [Finset.sum_div]
  have hcp : 0<∏ i,(Real.sqrt (r i))⁻¹ := Finset.prod_pos fun i _ => by positivity
  have he : Real.exp (-(((2*B+1)/(s:ℝ)^2)/2)*(∑ i,(v i:ℝ))) =
      Real.exp (-(B*(∑ i,q i)))/Real.exp ((∑ i,q i)/2) := by
    rw [← Real.exp_sub]
    congr 1
    simp only [q,← Finset.sum_div]
    field_simp
    ring
  rw [he]
  exact (div_le_div_of_nonneg_left (Real.exp_pos _).le hcp hc).trans (hn.trans
    (compressed_norm_mono_symbol _ hDs _ _ (symbol_continuous v).aestronglyMeasurable
      (symbol_continuous (fun i => s^2*w i)).aestronglyMeasurable (symbol_nonneg v)
      (symbol_nonneg _) (HeatL2.Diagonal.symbol_mono hvar)))

end GaussianAR

end

end OAI
