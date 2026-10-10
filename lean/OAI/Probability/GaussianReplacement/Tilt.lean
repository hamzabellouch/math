import OAI.Probability.GaussianReplacement.KernelVolume

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory



lemma compProd_withDensity_fst {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) [IsProbabilityMeasure μ] (κ : Kernel A B) [IsMarkovKernel κ]
    (w : A×B → ℝ≥0∞) (hw : Measurable w)
    (h1 : ∀ᵐ a ∂μ, ∫⁻ b, w (a,b) ∂κ a = 1) :
    ((μ ⊗ₘ κ).withDensity w).fst = μ := by
  ext s hs
  rw [Measure.fst_apply hs, withDensity_apply _ (hs.preimage measurable_fst),
    ←lintegral_indicator (hs.preimage measurable_fst),
    Measure.lintegral_compProd (hw.indicator (hs.preimage measurable_fst))]
  calc
    _ = ∫⁻ a, s.indicator (fun _ => (1:ℝ≥0∞)) a ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [h1] with a ha
      by_cases has : a ∈ s
      · simpa only [Set.indicator_of_mem has, Set.mem_preimage, has,
          Set.indicator_of_mem] using ha
      · simp [Set.indicator_of_notMem, has]
    _ = μ s := by simp [lintegral_indicator hs]

section KernelTilt
variable {E : Type*} [NormedAddCommGroup E] [innerProductSpaceRealE : InnerProductSpace ℝ E]
  [finiteDimensionalRealE : FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [nontrivialE : Nontrivial E]



def reciprocalKernelScale {r : ℕ} (κ : Kernel (Fin r → E) E) (s : E)
    (A : Fin r → E) : ℝ≥0∞ := ∫⁻ t, ENNReal.ofReal (‖t-s‖⁻¹) ∂κ A

omit innerProductSpaceRealE finiteDimensionalRealE nontrivialE in
lemma measurable_reciprocalKernelScale {r : ℕ} (κ : Kernel (Fin r → E) E)
    [IsMarkovKernel κ] (s : E) : Measurable (reciprocalKernelScale κ s) := by
  exact (show Measurable (fun t : E => ENNReal.ofReal (‖t-s‖⁻¹)) by fun_prop).lintegral_kernel

lemma reciprocal_kernel_projection_moment {r q : ℕ}
    (hr : r ≤ Module.finrank ℝ E) (hd : Module.finrank ℝ E ≤ 8*r)
    (hq : 2*q ≤ r) (hmargin : 2 ≤ r-q)
    (κ : Kernel (Fin r → E) E) [IsMarkovKernel κ] (s : E)
    (hscale : ∀ᵐ A ∂Measure.pi (fun _ : Fin r => stdGaussian E),
      reciprocalKernelScale κ s A ≠ 0 ∧ reciprocalKernelScale κ s A ≠ ∞)
    (hsupport : ∀ᵐ z ∂(Measure.pi (fun _ : Fin r => stdGaussian E)) ⊗ₘ κ,
      z.2-s ≠ 0 ∧ z.2-s ∈ (rowSpan z.1)ᗮ)
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (hφ1 : ∫⁻ t, φ t = 1) :
    ∫⁻ x, (∫⁻ A, (∫⁻ t, φ ⟪t-s,x⟫ ∂κ A) / reciprocalKernelScale κ s A
      ∂Measure.pi (fun _ : Fin r => stdGaussian E))^q ∂stdGaussian E ≤
      ENNReal.ofReal (5*kernelSmallBallConstant)^q := by
  let γ := Measure.pi (fun _ : Fin r => stdGaussian E)
  let P := γ ⊗ₘ κ
  let a := reciprocalKernelScale κ s
  let w : (Fin r → E)×E → ℝ≥0∞ := fun z => ENNReal.ofReal (‖z.2-s‖⁻¹) / a z.1
  have ha : Measurable a := measurable_reciprocalKernelScale κ s
  have hw : Measurable w := by dsimp [w]; fun_prop
  have hmass : ∀ᵐ A ∂γ, ∫⁻ t, w (A,t) ∂κ A = 1 := by
    filter_upwards [hscale] with A hA
    dsimp [w]
    simp_rw [div_eq_mul_inv]
    rw [lintegral_mul_const _ (by fun_prop)]
    exact ENNReal.div_self hA.1 hA.2
  let P' := P.withDensity w
  have hfst : P'.fst = γ := compProd_withDensity_fst γ κ w hw hmass
  have : IsProbabilityMeasure P' := by
    have hp : IsProbabilityMeasure P'.fst := hfst ▸ inferInstance
    have : IsProbabilityMeasure (P'.map Prod.fst) := hp
    exact Measure.isProbabilityMeasure_of_map (μ:=P') measurable_fst.aemeasurable
  let D : (Fin r → E)×E → (Fin r → E)×E := fun z => (z.1,z.2-s)
  have hD : Measurable D := by dsimp [D]; fun_prop
  let Q := P'.map D
  have : IsProbabilityMeasure Q := inferInstance
  have hQfst : Q.fst = γ := by
    change (P'.map D).map Prod.fst = _
    rw [Measure.map_map measurable_fst hD]
    exact hfst
  have hQsup : ∀ᵐ z ∂Q, z.2 ≠ 0 ∧ z.2 ∈ (rowSpan z.1)ᗮ := by
    have hm : MeasurableSet {z : (Fin r → E)×E |
        z.2 ≠ 0 ∧ z.2 ∈ (rowSpan z.1)ᗮ} := by
      have he : {z : (Fin r → E)×E | z.2 ∈ (rowSpan z.1)ᗮ} =
          {z | rowProjectionL z.1 z.2 = 0} := by
        ext z
        simp only [Set.mem_ofPred_eq, rowProjectionL_eq, Submodule.starProjection_apply_eq_zero_iff]
      exact (measurableSet_eq_fun measurable_snd measurable_const).compl.inter
        (by
          change MeasurableSet {z : (Fin r → E)×E | z.2 ∈ (rowSpan z.1)ᗮ}
          rw [he]
          exact measurableSet_eq_fun (measurable_rowProjection_pair r) measurable_const)
    apply (ae_map_iff hD.aemeasurable hm).mpr
    exact (withDensity_absolutelyContinuous P w).ae_le hsupport
  have hmoment := kernel_normalized_projection_moment hr hd hq hmargin Q hQfst hQsup φ hφ hφ1
  have heq (x : E) : (∫⁻ z, ENNReal.ofReal ‖z.2‖ * φ ⟪z.2,x⟫ ∂Q) =
      ∫⁻ A, (∫⁻ t, φ ⟪t-s,x⟫ ∂κ A) / a A ∂γ := by
    rw [lintegral_map (by fun_prop) hD]
    rw [lintegral_withDensity_eq_lintegral_mul P hw (by dsimp [D]; fun_prop)]
    calc
      _ = ∫⁻ z, φ ⟪z.2-s,x⟫ / a z.1 ∂P := by
        apply lintegral_congr_ae
        filter_upwards [hsupport] with z hz
        change w z * (ENNReal.ofReal ‖z.2-s‖ * φ ⟪z.2-s,x⟫) = _
        dsimp [w]
        have hn : 0 < ‖z.2-s‖ := norm_pos_iff.mpr hz.1
        rw [ENNReal.ofReal_inv_of_pos hn]
        have hc := ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hn).ne' ENNReal.ofReal_ne_top
        rw [div_eq_mul_inv, div_eq_mul_inv]
        calc
          _ = ((ENNReal.ofReal ‖z.2-s‖)⁻¹ * ENNReal.ofReal ‖z.2-s‖) *
              (φ ⟪z.2-s,x⟫ * (a z.1)⁻¹) := by simp only [mul_assoc, mul_comm, mul_left_comm]
          _ = _ := by rw [hc, one_mul]
      _ = _ := by
        rw [Measure.lintegral_compProd (by fun_prop)]
        apply lintegral_congr
        intro A
        simp_rw [div_eq_mul_inv]
        rw [lintegral_mul_const _ (by fun_prop)]
  simpa only [heq] using hmoment

end KernelTilt





def negativeLogAbs (x : ℝ) : ℝ := max (-Real.log |x|) 0

lemma measurable_negativeLogAbs : Measurable negativeLogAbs := by
  unfold negativeLogAbs
  fun_prop

lemma negativeLogAbs_nonneg (x : ℝ) : 0 ≤ negativeLogAbs x := le_max_right _ _

lemma integrable_negativeLogAbs_gaussian :
    Integrable negativeLogAbs (gaussianReal 0 1) := by
  have hl : IntegrableOn Real.log (Set.Icc (-1) 1) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (-1:ℝ) ≤ 1)).mp
      intervalIntegral.intervalIntegrable_log'
  have hm : IntegrableOn negativeLogAbs (Set.Icc (-1) 1) volume := by
    have h := (show Integrable (-Real.log) (volume.restrict (Set.Icc (-1) 1)) from hl.neg).sup (integrable_const 0)
    have he : negativeLogAbs = (-Real.log ⊔ fun _ => 0) := by
      ext x
      simp [negativeLogAbs, Real.log_abs]
    rw [IntegrableOn, he]
    exact h
  have hi : Integrable ((Set.Icc (-1:ℝ) 1).indicator negativeLogAbs) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr hm
  have he : (Set.Icc (-1:ℝ) 1).indicator negativeLogAbs = negativeLogAbs := by
    funext x
    by_cases hx : x ∈ Set.Icc (-1:ℝ) 1
    · simp [hx]
    · have ha : 1 ≤ |x| := by
        simp only [Set.mem_Icc, not_and_or, not_le] at hx
        rcases hx with hx | hx
        · rw [abs_of_neg (by linarith)]
          linarith
        · exact (le_abs_self x).trans' hx.le
      have hlog := Real.log_nonneg ha
      rw [Set.indicator_of_notMem hx, negativeLogAbs, max_eq_right (neg_nonpos.mpr hlog)]
  rw [he] at hi
  exact hi.mono_measure gaussianReal_le_volume

def regularizedCauchyCross (r e x y : ℝ) : ℝ :=
  Real.log Real.pi + Real.log ((r*x)^2+(r*y)^2+e^2) -
    (1/2:ℝ)*Real.log ((r*x)^2+e^2)

lemma regularizedCauchyCross_upper {r e : ℝ} (hr : 0 ≤ r) (he : 0 < e)
    (x y : ℝ) (hx : x ≠ 0) :
    regularizedCauchyCross r e x y ≤
      Real.log (max r e) + Real.log Real.pi + x^2+y^2+negativeLogAbs x := by
  have ht : 0 < (r*x)^2+(r*y)^2+e^2 := by positivity
  have hD : 0 < (r*x)^2+e^2 := by positivity
  have hxy : 0 < 1+x^2+y^2 := by positivity
  have hlxy : Real.log (1+x^2+y^2) ≤ x^2+y^2 := by
    have h := Real.log_le_sub_one_of_pos hxy
    linarith
  have hex : 0 < |x| := abs_pos.mpr hx
  have hlogx : -Real.log |x| ≤ negativeLogAbs x := le_max_left _ _
  rcases le_total r e with hre | her
  · have hs : r^2 ≤ e^2 := (sq_le_sq₀ hr he.le).mpr hre
    have hu : (r*x)^2+(r*y)^2+e^2 ≤ e^2*(1+x^2+y^2) := by
      have h1 := mul_le_mul_of_nonneg_right hs (sq_nonneg x)
      have h2 := mul_le_mul_of_nonneg_right hs (sq_nonneg y)
      nlinarith
    have hlogT := Real.log_le_log ht hu
    rw [Real.log_mul (sq_pos_of_pos he).ne' hxy.ne', Real.log_pow] at hlogT
    have hlogD := Real.log_le_log (sq_pos_of_pos he)
      (show e^2 ≤ (r*x)^2+e^2 by nlinarith [sq_nonneg (r*x)])
    rw [Real.log_pow] at hlogD
    rw [max_eq_right hre]
    unfold regularizedCauchyCross
    norm_num only [Nat.cast_ofNat] at hlogT hlogD
    linarith [negativeLogAbs_nonneg x]
  · have hrp : 0 < r := he.trans_le her
    have hs : e^2 ≤ r^2 := (sq_le_sq₀ he.le hr).mpr her
    have hu : (r*x)^2+(r*y)^2+e^2 ≤ r^2*(1+x^2+y^2) := by nlinarith
    have hlogT := Real.log_le_log ht hu
    rw [Real.log_mul (sq_pos_of_pos hrp).ne' hxy.ne', Real.log_pow] at hlogT
    have hlogD := Real.log_le_log (mul_pos (sq_pos_of_pos hrp) (sq_pos_of_ne_zero hx))
      (show r^2*x^2 ≤ (r*x)^2+e^2 by nlinarith [sq_nonneg e])
    rw [Real.log_mul (sq_pos_of_pos hrp).ne' (sq_pos_of_ne_zero hx).ne',
      Real.log_pow, Real.log_pow, ←Real.log_abs x] at hlogD
    rw [max_eq_left her]
    unfold regularizedCauchyCross
    norm_num only [Nat.cast_ofNat] at hlogT hlogD
    linarith

lemma regularizedCauchyCross_lower {r e : ℝ} (he : 0 < e) (x y : ℝ) :
    Real.log Real.pi + Real.log e ≤ regularizedCauchyCross r e x y := by
  have hD : 0 < (r*x)^2+e^2 := by positivity
  have hDT := Real.log_le_log hD
    (show (r*x)^2+e^2 ≤ (r*x)^2+(r*y)^2+e^2 by nlinarith [sq_nonneg (r*y)])
  have heD := Real.log_le_log (sq_pos_of_pos he)
    (show e^2 ≤ (r*x)^2+e^2 by nlinarith [sq_nonneg (r*x)])
  rw [Real.log_pow] at heD
  unfold regularizedCauchyCross
  norm_num only [Nat.cast_ofNat] at heD
  linarith

lemma log_regularizedCauchyPDF (r e c x y : ℝ) (he : 0 < e) :
    -Real.log (cauchyPDFReal c ⟨Real.sqrt ((r*x)^2+e^2), Real.sqrt_nonneg _⟩ (c+r*y)) =
      regularizedCauchyCross r e x y := by
  have hD : 0 < (r*x)^2+e^2 := by positivity
  have hs : 0 < Real.sqrt ((r*x)^2+e^2) := Real.sqrt_pos.mpr hD
  have ht : 0 < (r*x)^2+(r*y)^2+e^2 := by positivity
  change -Real.log (Real.pi⁻¹ * Real.sqrt ((r*x)^2+e^2) *
    (((c+r*y)-c)^2 + (Real.sqrt ((r*x)^2+e^2))^2)⁻¹) = _
  unfold regularizedCauchyCross
  simp only [add_sub_cancel_left, Real.sq_sqrt hD.le]
  rw [Real.log_mul (mul_ne_zero (inv_ne_zero Real.pi_pos.ne') hs.ne') (inv_ne_zero (by positivity)),
    Real.log_mul (inv_ne_zero Real.pi_pos.ne') hs.ne', Real.log_inv, Real.log_inv,
    Real.log_sqrt hD.le]
  have heq : (r*y)^2+((r*x)^2+e^2) = (r*x)^2+(r*y)^2+e^2 := by ring
  rw [heq]
  ring

abbrev standardNormalPair : Measure (ℝ×ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 1)

def cauchyTiltConstant : ℝ := Real.log Real.pi + 2 +
  ∫ x, negativeLogAbs x ∂gaussianReal 0 1

lemma integrable_standardNormal_square : Integrable (fun x : ℝ => x^2) (gaussianReal 0 1) := by
  exact (memLp_id_gaussianReal (μ:=0) (v:=1) 2).integrable_sq

lemma integral_standardNormal_square : (∫ x : ℝ, x^2 ∂gaussianReal 0 1) = 1 := by
  have h := variance_id_gaussianReal (μ:=0) (v:=1)
  rw [variance_eq_integral (by fun_prop)] at h
  simpa using h

lemma integrable_regularizedCauchyCross {r e : ℝ} (hr : 0 ≤ r) (he : 0 < e) :
    Integrable (fun z : ℝ×ℝ => regularizedCauchyCross r e z.1 z.2) standardNormalPair := by
  have hsq1 := integrable_standardNormal_square.comp_fst (ν:=gaussianReal 0 1)
  have hsq2 := integrable_standardNormal_square.comp_snd (μ:=gaussianReal 0 1)
  have hn := integrable_negativeLogAbs_gaussian.comp_fst (ν:=gaussianReal 0 1)
  have hup : Integrable (fun z : ℝ×ℝ => Real.log (max r e)+Real.log Real.pi+
      z.1^2+z.2^2+negativeLogAbs z.1) standardNormalPair :=
    (((integrable_const _).add hsq1).add hsq2).add hn
  have hx : ∀ᵐ z : ℝ×ℝ ∂standardNormalPair, z.1 ≠ 0 := by
    have hx0 : ∀ᵐ x : ℝ ∂gaussianReal 0 1, x ≠ 0 := by
      apply ae_iff.mpr
      apply (gaussianReal_absolutelyContinuous 0 (by norm_num : (1:ℝ≥0) ≠ 0))
      simp
    exact Measure.quasiMeasurePreserving_fst.ae hx0
  exact integrable_of_le_of_le (by unfold regularizedCauchyCross; fun_prop)
    (ae_of_all _ fun z => regularizedCauchyCross_lower he z.1 z.2)
    (hx.mono fun z hz => regularizedCauchyCross_upper hr he z.1 z.2 hz)
    (integrable_const _) hup

lemma integral_regularizedCauchyCross {r e : ℝ} (hr : 0 ≤ r) (he : 0 < e) :
    (∫ z : ℝ×ℝ, regularizedCauchyCross r e z.1 z.2 ∂standardNormalPair) ≤
      Real.log (max r e) + cauchyTiltConstant := by
  have hsq1 := integrable_standardNormal_square.comp_fst (ν:=gaussianReal 0 1)
  have hsq2 := integrable_standardNormal_square.comp_snd (μ:=gaussianReal 0 1)
  have hn := integrable_negativeLogAbs_gaussian.comp_fst (ν:=gaussianReal 0 1)
  have hup : Integrable (fun z : ℝ×ℝ => Real.log (max r e)+Real.log Real.pi+
      z.1^2+z.2^2+negativeLogAbs z.1) standardNormalPair :=
    (((integrable_const _).add hsq1).add hsq2).add hn
  have hx : ∀ᵐ z : ℝ×ℝ ∂standardNormalPair, z.1 ≠ 0 := by
    have hx0 : ∀ᵐ x : ℝ ∂gaussianReal 0 1, x ≠ 0 := by
      apply ae_iff.mpr
      apply (gaussianReal_absolutelyContinuous 0 (by norm_num : (1:ℝ≥0) ≠ 0))
      simp
    exact Measure.quasiMeasurePreserving_fst.ae hx0
  have h := integral_mono_ae (integrable_regularizedCauchyCross hr he) hup
    (hx.mono fun z hz => regularizedCauchyCross_upper hr he z.1 z.2 hz)
  have heq : (∫ z : ℝ×ℝ, Real.log (max r e)+Real.log Real.pi+
      z.1^2+z.2^2+negativeLogAbs z.1 ∂standardNormalPair) =
      Real.log (max r e)+cauchyTiltConstant := by
    have hc : Integrable (fun _ : ℝ×ℝ => Real.log (max r e)+Real.log Real.pi)
        standardNormalPair := integrable_const _
    have h1 := integral_add ((hc.add hsq1).add hsq2) hn
    have h2 := integral_add (hc.add hsq1) hsq2
    have h3 := integral_add hc hsq1
    simp only [Pi.add_apply] at h1 h2 h3
    rw [h1, h2, h3]
    rw [integral_fun_fst (fun x : ℝ => x^2), integral_fun_snd (fun x : ℝ => x^2),
      integral_fun_fst negativeLogAbs, integral_const]
    simp only [probReal_univ, one_smul, integral_standardNormal_square]
    unfold cauchyTiltConstant
    ring
  exact h.trans_eq heq

lemma cauchyTiltConstant_pos : 0 < cauchyTiltConstant := by
  have h1 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have h2 : 0 ≤ ∫ x, negativeLogAbs x ∂gaussianReal 0 1 :=
    integral_nonneg (fun x => negativeLogAbs_nonneg x)
  unfold cauchyTiltConstant
  linarith




section CauchyVector
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma gaussian_inner_map_scaled (v : E) :
    (stdGaussian E).map (fun x => ⟪v,x⟫) =
      (gaussianReal 0 1).map (fun x => ‖v‖*x) := by
  have hi := IsGaussian.map_eq_gaussianReal (μ:=stdGaussian E) (innerSL ℝ v)
  rw [integral_strongDual_stdGaussian,variance_dual_stdGaussian] at hi
  have he : (fun x : ℝ => ‖v‖*x) = fun x => x*‖v‖ := by funext x; ring
  rw [he,gaussianReal_map_mul_const]
  have hv : (‖v‖^2).toNNReal = (⟨‖v‖^2,sq_nonneg _⟩ : ℝ≥0) := by
    exact Real.toNNReal_of_nonneg (sq_nonneg _)
  rw [innerSL_apply_norm] at hi
  change (stdGaussian E).map (fun x => ⟪v,x⟫) = gaussianReal 0 (‖v‖^2).toNNReal at hi
  rw [hi]
  congr 1 <;> simp only [mul_zero,mul_one,hv]
  ext
  rfl


lemma gaussian_pair_inner_map_scaled (v : E) :
    ((stdGaussian E).prod (stdGaussian E)).map
      (fun z : E×E => (⟪v,z.1⟫,⟪v,z.2⟫)) =
      standardNormalPair.map (fun z : ℝ×ℝ => (‖v‖*z.1,‖v‖*z.2)) := by
  change ((stdGaussian E).prod (stdGaussian E)).map (Prod.map (fun x => ⟪v,x⟫) (fun x => ⟪v,x⟫)) =
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map (Prod.map (fun x => ‖v‖*x) (fun x => ‖v‖*x))
  rw [←Measure.map_prod_map (stdGaussian E) (stdGaussian E) (by fun_prop) (by fun_prop),
    gaussian_inner_map_scaled,Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]

lemma gaussian_regularizedCross_integrable (v : E) {e : ℝ} (he : 0 < e) :
    Integrable (fun z : E×E => regularizedCauchyCross 1 e ⟪v,z.1⟫ ⟪v,z.2⟫)
      ((stdGaussian E).prod (stdGaussian E)) := by
  have hm : Measurable (fun z : ℝ×ℝ => regularizedCauchyCross 1 e z.1 z.2) := by
    unfold regularizedCauchyCross; fun_prop
  have hms : Measurable (fun z : ℝ×ℝ => (‖v‖*z.1,‖v‖*z.2)) := by fun_prop
  have hmv : Measurable (fun z : E×E => (⟪v,z.1⟫,⟪v,z.2⟫)) := by fun_prop
  have hi := integrable_regularizedCauchyCross (norm_nonneg v) he
  have hi' : Integrable (fun z : ℝ×ℝ => regularizedCauchyCross 1 e (‖v‖*z.1) (‖v‖*z.2))
      standardNormalPair := by simpa only [regularizedCauchyCross,one_mul] using hi
  have hmap : Integrable (fun z : ℝ×ℝ => regularizedCauchyCross 1 e z.1 z.2)
      (standardNormalPair.map (fun z : ℝ×ℝ => (‖v‖*z.1,‖v‖*z.2))) :=
    (integrable_map_measure hm.aestronglyMeasurable hms.aemeasurable).mpr hi'
  rw [←gaussian_pair_inner_map_scaled v] at hmap
  exact (integrable_map_measure hm.aestronglyMeasurable hmv.aemeasurable).mp hmap

lemma gaussian_regularizedCross_integral (v : E) {e : ℝ} (he : 0 < e) :
    (∫ z : E×E, regularizedCauchyCross 1 e ⟪v,z.1⟫ ⟪v,z.2⟫
      ∂(stdGaussian E).prod (stdGaussian E)) ≤
      Real.log (max ‖v‖ e) + cauchyTiltConstant := by
  have hm : Measurable (fun z : ℝ×ℝ => regularizedCauchyCross 1 e z.1 z.2) := by
    unfold regularizedCauchyCross; fun_prop
  rw [←integral_map (by fun_prop : AEMeasurable (fun z : E×E => (⟪v,z.1⟫,⟪v,z.2⟫)) _)
    hm.aestronglyMeasurable,gaussian_pair_inner_map_scaled,
    integral_map (by fun_prop) hm.aestronglyMeasurable]
  simpa only [regularizedCauchyCross,one_mul] using integral_regularizedCauchyCross (norm_nonneg v) he

end CauchyVector



end CurrentProjection

end

end OAI
