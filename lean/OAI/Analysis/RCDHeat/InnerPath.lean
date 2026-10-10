import Mathlib
import OAI.Analysis.RCDHeat.FisherLimit
import OAI.Analysis.RCDHeat.HopfTransport

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: InnerPath, HeatHopfPair, HeatHopfActual, HeatKuwada. -/



namespace RegularPointCoordinates

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
 theorem inner_lipschitzOn {s : Set ℝ} {F G : ℝ → E} {K L B C : ℝ≥0}
    (hF : LipschitzOnWith K F s) (hG : LipschitzOnWith L G s)
    (hB : ∀t ∈ s, ‖F t‖ ≤ B) (hC : ∀t ∈ s, ‖G t‖ ≤ C) :
    LipschitzOnWith (K*C+B*L) (fun t => inner ℝ (F t) (G t)) s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro r hr t ht
  rw [Real.dist_eq]
  have he : inner ℝ (F r) (G r)-inner ℝ (F t) (G t) =
      inner ℝ (F r-F t) (G r)+inner ℝ (F t) (G r-G t) := by
    rw [inner_sub_left,inner_sub_right]
    ring
  rw [he]
  calc
    _ ≤ |inner ℝ (F r-F t) (G r)|+|inner ℝ (F t) (G r-G t)| := abs_add_le _ _
    _ ≤ ‖F r-F t‖*‖G r‖+‖F t‖*‖G r-G t‖ := add_le_add
      (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ ((K:ℝ)*dist r t)*C+(B:ℝ)*((L:ℝ)*dist r t) := add_le_add
      (mul_le_mul (by simpa only [dist_eq_norm] using hF.dist_le_mul r hr t ht)
        (hC r hr) (norm_nonneg _) (by positivity))
      (mul_le_mul (hB t ht) (by simpa only [dist_eq_norm] using hG.dist_le_mul r hr t ht)
        (norm_nonneg _) B.coe_nonneg)
    _ = _ := by simp only [NNReal.coe_add,NNReal.coe_mul]; ring

 theorem lipschitzOn_inner_of_lipschitzOn {a b : ℝ} {F G : ℝ → E} {K L : ℝ≥0}
    (hF : LipschitzOnWith K F (Icc a b)) (hG : LipschitzOnWith L G (Icc a b)) :
    ∃ C : ℝ≥0, LipschitzOnWith C (fun t => inner ℝ (F t) (G t)) (Icc a b) := by
  obtain ⟨B,hB⟩ := (isCompact_Icc.image_of_continuousOn hF.continuousOn).isBounded.exists_norm_le
  obtain ⟨C,hC⟩ := (isCompact_Icc.image_of_continuousOn hG.continuousOn).isBounded.exists_norm_le
  let B' : ℝ≥0 := ⟨max 0 B,le_max_left _ _⟩
  let C' : ℝ≥0 := ⟨max 0 C,le_max_left _ _⟩
  exact ⟨K*C'+B'*L,inner_lipschitzOn hF hG
    (fun t ht => (hB _ (mem_image_of_mem F ht)).trans (le_max_right _ _))
    (fun t ht => (hC _ (mem_image_of_mem G ht)).trans (le_max_right _ _))⟩

 theorem sub_le_integral_of_ae_deriv_le {A H : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hA : AbsolutelyContinuousOnInterval A a b) (hH : IntervalIntegrable H volume a b)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo a b → deriv A t ≤ H t) :
    A b-A a ≤ ∫t in a..b, H t := by
  rw [← hA.integral_deriv_eq_sub]
  apply intervalIntegral.integral_mono_ae_restrict hab hA.intervalIntegrable_deriv hH
  rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := (volume : Measure ℝ)))]
  exact (ae_restrict_iff' measurableSet_Ioo).mpr hd
end

 
section
open Set Metric Filter MeasureTheory
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
omit [ProperSpace X] in
 theorem SobolevSpace.ofLipschitzCompact_energy_le [IsFiniteMeasureOnCompacts μ] {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hs : HasCompactSupport f) {S : Set X}
    (hS : MeasurableSet S) (hSf : μ S ≠ ∞) (hsS : tsupport f ⊆ S) :
    SobolevSpace.energy μ hQ (SobolevSpace.ofLipschitzCompact μ hQ hf hs) ≤
      (L:ℝ)^2*(μ S).toReal/2 := by
  have hb : slopeEnergy μ f ≤ (2 : ℝ≥0∞)⁻¹*((L:ℝ≥0∞)^2*μ S) := by
    apply mul_le_mul_right
    calc
      _ ≤ ∫⁻ x, S.indicator (fun _ => (L:ℝ≥0∞)^2) x ∂μ := by
        apply lintegral_mono
        intro x
        by_cases hx : x ∈ S
        · simp only [indicator_of_mem hx]
          exact pow_le_pow_left₀ (by positivity) (localSlope_le_of_lipschitz hf x) 2
        · simp only [indicator_of_notMem hx]
          rw [localSlope_eq_zero_of_notMem_tsupport (fun ht => hx (hsS ht)), zero_pow (by decide)]
      _ = _ := lintegral_indicator_const hS _
  have hc := (cheegerEnergy_le_slopeEnergy μ (hf.continuous.memLp_of_hasCompactSupport hs) hf).trans hb
  have he : energyLp μ (SobolevSpace.toLp μ hQ (SobolevSpace.ofLipschitzCompact μ hQ hf hs)) =
      cheegerEnergy μ f := cheegerEnergy_congr_ae μ (SobolevSpace.ofLipschitzCompact_coe μ hQ hf hs)
  unfold SobolevSpace.energy
  rw [he]
  have ht : (2 : ℝ≥0∞)⁻¹*((L:ℝ≥0∞)^2*μ S) ≠ ∞ := by finiteness
  have hh := ENNReal.toReal_mono ht hc
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_pow,
    ENNReal.coe_toReal,ENNReal.toReal_ofNat,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using hh

variable [μ.Regular]
 theorem heatShift_hasDerivAt (f : Lp ℝ 2 μ) {σ t : ℝ} (ht : 0 < σ+t) :
    HasDerivAt (fun s => heatAt μ hQ (σ+s) f) (-heatGeneratorAt μ hQ (σ+t) f) t := by
  simpa only [Function.comp_def,Pi.add_apply,id_eq,zero_add,one_smul,smul_eq_mul,mul_one] using
    (heatAt_hasDerivAt μ hQ (σ+t) ht f).scomp t
      ((hasDerivAt_const t σ).add (hasDerivAt_id t))
 theorem heatShift_lipschitzOn (f : Lp ℝ 2 μ) {σ a b : ℝ} (ha : 0 < σ+a) :
    ∃ C : ℝ≥0, LipschitzOnWith C (fun t => heatAt μ hQ (σ+t) f) (Icc a b) := by
  let C : ℝ≥0 := ⟨2*(1+1/(σ+a))*‖f‖,by positivity⟩
  refine ⟨C,(convex_Icc a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t ht => (heatShift_hasDerivAt μ hQ f (by linarith [ht.1])).hasDerivWithinAt) ?_⟩
  intro t ht
  change ‖-heatGeneratorAt μ hQ (σ+t) f‖ ≤ (C:ℝ)
  rw [norm_neg]
  exact (heatGeneratorAt μ hQ (σ+t)).le_of_opNorm_le
    (heatGeneratorAt_norm_le_of_ge μ hQ (σ+a) ha (σ+t) (by linarith [ht.1])) f

omit [ProperSpace X] [μ.Regular] in
 theorem hj_inner_bound (F D : Lp ℝ 2 μ) (g : SobolevSpace μ hQ)
    (hF : 0 ≤ F) (C : ℝ≥0) (hFC : ∀ᵐ x ∂μ, |F x| ≤ C)
    (hD : ∀ᵐ x ∂μ, D x+SobolevSpace.minimalSlope μ hQ g x^2/2 ≤ 0) :
    inner ℝ F D ≤ -(∫x, |F x| * SobolevSpace.minimalSlope μ hQ g x^2 ∂μ)/2 := by
  let G := SobolevSpace.minimalSlope μ hQ g
  have hs : Integrable (fun x => G x^2) μ := by
    simpa only [Real.norm_eq_abs,sq_abs] using
      (Lp.memLp G).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
  have hi : Integrable (fun x => |F x| * G x^2) μ := by
    apply (hs.const_mul (C:ℝ)).mono'
      ((continuous_abs.comp_aestronglyMeasurable (Lp.aestronglyMeasurable F)).mul
        ((Lp.aestronglyMeasurable G).pow 2))
    filter_upwards [hFC] with x hx
    change |(|F x| * G x^2)| ≤ (C:ℝ)*G x^2
    rw [abs_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right hx (sq_nonneg _)
  rw [L2.inner_def]
  simp only [Real.inner_apply]
  calc
    _ ≤ ∫x, -(|F x| * G x^2)/2 ∂μ := by
      apply integral_mono_ae ((Lp.memLp F).integrable_mul (Lp.memLp D)) (hi.neg.div_const 2)
      filter_upwards [(Lp.coeFn_nonneg _).mpr hF,hD] with x hFx hDx
      change F x*D x ≤ -(|F x| * G x^2)/2
      rw [abs_of_nonneg hFx]
      change D x+G x^2/2 ≤ 0 at hDx
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hFx hDx]
    _ = _ := by rw [integral_div,integral_neg]

 theorem heat_hj_pair_bound (f : Lp ℝ 2 μ) (hf : 0 ≤ f) (C : ℝ≥0)
    (hfC : ∀ᵐ x ∂μ, |f x| ≤ C) {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε)
    (g : SobolevSpace μ hQ) (D : Lp ℝ 2 μ)
    (hD : ∀ᵐ x ∂μ, D x+SobolevSpace.minimalSlope μ hQ g x^2/2 ≤ 0) :
    inner ℝ (-heatGeneratorAt μ hQ t f) (SobolevSpace.toLp μ hQ g)+
      inner ℝ (heatAt μ hQ t f) D ≤
      regularizedFisher μ hQ hε f t/2+ε*SobolevSpace.energy μ hQ g := by
  have hFC := heatAt_abs_le_const μ hQ t C f hfC
  have hI := hj_inner_bound μ hQ (heatAt μ hQ t f) D g
    (heatAt_nonneg μ hQ t f hf) C hFC hD
  have hY := energyForm_weighted_young μ hQ (heatSobolev μ hQ t ht f) g hε C
    (by simpa only [heatSobolev_toLp] using hFC)
  rw [heatSobolev_toLp,← regularizedFisher_eq_integral μ hQ hε f t ht] at hY
  rw [heatGeneratorAt_of_pos μ hQ t ht,inner_neg_left,← heatGenerator_form]
  linarith [neg_le_abs (energyForm μ hQ (heatSobolev μ hQ t ht f) g)]

variable {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ) (hgeo : IsGeodesicSpace X)
  (p : X) (R : ℝ) (h0 : ∀x, R < dist p x → φ x = 0) {a b σ : ℝ}
  (ha : 0 < a) (hab : a ≤ b)
 theorem hopfPathSobolev_energy_le (t : ℝ) :
    SobolevSpace.energy μ hQ (hopfPathSobolev μ hQ hφ hgeo p R h0 ha hab t) ≤
      (L:ℝ)^2*(μ (closedBall p (R+2*b*(L:ℝ)))).toReal/2 := by
  apply SobolevSpace.ofLipschitzCompact_energy_le μ hQ _ _ measurableSet_closedBall
    ((isCompact_closedBall _ _).measure_lt_top.ne)
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  by_contra hn
  apply hx
  exact hopfPath_zero_outside hφ p R h0 ha hab
    (by simpa only [mem_closedBall,not_le,dist_comm] using hn) t

variable [SigmaFinite μ]
 theorem heat_hopf_regularized_pair (f : Lp ℝ 2 μ) (hf : 0 ≤ f) (C : ℝ≥0)
    (hfC : ∀ᵐ x ∂μ, |f x| ≤ C) (hσ : 0 < σ+a) {ε : ℝ} (hε : 0 < ε) :
    inner ℝ (heatAt μ hQ (σ+b) f) (SobolevSpace.toLp μ hQ
      (hopfPathSobolev μ hQ hφ hgeo p R h0 ha hab b)) -
    inner ℝ (heatAt μ hQ (σ+a) f) (SobolevSpace.toLp μ hQ
      (hopfPathSobolev μ hQ hφ hgeo p R h0 ha hab a)) ≤
      (integralPotential μ (regularizedEntropy ε) (heatAt μ hQ (σ+a) f)-
        integralPotential μ (regularizedEntropy ε) (heatAt μ hQ (σ+b) f))/2+
      ε*((L:ℝ)^2*(μ (closedBall p (R+2*b*(L:ℝ)))).toReal/2)*(b-a) := by
  let G := hopfPathSobolev μ hQ hφ hgeo p R h0 ha hab
  let A := fun t => inner ℝ (heatAt μ hQ (σ+t) f) (SobolevSpace.toLp μ hQ (G t))
  let B := (L:ℝ)^2*(μ (closedBall p (R+2*b*(L:ℝ)))).toReal/2
  obtain ⟨K,hK⟩ := heatShift_lipschitzOn μ hQ f (b := b) hσ
  obtain ⟨J,hJ⟩ := hopfPathSobolev_lipschitz μ hQ hφ hgeo p R h0 ha hab
  obtain ⟨M,hM⟩ := lipschitzOn_inner_of_lipschitzOn hK hJ.lipschitzOnWith
  have hAC : AbsolutelyContinuousOnInterval A a b := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hab] using hM
  have hInt : IntervalIntegrable (fun t => regularizedFisher μ hQ hε f (σ+t)) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    exact (heatDissipation_continuousOn μ hQ (regularizedLog_lipschitz hε)
      (regularizedLog_zero ε) f).comp (continuous_const.add continuous_id).continuousOn
      (fun t ht => by change 0 < σ+t; linarith [ht.1])
  have hder : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo a b →
      deriv A t ≤ regularizedFisher μ hQ hε f (σ+t)/2+ε*B := by
    filter_upwards [hopfPathSobolev_ae_hasDerivAt_hj μ hQ hφ hgeo p R h0 ha hab] with t ht htI
    obtain ⟨D,hD,hHJ⟩ := ht
    have hpos : 0 < σ+t := by linarith [htI.1]
    have hd := (heatShift_hasDerivAt μ hQ f hpos).inner ℝ hD
    have he := hd.deriv
    change deriv A t = _ at he
    rw [he]
    have hb := heat_hj_pair_bound μ hQ f hf C hfC hpos hε (G t) D (hHJ htI)
    have hE := hopfPathSobolev_energy_le μ hQ hφ hgeo p R h0 ha hab t
    rw [add_comm]
    exact hb.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hE hε.le))
  have hi := sub_le_integral_of_ae_deriv_le hab hAC
    ((hInt.div_const 2).add intervalIntegrable_const) hder
  rw [intervalIntegral.integral_add (hInt.div_const 2) intervalIntegrable_const,
    intervalIntegral.integral_div,intervalIntegral.integral_comp_add_left,
    heatAt_regularizedEntropy_dissipation μ hQ hε f (σ+a) (σ+b) hσ (by linarith),
    intervalIntegral.integral_const,smul_eq_mul] at hi
  simpa only [mul_comm (b-a)] using hi

 theorem heat_hopf_entropy_pair (f : Lp ℝ 2 μ) (hf : 0 ≤ f) (C : ℝ≥0)
    (hfC : ∀ᵐ x ∂μ, |f x| ≤ C) (hσ : 0 < σ+a)
    (hAi : Integrable (heatAt μ hQ (σ+a) f) μ) (hBi : Integrable (heatAt μ hQ (σ+b) f) μ)
    (hAe : Integrable (fun x => heatAt μ hQ (σ+a) f x*Real.log (heatAt μ hQ (σ+a) f x)) μ)
    (hBe : Integrable (fun x => heatAt μ hQ (σ+b) f x*Real.log (heatAt μ hQ (σ+b) f x)) μ)
    (hm : (∫x, heatAt μ hQ (σ+a) f x ∂μ) = ∫x, heatAt μ hQ (σ+b) f x ∂μ) :
    inner ℝ (heatAt μ hQ (σ+b) f) (SobolevSpace.toLp μ hQ
      (hopfPathSobolev μ hQ hφ hgeo p R h0 ha hab b)) -
    inner ℝ (heatAt μ hQ (σ+a) f) (SobolevSpace.toLp μ hQ
      (hopfPathSobolev μ hQ hφ hgeo p R h0 ha hab a)) ≤
      ((∫x, heatAt μ hQ (σ+a) f x*Real.log (heatAt μ hQ (σ+a) f x) ∂μ)-
        ∫x, heatAt μ hQ (σ+b) f x*Real.log (heatAt μ hQ (σ+b) f x) ∂μ)/2 := by
  have he := integral_normalizedEntropy_sub_tendsto μ (heatAt μ hQ (σ+a) f) (heatAt μ hQ (σ+b) f)
    (heatAt_nonneg μ hQ (σ+a) f hf) (heatAt_nonneg μ hQ (σ+b) f hf) hAi hBi hAe hBe hm
  have hz : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hl := (he.div_const 2).add ((hz.mul_const
    ((L:ℝ)^2*(μ (closedBall p (R+2*b*(L:ℝ)))).toReal/2)).mul_const (b-a))
  simp only [zero_mul,add_zero] at hl
  apply ge_of_tendsto hl
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact heat_hopf_regularized_pair μ hQ hφ hgeo p R h0 ha hab f hf C hfC hσ hε
end

 
section
open Set Metric Filter MeasureTheory
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ) (hgeo : IsGeodesicSpace X)
  (p : X) (R : ℝ) (h0 : ∀x, R < dist p x → φ x = 0)
include hφ h0
omit [MeasurableSpace X] [BorelSpace X] in
 theorem hopfLax_hasCompactSupport {t : ℝ} (ht : 0 < t) : HasCompactSupport (hopfLax φ t) := by
  simpa only [hopfPath_eq (show t ∈ Icc t t from ⟨le_rfl,le_rfl⟩)] using
    hopfPath_hasCompactSupport hφ p R h0 ht (le_refl t) t
include hgeo
 theorem hopfLax_integrable_mul (F : Lp ℝ 2 μ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x => hopfLax φ t x*F x) μ :=
  (show MemLp (hopfLax φ t) 2 μ from (hopfLax_lipschitz hφ hgeo ht).continuous.memLp_of_hasCompactSupport
    (hopfLax_hasCompactSupport hφ p R h0 ht)).integrable_mul (Lp.memLp F)
 theorem inner_hopfPathSobolev (F : Lp ℝ 2 μ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {t : ℝ} (ht : t ∈ Icc a b) :
    inner ℝ F (SobolevSpace.toLp μ hQ (hopfPathSobolev μ hQ hφ hgeo p R h0 ha hab t)) =
      ∫x, hopfLax φ t x*F x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hopfPathSobolev_coe μ hQ hφ hgeo p R h0 ha hab t] with x hx
  rw [Real.inner_apply,hx,hopfPath_eq ht,mul_comm]

variable [SigmaFinite μ]
 theorem heat_hopf_entropy_dual (f : Lp ℝ 2 μ) (hf : 0 ≤ f) (C : ℝ≥0)
    (hfC : ∀ᵐ x ∂μ, |f x| ≤ C) {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (hsi : Integrable (heatAt μ hQ s f) μ) (hti : Integrable (heatAt μ hQ t f) μ)
    (hse : Integrable (fun x => heatAt μ hQ s f x*Real.log (heatAt μ hQ s f x)) μ)
    (hte : Integrable (fun x => heatAt μ hQ t f x*Real.log (heatAt μ hQ t f x)) μ)
    (hm : (∫x, heatAt μ hQ s f x ∂μ) = ∫x, heatAt μ hQ t f x ∂μ) :
    (∫x, hopfLax φ (t-s) x*heatAt μ hQ t f x ∂μ) - (∫x, φ x*heatAt μ hQ s f x ∂μ) ≤
      ((∫x, heatAt μ hQ s f x*Real.log (heatAt μ hQ s f x) ∂μ)-
        ∫x, heatAt μ hQ t f x*Real.log (heatAt μ hQ t f x) ∂μ)/2 := by
  have hφS : HasCompactSupport φ := by
    apply HasCompactSupport.intro (isCompact_closedBall p R)
    intro x hx
    exact h0 x (by simpa only [mem_closedBall,not_le,dist_comm] using hx)
  have hφi : Integrable (fun x => φ x*heatAt μ hQ s f x) μ :=
    (show MemLp φ 2 μ from hφ.continuous.memLp_of_hasCompactSupport hφS).integrable_mul (Lp.memLp _)
  have hs0 := (Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ hQ s f hf)
  have ht0 := (Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ hQ t f hf)
  have hpoint (η : ℝ) (hη : 0 < η) :
      (∫x, hopfLax φ (t-s) x*heatAt μ hQ t f x ∂μ) - (∫x, φ x*heatAt μ hQ s f x ∂μ) ≤
        ((∫x, heatAt μ hQ s f x*Real.log (heatAt μ hQ s f x) ∂μ)-
          ∫x, heatAt μ hQ t f x*Real.log (heatAt μ hQ t f x) ∂μ)/2+
        η*((L:ℝ)^2/2)*(∫x, heatAt μ hQ t f x ∂μ) := by
    have hle : η ≤ η+(t-s) := by linarith
    have he1 : s-η+η = s := by ring
    have he2 : s-η+(η+(t-s)) = t := by ring
    have hh := heat_hopf_entropy_pair μ hQ hφ hgeo p R h0 hη hle f hf C hfC
      (σ := s-η) (by rwa [he1]) (by rwa [he1]) (by rwa [he2])
      (by rwa [he1]) (by rwa [he2]) (by rwa [he1,he2])
    rw [he1,he2,inner_hopfPathSobolev μ hQ hφ hgeo p R h0 _ hη hle ⟨hle,le_rfl⟩,
      inner_hopfPathSobolev μ hQ hφ hgeo p R h0 _ hη hle ⟨le_rfl,hle⟩] at hh
    have hi1 := hopfLax_integrable_mul μ hφ hgeo p R h0 (heatAt μ hQ t f) (sub_pos.mpr hst)
    have hi2 := hopfLax_integrable_mul μ hφ hgeo p R h0 (heatAt μ hQ t f) (by linarith : 0 < η+(t-s))
    have hi3 := hopfLax_integrable_mul μ hφ hgeo p R h0 (heatAt μ hQ s f) hη
    have hu : (∫x, hopfLax φ (t-s) x*heatAt μ hQ t f x ∂μ) ≤
        (∫x, hopfLax φ (η+(t-s)) x*heatAt μ hQ t f x ∂μ)+
          η*((L:ℝ)^2/2)*(∫x, heatAt μ hQ t f x ∂μ) := by
      rw [← integral_const_mul,← integral_add hi2 (hti.const_mul _)]
      apply integral_mono_ae hi1 (hi2.add (hti.const_mul _))
      filter_upwards [ht0] with x hx
      have hb := hopfLax_time_difference_sharp hφ hgeo (sub_pos.mpr hst)
        (by linarith : 0 < η+(t-s)) x
      have he : |(η+(t-s))-(t-s)| = η := by rw [add_sub_cancel_right,abs_of_pos hη]
      rw [he] at hb
      have hp := (abs_le.mp hb).1
      change hopfLax φ (t-s) x*heatAt μ hQ t f x ≤
        hopfLax φ (η+(t-s)) x*heatAt μ hQ t f x+η*((L:ℝ)^2/2)*heatAt μ hQ t f x
      have hm := mul_le_mul_of_nonneg_right hp hx
      nlinarith only [hm]
    have hv : (∫x, hopfLax φ η x*heatAt μ hQ s f x ∂μ) ≤
        (∫x, φ x*heatAt μ hQ s f x ∂μ) := by
      apply integral_mono_ae hi3 hφi
      filter_upwards [hs0] with x hx
      exact mul_le_mul_of_nonneg_right (hopfLax_bounds hφ hη x).2 hx
    linarith
  have hz : Tendsto (fun η : ℝ => η) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have he := ((tendsto_const_nhds (x :=
    ((∫x, heatAt μ hQ s f x*Real.log (heatAt μ hQ s f x) ∂μ)-
      ∫x, heatAt μ hQ t f x*Real.log (heatAt μ hQ t f x) ∂μ)/2)).add ((hz.mul_const ((L:ℝ)^2/2)).mul_const
    (∫x, heatAt μ hQ t f x ∂μ)))
  simp only [zero_mul,add_zero] at he
  apply ge_of_tendsto he
  filter_upwards [self_mem_nhdsWithin] with η hη
  exact hpoint η hη
end

 
open Set Metric Filter MeasureTheory
open scoped Topology ENNReal NNReal BoundedContinuousFunction
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
 theorem transportCost_le_of_scaled (π : Measure (X×X)) {τ A : ℝ} (hτ : 0 < τ)
    (h : (∫⁻xy, ENNReal.ofReal (dist xy.1 xy.2^2/(2*τ)) ∂π) ≤ ENNReal.ofReal A) :
    transportCost π ≤ ENNReal.ofReal (2*τ*A) := by
  have hc : Measurable (fun xy : X×X => ENNReal.ofReal (dist xy.1 xy.2^2/(2*τ))) :=
    (((continuous_fst.dist continuous_snd).pow 2).div_const _).measurable.ennreal_ofReal
  calc
    transportCost π = ENNReal.ofReal (2*τ)*
        (∫⁻xy, ENNReal.ofReal (dist xy.1 xy.2^2/(2*τ)) ∂π) := by
      rw [← lintegral_const_mul _ hc]
      apply lintegral_congr
      intro xy
      rw [← ENNReal.ofReal_pow dist_nonneg,← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*τ)]
      congr 1
      field_simp
    _ ≤ ENNReal.ofReal (2*τ)*ENNReal.ofReal A := mul_le_mul' le_rfl h
    _ = ENNReal.ofReal (2*τ*A) := (ENNReal.ofReal_mul (by positivity : 0 ≤ 2*τ)).symm

variable (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
 theorem integral_heatMeasure (f : Lp ℝ 2 μ) (hf : 0 ≤ f) (t : ℝ) (φ : X → ℝ) :
    (∫x, φ x ∂heatMeasure μ hQ t f) = ∫x, φ x*heatAt μ hQ t f x ∂μ := by
  rw [heatMeasure,integral_withDensity_eq_integral_toReal_smul₀
    ((Lp.aestronglyMeasurable (heatAt μ hQ t f)).aemeasurable.ennreal_ofReal)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [(Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ hQ t f hf)] with x hx
  rw [ENNReal.toReal_ofReal hx,smul_eq_mul,mul_comm]

variable [SigmaFinite μ]
 theorem heat_coupling_entropy (hgeo : IsGeodesicSpace X) (p : X) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 μ) (hf0 : 0 ≤ f) (hfi : Integrable f μ)
    (hfm : (∫x, f x ∂μ) = 1) {r : ℝ} (hfr : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r)
    (C : ℝ≥0) (hfC : ∀ᵐ x ∂μ, |f x| ≤ C) {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    ∃ π : Measure (X×X), IsProbabilityMeasure π ∧
      π.map Prod.fst = heatMeasure μ hQ s f ∧ π.map Prod.snd = heatMeasure μ hQ t f ∧
      transportCost π ≤ ENNReal.ofReal ((t-s)*
        ((∫x, heatAt μ hQ s f x*Real.log (heatAt μ hQ s f x) ∂μ)-
          ∫x, heatAt μ hQ t f x*Real.log (heatAt μ hQ t f x) ∂μ)) := by
  let := heatMeasure_probability μ hQ p hA hB hvol f hf0 hfi hfm hs.le
  let := heatMeasure_probability μ hQ p hA hB hvol f hf0 hfi hfm (hs.le.trans hst.le)
  have hE := coupling_of_compact_hopf_bound (heatMeasure μ hQ s f) (heatMeasure μ hQ t f)
    p hgeo (sub_pos.mpr hst)
    (((∫x, heatAt μ hQ s f x*Real.log (heatAt μ hQ s f x) ∂μ)-
      ∫x, heatAt μ hQ t f x*Real.log (heatAt μ hQ t f x) ∂μ)/2)
  obtain ⟨π,hp,hF,hS,hc⟩ := hE (fun φ L hφ R hR => by
    rw [integral_heatMeasure μ hQ f hf0,integral_heatMeasure μ hQ f hf0]
    apply heat_hopf_entropy_dual μ hQ hφ hgeo p R hR f hf0 C hfC hs hst
      (heatAt_integrable_of_nonneg μ hQ s f hf0 hfi)
      (heatAt_integrable_of_nonneg μ hQ t f hf0 hfi)
      (heatAt_entropy_integrable μ hQ p hA hB hvol f hf0 hfr hs.le)
      (heatAt_entropy_integrable μ hQ p hA hB hvol f hf0 hfr (hs.le.trans hst.le))
    rw [heatAt_integral_eq_of_exponential_volume μ hQ p hA hB hvol f hf0 hfi hs.le,
      heatAt_integral_eq_of_exponential_volume μ hQ p hA hB hvol f hf0 hfi (hs.le.trans hst.le)])
  refine ⟨π,hp,hF,hS,?_⟩
  convert transportCost_le_of_scaled π (sub_pos.mpr hst) hc using 2; ring

 theorem heat_coupling_fisher_action (hgeo : IsGeodesicSpace X) (p : X) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 μ) (hf0 : 0 ≤ f) (hfi : Integrable f μ)
    (hfm : (∫x, f x ∂μ) = 1) {r : ℝ} (hfr : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r)
    (C : ℝ≥0) (hfC : ∀ᵐ x ∂μ, |f x| ≤ C) {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    ∃ π : Measure (X×X), IsProbabilityMeasure π ∧
      π.map Prod.fst = heatMeasure μ hQ s f ∧ π.map Prod.snd = heatMeasure μ hQ t f ∧
      transportCost π ≤ ENNReal.ofReal (t-s)*(∫⁻r in Ioc s t, fisherInformation μ hQ f r) := by
  rw [heatAt_entropy_dissipation μ hQ p hA hB hvol f hf0 hfi hfr hs hst.le,
    ← ENNReal.ofReal_mul (sub_pos.mpr hst).le]
  exact heat_coupling_entropy μ hQ hgeo p hA hB hvol f hf0 hfi hfm hfr C hfC hs hst

end RegularPointCoordinates

end OAI
