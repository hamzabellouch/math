import Mathlib
import OAI.Probability.SKFluctuations.AbsTiltedMeanLe

namespace OAI

/-! Eventually Nat Pos. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations
open Filter
open scoped Topology

 theorem eventually_nat_pos : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < (n : ℝ) := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact_mod_cast hn

 theorem eventually_const_mul_rpow_le (c : ℝ) {a b : ℝ} (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, c*(n : ℝ)^a ≤ (n : ℝ)^b := by
  have hh := ((tendsto_rpow_atTop (sub_pos.mpr hab)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop c)
  filter_upwards [hh, eventually_nat_pos] with n hn hp
  change c ≤ (n : ℝ)^(b-a) at hn
  rw [Real.rpow_sub hp] at hn
  exact (le_div_iff₀ (Real.rpow_pos_of_pos hp a)).mp hn

 theorem eventually_rpow_le_const_mul_rpow {c a b : ℝ} (hc : 0 < c) (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ)^a ≤ c*(n : ℝ)^b := by
  filter_upwards [eventually_const_mul_rpow_le (1/c) hab] with n hn
  have := mul_le_mul_of_nonneg_left hn hc.le
  field_simp at this
  linarith

 theorem tendsto_nat_rpow_zero {a : ℝ} (ha : a < 0) :
    Tendsto (fun n : ℕ => (n : ℝ)^a) atTop (𝓝 0) := by
  have ht := ((tendsto_rpow_atTop (by linarith : 0 < -a)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).inv_tendsto_atTop
  convert ht using 1
  funext n
  change (n : ℝ)^a = ((n : ℝ)^(-a))⁻¹
  rw [Real.rpow_neg (Nat.cast_nonneg n), inv_inv]

 theorem tendsto_const_div_nat_rpow {a : ℝ} (ha : 0 < a) (c : ℝ) :
    Tendsto (fun n : ℕ => c/(n : ℝ)^a) atTop (𝓝 0) := by
  have ht := (tendsto_nat_rpow_zero (neg_neg_of_pos ha)).const_mul c
  simpa only [Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv, mul_zero] using ht

end SKFluctuations

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

 theorem augmentedSD_monomial_bounds {beta m c C : ℝ} (hb : beta ≠ 0)
    (hm : 0 < m) (hm' : m < 1/300) (hc : 0 < c) (hC : 0 < C)
    (hwindow : ∀ᶠ n : ℕ in atTop,
      c*(n : ℝ)^(20*m) ≤ completedCenteredLogLaplace beta ((n : ℝ)^(-(1:ℝ)/6+5*m)) n ∧
      completedCenteredLogLaplace beta ((n : ℝ)^(-(1:ℝ)/6+5*m)) n ≤ C*(n : ℝ)^(100*m)) :
    ∃ L U : ℝ, 0 < L ∧ 0 < U ∧ ∀ᶠ n : ℕ in atTop,
      L*(n : ℝ)^((1:ℝ)/6-5*m) ≤ augmentedSD beta n ∧
      augmentedSD beta n ≤ U*(n : ℝ)^((1:ℝ)/6+95*m) := by
  let K := Real.log 2 - Real.log PreKopa.Density.positiveMass
  let B := C+|K|+1
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨PreKopa.tailRate/2, B/PreKopa.Density.positiveThreshold,
    div_pos PreKopa.tailRate_pos (by norm_num), div_pos hB PreKopa.Density.positiveThreshold_pos, ?_⟩
  have hs := (tendsto_nat_rpow_zero (by linarith : -(1:ℝ)/6+5*m < 0)).eventually
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1/2))
  have hlarge := (((tendsto_rpow_atTop (by positivity : 0 < 20*m)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul_atTop hc).eventually
    (eventually_gt_atTop (Real.log (1+PreKopa.Density.tailConstant)))
  filter_upwards [hwindow, hs, hlarge, eventually_ge_atTop 1] with n hn hs hnK hn1
  have hnpos : (0:ℝ) < (n : ℝ) := by exact_mod_cast (show 0<n by omega)
  have hnreal : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnpow : 1 ≤ (n : ℝ)^(100*m) := Real.one_le_rpow hnreal (by positivity)
  have ht : 0 < (n : ℝ)^(-(1:ℝ)/6+5*m) := Real.rpow_pos_of_pos hnpos _
  have hlo := augmentedSD_lower_of_logLaplace hb n ht (by linarith) (hnK.trans_le hn.1)
  have hup := augmentedSD_upper_of_logLaplace hb n ht hs.le hn.2
  have helo : PreKopa.tailRate/(2*(n : ℝ)^(-(1:ℝ)/6+5*m)) =
      (PreKopa.tailRate/2)*(n : ℝ)^((1:ℝ)/6-5*m) := by
    rw [show (1:ℝ)/6-5*m = - (-(1:ℝ)/6+5*m) by ring, Real.rpow_neg hnpos.le]
    ring
  constructor
  · rw [helo] at hlo
    exact hlo.le
  · apply hup.trans
    have hnum : C*(n : ℝ)^(100*m)+Real.log 2-Real.log PreKopa.Density.positiveMass ≤
        B*(n : ℝ)^(100*m) := by
      have hK : K ≤ |K| := le_abs_self _
      have hKm := mul_le_mul_of_nonneg_left hnpow (abs_nonneg K)
      dsimp [B, K] at *
      nlinarith
    have hdiv := div_le_div_of_nonneg_right hnum (mul_nonneg ht.le PreKopa.Density.positiveThreshold_pos.le)
    apply hdiv.trans_eq
    rw [div_mul_eq_div_div, mul_div_assoc, ← Real.rpow_sub hnpos]
    have he : 100*m-(-(1:ℝ)/6+5*m) = (1:ℝ)/6+95*m := by ring
    rw [he]
    ring

 theorem augmentedSD_scale_of_window (hw : PositiveLaplaceWindow) {beta : ℝ} (hb : 1 < beta)
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ)^((1:ℝ)/6-eta) ≤ augmentedSD beta n ∧
      augmentedSD beta n ≤ (n : ℝ)^((1:ℝ)/6+eta) := by
  obtain ⟨m,hm,hm'⟩ := exists_between (show (0:ℝ) < min (1/300) (eta/100) by positivity)
  have hm300 : m<1/300 := lt_of_lt_of_le hm' (min_le_left _ _)
  have hmeta : m<eta/100 := lt_of_lt_of_le hm' (min_le_right _ _)
  obtain ⟨c,C,hc,hC,n₀,hn₀⟩ := hw beta hb m hm hm300
  have hw' : ∀ᶠ n : ℕ in atTop,
      c*(n : ℝ)^(20*m) ≤ completedCenteredLogLaplace beta ((n : ℝ)^(-(1:ℝ)/6+5*m)) n ∧
      completedCenteredLogLaplace beta ((n : ℝ)^(-(1:ℝ)/6+5*m)) n ≤ C*(n : ℝ)^(100*m) :=
    (eventually_ge_atTop n₀).mono hn₀
  obtain ⟨L,U,hL,_,hLU⟩ := augmentedSD_monomial_bounds (by linarith : beta ≠ 0) hm hm300 hc hC hw'
  filter_upwards [hLU, eventually_rpow_le_const_mul_rpow hL (show (1:ℝ)/6-eta < 1/6-5*m by linarith),
    eventually_const_mul_rpow_le U (show (1:ℝ)/6+95*m < 1/6+eta by linarith)] with n hn hl hu
  exact ⟨hl.trans hn.1, hn.2.trans hu⟩

end SKFluctuations

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

 theorem nat_rpow_sq (n : ℕ) (a : ℝ) : ((n : ℝ)^a)^2 = (n : ℝ)^(2*a) := by
  rw [← Real.rpow_two, ← Real.rpow_mul (Nat.cast_nonneg n), mul_comm a]

 theorem augmentedSD_sq (beta : ℝ) (n : ℕ) :
    (augmentedSD beta n)^2 = freeEnergyVariance beta n + beta^2/2+1 :=
  Real.sq_sqrt (by positivity [freeEnergyVariance_nonneg beta n])

 theorem freeEnergySD_sq (beta : ℝ) (n : ℕ) :
    (freeEnergySD beta n)^2 = freeEnergyVariance beta n :=
  Real.sq_sqrt (freeEnergyVariance_nonneg beta n)

 theorem freeEnergySD_nonneg (beta : ℝ) (n : ℕ) : 0 ≤ freeEnergySD beta n := Real.sqrt_nonneg _

 theorem freeEnergySD_le_augmentedSD (beta : ℝ) (n : ℕ) :
    freeEnergySD beta n ≤ augmentedSD beta n := by
  apply Real.sqrt_le_sqrt
  nlinarith [sq_nonneg beta]

 theorem freeEnergySD_scale_of_window (hw : PositiveLaplaceWindow) {beta : ℝ} (hb : 1 < beta)
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ)^((1:ℝ)/6-eta) ≤ freeEnergySD beta n ∧
      freeEnergySD beta n ≤ (n : ℝ)^((1:ℝ)/6+eta) := by
  let δ := min (eta/2) (1/12)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδε : δ < eta := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδ12 : δ ≤ 1/12 := min_le_right _ _
  have hD := eventually_const_mul_rpow_le (2*(beta^2/2+1))
    (show (0:ℝ) < 1/3-2*δ by linarith)
  simp only [Real.rpow_zero, mul_one] at hD
  have hpow := eventually_const_mul_rpow_le 2
    (show (1:ℝ)/3-2*eta < 1/3-2*δ by linarith)
  filter_upwards [augmentedSD_scale_of_window hw hb hδ, augmentedSD_scale_of_window hw hb heta,
    hD, hpow] with n hn hn' hnD hnP
  constructor
  · have hs : ((n : ℝ)^((1:ℝ)/6-δ))^2 ≤ (augmentedSD beta n)^2 :=
      (sq_le_sq₀ (Real.rpow_nonneg (Nat.cast_nonneg n) _) (augmentedSD_pos _ _).le).mpr hn.1
    rw [nat_rpow_sq, augmentedSD_sq] at hs
    have he : 2*((1:ℝ)/6-δ) = 1/3-2*δ := by ring
    rw [he] at hs
    have htarg : ((n : ℝ)^((1:ℝ)/6-eta))^2 = (n : ℝ)^((1:ℝ)/3-2*eta) := by
      rw [nat_rpow_sq]; congr 1; ring
    have hv := freeEnergySD_sq beta n
    have hn0 := freeEnergySD_nonneg beta n
    nlinarith [Real.rpow_nonneg (Nat.cast_nonneg n) ((1:ℝ)/6-eta)]
  · exact (freeEnergySD_le_augmentedSD beta n).trans hn'.2

 theorem freeEnergyVariance_scale_of_window (hw : PositiveLaplaceWindow) {beta : ℝ} (hb : 1 < beta)
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ)^((1:ℝ)/3-eta) ≤ freeEnergyVariance beta n ∧
      freeEnergyVariance beta n ≤ (n : ℝ)^((1:ℝ)/3+eta) := by
  filter_upwards [freeEnergySD_scale_of_window hw hb (show 0<eta/2 by linarith)] with n hn
  have hlo := (sq_le_sq₀ (Real.rpow_nonneg (Nat.cast_nonneg n) _) (freeEnergySD_nonneg beta n)).mpr hn.1
  have hup := (sq_le_sq₀ (freeEnergySD_nonneg beta n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)).mpr hn.2
  rw [nat_rpow_sq, freeEnergySD_sq] at hlo
  rw [nat_rpow_sq, freeEnergySD_sq] at hup
  have he₁ : 2*((1:ℝ)/6-eta/2) = 1/3-eta := by ring
  have he₂ : 2*((1:ℝ)/6+eta/2) = 1/3+eta := by ring
  rw [he₁] at hlo
  rw [he₂] at hup
  exact ⟨hlo,hup⟩

end SKFluctuations

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

 theorem freeEnergy_smallball_tendsto_of_window (hw : PositiveLaplaceWindow) {beta : ℝ} (hb : 1 < beta)
    {eta : ℝ} (heta : 0 < eta) :
    Tendsto (fun n : ℕ => (disorderLaw n).real
      {g | |freeEnergy beta n g - meanFreeEnergy beta n| ≤ (n : ℝ)^((1:ℝ)/6-eta)}) atTop (𝓝 0) := by
  let δ : ℝ := min (eta/4) (1/48)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδe : δ ≤ eta/4 := min_le_left _ _
  have hδ48 : δ ≤ 1/48 := min_le_right _ _
  let K := 2 * PreKopa.Density.densityBoundConstant
  have hK : 0 ≤ K := by dsimp [K]; positivity [PreKopa.Density.densityBoundConstant_pos]
  have hbnd : ∀ᶠ n : ℕ in atTop, (disorderLaw n).real
      {g | |freeEnergy beta n g - meanFreeEnergy beta n| ≤ (n : ℝ)^((1:ℝ)/6-eta)} ≤
      K*((n : ℝ)^(-eta+δ)+2*(n : ℝ)^(2*δ-1/6)) +
        (beta^2/2+1)/(n : ℝ)^(2*δ) := by
    filter_upwards [augmentedSD_scale_of_window hw hb hδ, eventually_nat_pos] with n hn hp
    have hnδ := Real.rpow_pos_of_pos hp δ
    apply (freeEnergy_interval_bound (by linarith : beta ≠ 0) n
      (Real.rpow_nonneg hp.le _) hnδ).trans
    apply add_le_add
    · have hdiv := div_le_div_of_nonneg_left (by positivity : 0 ≤
          K*((n : ℝ)^((1:ℝ)/6-eta)+2*(n : ℝ)^δ))
        (Real.rpow_pos_of_pos hp ((1:ℝ)/6-δ)) hn.1
      apply hdiv.trans_eq
      rw [mul_div_assoc, add_div, mul_div_assoc, ← Real.rpow_sub hp, ← Real.rpow_sub hp]
      congr 2 <;> congr 1 <;> ring_nf
    · rw [nat_rpow_sq]
  have ht₁ := (tendsto_nat_rpow_zero (by linarith : -eta+δ<0)).add
    ((tendsto_nat_rpow_zero (by linarith : 2*δ-1/6<0)).const_mul 2)
  have ht₂ := tendsto_const_div_nat_rpow (by positivity : 0<2*δ) (beta^2/2+1)
  have ht := (ht₁.const_mul K).add ht₂
  simp only [mul_zero, add_zero] at ht
  exact squeeze_zero' (Filter.Eventually.of_forall fun _ => measureReal_nonneg) hbnd ht

 theorem freeEnergy_largetail_tendsto_of_window (hw : PositiveLaplaceWindow) {beta : ℝ} (hb : 1 < beta)
    {eta : ℝ} (heta : 0 < eta) :
    Tendsto (fun n : ℕ => (disorderLaw n).real
      {g | (n : ℝ)^((1:ℝ)/6+eta) < |freeEnergy beta n g - meanFreeEnergy beta n|}) atTop (𝓝 0) := by
  have hbnd : ∀ᶠ n : ℕ in atTop, (disorderLaw n).real
      {g | (n : ℝ)^((1:ℝ)/6+eta) < |freeEnergy beta n g - meanFreeEnergy beta n|} ≤
      (n : ℝ)^(-eta) := by
    filter_upwards [freeEnergyVariance_scale_of_window hw hb heta, eventually_nat_pos] with n hn hp
    have ht := NoiseTransfer.strict_tail_le_variance (memLp_freeEnergy beta n)
      (Real.rpow_pos_of_pos hp ((1:ℝ)/6+eta))
    apply ht.trans
    change freeEnergyVariance beta n / ((n : ℝ)^((1:ℝ)/6+eta))^2 ≤ _
    rw [nat_rpow_sq]
    apply (div_le_div_of_nonneg_right hn.2 (Real.rpow_nonneg hp.le _)).trans_eq
    rw [← Real.rpow_sub hp]
    congr 1
    ring
  exact squeeze_zero' (Filter.Eventually.of_forall fun _ => measureReal_nonneg)
    hbnd (tendsto_nat_rpow_zero (neg_neg_of_pos heta))

end SKFluctuations

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

 theorem measurableSet_fluctuationEvent (beta eta : ℝ) (n : ℕ) :
    MeasurableSet (fluctuationEvent beta eta n) := by
  have hm := ((continuous_freeEnergy beta n).measurable.sub_const (meanFreeEnergy beta n)).abs
  exact (measurableSet_le measurable_const hm).inter (measurableSet_le hm measurable_const)

 theorem fluctuationEvent_tendsto_of_window (hw : PositiveLaplaceWindow) {beta : ℝ} (hb : 1 < beta)
    {eta : ℝ} (heta : 0 < eta) :
    Tendsto (fun n : ℕ => disorderLaw n (fluctuationEvent beta eta n)) atTop (𝓝 1) := by
  have hbnd (n : ℕ) : (disorderLaw n).real (fluctuationEvent beta eta n)ᶜ ≤
      (disorderLaw n).real {g | |freeEnergy beta n g - meanFreeEnergy beta n| ≤ (n : ℝ)^((1:ℝ)/6-eta)} +
      (disorderLaw n).real {g | (n : ℝ)^((1:ℝ)/6+eta) < |freeEnergy beta n g - meanFreeEnergy beta n|} := by
    apply (measureReal_mono (s₂ :=
      {g | |freeEnergy beta n g - meanFreeEnergy beta n| ≤ (n : ℝ)^((1:ℝ)/6-eta)} ∪
      {g | (n : ℝ)^((1:ℝ)/6+eta) < |freeEnergy beta n g - meanFreeEnergy beta n|}) ?_).trans
      (measureReal_union_le _ _)
    intro g hg
    change ¬ ((n : ℝ)^((1:ℝ)/6-eta) ≤ |freeEnergy beta n g - meanFreeEnergy beta n| ∧
      |freeEnergy beta n g - meanFreeEnergy beta n| ≤ (n : ℝ)^((1:ℝ)/6+eta)) at hg
    by_cases hlow : |freeEnergy beta n g - meanFreeEnergy beta n| ≤ (n : ℝ)^((1:ℝ)/6-eta)
    · exact Or.inl hlow
    · exact Or.inr (lt_of_not_ge fun hu => hg ⟨(lt_of_not_ge hlow).le,hu⟩)
  have hzero := squeeze_zero (fun _ => measureReal_nonneg) hbnd
    (by simpa using ((freeEnergy_smallball_tendsto_of_window hw hb heta).add
      (freeEnergy_largetail_tendsto_of_window hw hb heta)))
  have hone : Tendsto (fun n => 1 - (disorderLaw n).real
      (fluctuationEvent beta eta n)ᶜ) atTop (𝓝 (1 - (0 : ℝ))) :=
    tendsto_const_nhds.sub hzero
  have he (n : ℕ) : 1-(disorderLaw n).real (fluctuationEvent beta eta n)ᶜ =
      (disorderLaw n).real (fluctuationEvent beta eta n) := by
    rw [measureReal_compl (measurableSet_fluctuationEvent beta eta n)]
    simp
  simp only [he, sub_zero] at hone
  have hr := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hone
  convert hr using 1
  · funext n
    exact (ENNReal.ofReal_toReal (measure_ne_top (disorderLaw n) _)).symm
  · exact (ENNReal.ofReal_one).symm ▸ rfl

 

 theorem main_of_positiveLaplaceWindow (hw : PositiveLaplaceWindow) : MainFluctuationStatement := by
  intro beta hb
  refine ⟨?_, ?_, ?_⟩
  · intro eta heta
    exact eventually_atTop.mp (freeEnergySD_scale_of_window hw hb heta)
  · intro eta heta
    exact eventually_atTop.mp (freeEnergyVariance_scale_of_window hw hb heta)
  · intro eta heta
    exact fluctuationEvent_tendsto_of_window hw hb heta

end SKFluctuations

namespace SKFluctuations.GaussianCalculus
open MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

theorem hasDerivAt_standardGaussianPDF (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have h := (((hasDerivAt_id x).pow 2).neg.div_const 2).exp.const_mul
    ((Real.sqrt (2 * Real.pi))⁻¹)
  rw [gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  apply h.congr_deriv
  dsimp
  ring

 
theorem integrable_standardGaussian_iff {f : ℝ → ℝ} :
    Integrable f (gaussianReal 0 1) ↔ Integrable (fun x => gaussianPDFReal 0 1 x * f x) := by
  rw [gaussianReal_of_var_ne_zero 0 (one_ne_zero : (1 : ℝ≥0) ≠ 0),
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (Filter.Eventually.of_forall fun _ => gaussianPDF_lt_top)]
  simp only [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _), smul_eq_mul]

 

theorem standardGaussian_stein {f f₁ : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (f₁ x) x)
    (hf : Integrable f (gaussianReal 0 1))
    (hf₁ : Integrable f₁ (gaussianReal 0 1))
    (hxf : Integrable (fun x => x*f x) (gaussianReal 0 1)) :
    (∫ x, x*f x ∂gaussianReal 0 1) = ∫ x, f₁ x ∂gaussianReal 0 1 := by
  have hd' (x : ℝ) : HasDerivAt (fun y => gaussianPDFReal 0 1 y * f y)
      (gaussianPDFReal 0 1 x * f₁ x - gaussianPDFReal 0 1 x * (x*f x)) x := by
    exact ((hasDerivAt_standardGaussianPDF x).mul (hd x)).congr_deriv (by ring)
  have hh := integral_eq_zero_of_hasDerivAt_of_integrable hd'
    ((integrable_standardGaussian_iff.mp hf₁).sub (integrable_standardGaussian_iff.mp hxf))
    (integrable_standardGaussian_iff.mp hf)
  rw [integral_sub (integrable_standardGaussian_iff.mp hf₁)
    (integrable_standardGaussian_iff.mp hxf)] at hh
  rw [integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : ℝ≥0) ≠ 0),
    integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : ℝ≥0) ≠ 0)]
  simpa only [smul_eq_mul] using (sub_eq_zero.mp hh).symm

end SKFluctuations.GaussianCalculus

namespace SKFluctuations.GaussianCalculus
open MeasureTheory ProbabilityTheory
open scoped Topology NNReal

 

theorem standardGaussianVector_stein {n : ℕ} (i : Fin (n+1))
    {f f₁ : (Fin (n+1) → ℝ) → ℝ}
    (hd : ∀ (y : Fin n → ℝ) t, HasDerivAt (fun s => f (i.insertNth s y)) (f₁ (i.insertNth t y)) t)
    (hf : Integrable f (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1))
    (hf₁ : Integrable f₁ (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1))
    (hxf : Integrable (fun x => x i*f x) (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1)) :
    (∫ x, x i*f x ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) =
      ∫ x, f₁ x ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1) := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i).symm
  have he : MeasurePreserving e ((gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin n => gaussianReal 0 1))
      (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => gaussianReal 0 1) i).symm _
  have heq (t : ℝ) (y : Fin n → ℝ) : e (t,y) = i.insertNth t y := rfl
  have hF := he.integrable_comp_of_integrable hf
  have hF₁ := he.integrable_comp_of_integrable hf₁
  have hXF := he.integrable_comp_of_integrable hxf
  rw [← he.integral_comp' (fun x => x i*f x), ← he.integral_comp' f₁]
  change (∫ x, ((fun x => x i*f x) ∘ e) x ∂_) = ∫ x, (f₁ ∘ e) x ∂_
  rw [integral_prod_symm _ hXF, integral_prod_symm _ hF₁]
  apply integral_congr_ae
  filter_upwards [hF.prod_left_ae, hF₁.prod_left_ae, hXF.prod_left_ae] with y hy hy₁ hyx
  simp only [Function.comp_def, heq, Fin.insertNth_apply_same] at hy hy₁ hyx ⊢
  exact standardGaussian_stein (hd y) hy hy₁ hyx

end SKFluctuations.GaussianCalculus

namespace SKFluctuations.GaussianCalculus
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 

def ExpNormBounded (f : E → ℝ) : Prop :=
  Continuous f ∧ ∃ C c : ℝ, 0 ≤ C ∧ 0 ≤ c ∧ ∀ x, |f x| ≤ C*Real.exp (c*‖x‖)

theorem affine_norm_exp_bound {f : E → ℝ} {C c : ℝ}
    (hC : 0 ≤ C) (hc : 0 ≤ c) (hb : ∀ x, |f x| ≤ C*Real.exp (c*‖x‖))
    (x : E) (a : ℝ) (z : E) :
    |f (x+a • z)| ≤ C*Real.exp (c*‖x‖)*Real.exp (c*|a| *‖z‖) := by
  calc
    _ ≤ C*Real.exp (c*‖x+a • z‖) := hb _
    _ ≤ C*Real.exp (c*(‖x‖+|a| *‖z‖)) := by
      gcongr
      simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le x (a • z)
    _ = _ := by rw [mul_add, Real.exp_add]; ring_nf

theorem affine_coord_exp_bound {ι : Type*} [Fintype ι]
    {f : (ι → ℝ) → ℝ} {C c : ℝ}
    (hC : 0 ≤ C) (hc : 0 ≤ c) (hb : ∀ x, |f x| ≤ C*Real.exp (c*‖x‖))
    (x : ι → ℝ) (a : ℝ) (z : ι → ℝ) (i : ι) :
    |z i*f (x+a • z)| ≤ C*Real.exp (c*‖x‖)*Real.exp ((c*|a|+1)*‖z‖) := by
  rw [abs_mul]
  calc
    _ ≤ Real.exp ‖z‖ * (C*Real.exp (c*‖x‖)*Real.exp (c*|a| *‖z‖)) := by
      apply mul_le_mul _ (affine_norm_exp_bound hC hc hb x a z) (abs_nonneg _) (Real.exp_nonneg _)
      have he := Real.add_one_le_exp ‖z‖
      have hz : |z i| ≤ ‖z‖ := norm_le_pi_norm z i
      linarith
    _ = _ := by rw [show (c*|a|+1)*‖z‖ = ‖z‖+c*|a| *‖z‖ by ring, Real.exp_add]; ring

variable [MeasurableSpace E] [BorelSpace E]

theorem ExpNormBounded.affine_integrable {f : E → ℝ} (hf : ExpNormBounded f)
    {ν : Measure E} (hν : ExponentialIncrement ν) (x : E) (a : ℝ) :
    Integrable (fun z => f (x+a • z)) ν := by
  obtain ⟨C,c,hC,hc,hb⟩ := hf.2
  apply ((hν (c*|a|)).const_mul (C*Real.exp (c*‖x‖))).mono'
    (hf.1.comp (continuous_const.add ((continuous_const (y := a)).smul continuous_id))).aestronglyMeasurable
  exact Eventually.of_forall fun z => by
    change |f (x+a • z)| ≤ _
    exact affine_norm_exp_bound hC hc hb x a z

theorem ExpNormBounded.affine_coord_integrable {ι : Type*} [Fintype ι]
    {f : (ι → ℝ) → ℝ} (hf : ExpNormBounded f)
    (q : ι → ℝ≥0) (x : ι → ℝ) (a : ℝ) (i : ι) :
    Integrable (fun z => z i*f (x+a • z)) (Measure.pi fun i => gaussianReal 0 (q i)) := by
  obtain ⟨C,c,hC,hc,hb⟩ := hf.2
  have hm : AEStronglyMeasurable (fun z => z i*f (x+a • z))
      (Measure.pi fun i => gaussianReal 0 (q i)) := by
    exact ((continuous_apply i).mul (hf.1.comp (continuous_const.add
      ((continuous_const (y := a)).smul continuous_id)))).aestronglyMeasurable
  apply (((exponentialIncrement_gaussian q) (c*|a|+1)).const_mul (C*Real.exp (c*‖x‖))).mono' hm
  exact Eventually.of_forall fun z => by
    change |z i*f (x+a • z)| ≤ _
    exact affine_coord_exp_bound hC hc hb x a z i

omit [MeasurableSpace E] [BorelSpace E] [NormedSpace ℝ E] in
theorem ExpNormBounded.exp_lipschitz {F : E → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (m : ℝ) : ExpNormBounded (fun x => Real.exp (m*F x)) := by
  refine ⟨Real.continuous_exp.comp (hF.continuous.const_mul m),
    Real.exp (m*F 0), |m| *C, Real.exp_nonneg _, mul_nonneg (abs_nonneg _) C.coe_nonneg, ?_⟩
  intro x
  rw [abs_of_pos (Real.exp_pos _), ← Real.exp_add, Real.exp_le_exp]
  have ht : |F x-F 0| ≤ C*‖x‖ := by simpa only [Real.dist_eq, dist_zero_right] using hF.dist_le_mul x 0
  have hm := le_abs_self (m*(F x-F 0))
  rw [abs_mul] at hm
  have h := mul_le_mul_of_nonneg_left ht (abs_nonneg m)
  nlinarith

omit [MeasurableSpace E] [BorelSpace E] in
theorem ExpNormBounded.bdd_mul {f A : E → ℝ} (hf : ExpNormBounded f)
    (hA : BddSmooth 0 A) : ExpNormBounded (fun x => A x*f x) := by
  obtain ⟨C,c,hC,hc,hb⟩ := hf.2
  obtain ⟨B,hB,hbB⟩ := hA.bound
  refine ⟨hA.continuous.mul hf.1, B*C, c, mul_nonneg hB hC, hc, fun x => ?_⟩
  rw [abs_mul]
  exact (mul_le_mul (hbB x) (hb x) (abs_nonneg _) hB).trans_eq (by ring)

end SKFluctuations.GaussianCalculus

namespace SKFluctuations.GaussianCalculus
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 

theorem hasDerivAt_gaussian_vector_affine {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} {f₁ : Fin n → (Fin n → ℝ) → ℝ}
    (hf : ExpNormBounded f) (hf₁ : ∀ i, ExpNormBounded (f₁ i))
    (hd : ∀ x v t, HasDerivAt (fun s : ℝ => f (x+s • v))
      (∑ i, v i*f₁ i (x+t • v)) t) (x : Fin n → ℝ) (a : ℝ) :
    HasDerivAt (fun t => ∫ z, f (x+t • z) ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1))
      (∫ z, ∑ i, z i*f₁ i (x+a • z) ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)) a := by
  choose C c hC hc hb using fun i => (hf₁ i).2
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.ball a 1) (bound := fun z => ∑ i,
      C i*Real.exp (c i*‖x‖)*Real.exp ((c i*(|a|+1)+1)*‖z‖)))
    (Metric.ball_mem_nhds a (by norm_num)) _
    (hf.affine_integrable (exponentialIncrement_gaussian (fun _ => 1)) x a) _ _ _ _ |>.2
  · exact Eventually.of_forall fun t =>
      (hf.1.comp (continuous_const.add ((continuous_const (y := t)).smul continuous_id))).aestronglyMeasurable
  · exact (continuous_finsetSum _ fun i _ => (continuous_apply i).mul
      ((hf₁ i).1.comp (continuous_const.add ((continuous_const (y := a)).smul continuous_id)))).aestronglyMeasurable
  · apply Eventually.of_forall
    intro z t ht
    have hat : |t| ≤ |a|+1 := by
      have h := (Metric.mem_ball.mp ht).le
      rw [Real.dist_eq] at h
      calc |t| = |(t-a)+a| := by congr 1; ring
           _ ≤ |t-a|+|a| := abs_add_le _ _
           _ ≤ |a|+1 := by linarith
    calc
      ‖∑ i, z i*f₁ i (x+t • z)‖ ≤ ∑ i, |z i*f₁ i (x+t • z)| := norm_sum_le _ _
      _ ≤ _ := Finset.sum_le_sum fun i _ =>
        (affine_coord_exp_bound (hC i) (hc i) (hb i) x t z i).trans (by have hCi := hC i; have hci := hc i; gcongr)
  · exact integrable_finsetSum _ fun i _ =>
      ((exponentialIncrement_gaussian (fun _ : Fin n => 1)) _).const_mul _
  · exact Eventually.of_forall fun z t _ => hd x z t

 

theorem hasDerivAt_gaussian_vector_affine_heat {n : ℕ}
    {f : (Fin (n+1) → ℝ) → ℝ} {f₁ f₂ : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ}
    (hf : ExpNormBounded f) (hf₁ : ∀ i, ExpNormBounded (f₁ i))
    (hf₂ : ∀ i, ExpNormBounded (f₂ i))
    (hd : ∀ x v t, HasDerivAt (fun s : ℝ => f (x+s • v))
      (∑ i, v i*f₁ i (x+t • v)) t)
    (hd₁ : ∀ i x t, HasDerivAt (fun s : ℝ => f₁ i (x+s • Pi.single i 1))
      (f₂ i (x+t • Pi.single i 1)) t) (x : Fin (n+1) → ℝ) (a : ℝ) :
    HasDerivAt (fun t => ∫ z, f (x+t • z) ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1))
      (a * ∫ z, ∑ i, f₂ i (x+a • z) ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) a := by
  have hs (i : Fin (n+1)) :
      (∫ z, z i*f₁ i (x+a • z) ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) =
       a*∫ z, f₂ i (x+a • z) ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1) := by
    have h := standardGaussianVector_stein i
      (f := fun z => f₁ i (x+a • z)) (f₁ := fun z => a*f₂ i (x+a • z))
      ?_ ((hf₁ i).affine_integrable (exponentialIncrement_gaussian (fun _ => 1)) x a)
      (((hf₂ i).affine_integrable (exponentialIncrement_gaussian (fun _ => 1)) x a).const_mul a)
      ((hf₁ i).affine_coord_integrable (fun _ => 1) x a i)
    · simpa only [integral_const_mul] using h
    · intro y t
      have he (s : ℝ) : x+a • i.insertNth s y =
          (x+a • i.insertNth 0 y)+(a*s) • Pi.single i 1 := by
        ext j
        by_cases hj : j = i
        · subst j
          simp
        · obtain ⟨k,rfl⟩ := (Fin.eq_self_or_eq_succAbove i j).resolve_left hj
          simp
      have hd' := (hd₁ i (x+a • i.insertNth 0 y) (a*t)).comp t ((hasDerivAt_id t).const_mul a)
      simpa only [Function.comp_def, ← he, mul_one, mul_comm] using hd' 
  apply (hasDerivAt_gaussian_vector_affine hf hf₁ hd x a).congr_deriv
  rw [integral_finsetSum _ (fun i _ => (hf₁ i).affine_coord_integrable (fun _ => 1) x a i)]
  simp_rw [hs]
  rw [← Finset.mul_sum, integral_finsetSum _ (fun i _ =>
    (hf₂ i).affine_integrable (exponentialIncrement_gaussian (fun _ => 1)) x a)]

theorem hasDerivAt_gaussian_vector_variance {n : ℕ}
    {f : (Fin (n+1) → ℝ) → ℝ} {f₁ f₂ : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ}
    (hf : ExpNormBounded f) (hf₁ : ∀ i, ExpNormBounded (f₁ i))
    (hf₂ : ∀ i, ExpNormBounded (f₂ i))
    (hd : ∀ x v t, HasDerivAt (fun s : ℝ => f (x+s • v))
      (∑ i, v i*f₁ i (x+t • v)) t)
    (hd₁ : ∀ i x t, HasDerivAt (fun s : ℝ => f₁ i (x+s • Pi.single i 1))
      (f₂ i (x+t • Pi.single i 1)) t) (x : Fin (n+1) → ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ z, f (x+Real.sqrt s • z) ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1))
      ((1/2:ℝ) * ∫ z, ∑ i, f₂ i (x+Real.sqrt t • z) ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) t := by
  have h := (hasDerivAt_gaussian_vector_affine_heat hf hf₁ hf₂ hd hd₁ x (Real.sqrt t)).comp t
    (Real.hasDerivAt_sqrt ht.ne')
  exact h.congr_deriv (by field_simp [Real.sqrt_ne_zero'.mpr ht])

end SKFluctuations.GaussianCalculus

namespace SKFluctuations.GaussianCalculus
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem ExpNormBounded.continuous_gaussian_affine {f : E → ℝ} (hf : ExpNormBounded f)
    {ν : Measure E} (hν : ExponentialIncrement ν) (x : E) :
    Continuous (fun a : ℝ => ∫ z, f (x+a • z) ∂ν) := by
  obtain ⟨C,c,hC,hc,hb⟩ := hf.2
  apply continuous_iff_continuousAt.mpr
  intro a
  apply continuousAt_of_dominated
    (bound := fun z => C*Real.exp (c*‖x‖)*Real.exp (c*(|a|+1)*‖z‖))
  · exact Eventually.of_forall fun t =>
      (hf.1.comp (continuous_const.add ((continuous_const (y := t)).smul continuous_id))).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds a (by norm_num : (0:ℝ)<1)] with t ht
    apply Eventually.of_forall
    intro z
    have hat : |t| ≤ |a|+1 := by
      have h := (Metric.mem_ball.mp ht).le
      rw [Real.dist_eq] at h
      calc |t| = |(t-a)+a| := by congr 1; ring
           _ ≤ |t-a|+|a| := abs_add_le _ _
           _ ≤ |a|+1 := by linarith
    change |f (x+t • z)| ≤ _
    exact (affine_norm_exp_bound hC hc hb x t z).trans (by gcongr)
  · exact (hν _).const_mul _
  · exact Eventually.of_forall fun z =>
      (hf.1.comp (continuous_const.add (continuous_id.smul continuous_const))).continuousAt

theorem ExpNormBounded.continuous_gaussian_variance {f : E → ℝ} (hf : ExpNormBounded f)
    {ν : Measure E} (hν : ExponentialIncrement ν) (x : E) :
    Continuous (fun s => ∫ z, f (x+Real.sqrt s • z) ∂ν) :=
  (hf.continuous_gaussian_affine hν x).comp Real.continuous_sqrt

 

theorem hasDerivWithinAt_gaussian_vector_variance_zero {n : ℕ}
    {f : (Fin (n+1) → ℝ) → ℝ} {f₁ f₂ : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ}
    (hf : ExpNormBounded f) (hf₁ : ∀ i, ExpNormBounded (f₁ i))
    (hf₂ : ∀ i, ExpNormBounded (f₂ i))
    (hd : ∀ x v t, HasDerivAt (fun s : ℝ => f (x+s • v))
      (∑ i, v i*f₁ i (x+t • v)) t)
    (hd₁ : ∀ i x t, HasDerivAt (fun s : ℝ => f₁ i (x+s • Pi.single i 1))
      (f₂ i (x+t • Pi.single i 1)) t) (x : Fin (n+1) → ℝ) :
    HasDerivWithinAt (fun s => ∫ z, f (x+Real.sqrt s • z)
        ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1))
      ((1/2:ℝ)*∑ i, f₂ i x) (Ici 0) 0 := by
  let ν := Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)
  have hν : ExponentialIncrement ν := exponentialIncrement_gaussian (fun _ => 1)
  have hcont : Continuous (fun s => (1/2:ℝ)*∫ z, ∑ i, f₂ i (x+Real.sqrt s • z) ∂ν) := by
    apply Continuous.const_mul _ _
    have hc := continuous_finsetSum Finset.univ (fun i _ => (hf₂ i).continuous_gaussian_variance hν x)
    convert hc using 1
    ext s
    exact integral_finsetSum _ fun i _ => (hf₂ i).affine_integrable hν x _
  apply hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioi 0)
  · exact fun s hs => (hasDerivAt_gaussian_vector_variance hf hf₁ hf₂ hd hd₁ x hs).differentiableAt.differentiableWithinAt
  · exact (hf.continuous_gaussian_variance hν x).continuousAt.continuousWithinAt
  · exact self_mem_nhdsWithin
  · have hlim : Tendsto (fun s => (1/2:ℝ)*∫ z, ∑ i, f₂ i (x+Real.sqrt s • z) ∂ν)
        (𝓝[>] (0:ℝ)) (𝓝 ((1/2:ℝ)*∫ z, ∑ i, f₂ i (x+Real.sqrt 0 • z) ∂ν)) :=
      hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have he : (fun s => deriv (fun r => ∫ z, f (x+Real.sqrt r • z) ∂ν) s) =ᶠ[𝓝[>] (0:ℝ)]
        (fun s => (1/2:ℝ)*∫ z, ∑ i, f₂ i (x+Real.sqrt s • z) ∂ν) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (hasDerivAt_gaussian_vector_variance hf hf₁ hf₂ hd hd₁ x hs).deriv
    have hc : Tendsto (fun s => (1/2:ℝ)*∫ z, ∑ i, f₂ i (x+Real.sqrt s • z) ∂ν)
        (𝓝[>] (0:ℝ)) (𝓝 ((1/2:ℝ)*∑ i, f₂ i x)) := by
      simpa only [Real.sqrt_zero, zero_smul, add_zero, integral_const, probReal_univ, one_smul] using hlim
    exact hc.congr' he.symm

theorem hasDerivWithinAt_gaussian_vector_variance {n : ℕ}
    {f : (Fin (n+1) → ℝ) → ℝ} {f₁ f₂ : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ}
    (hf : ExpNormBounded f) (hf₁ : ∀ i, ExpNormBounded (f₁ i))
    (hf₂ : ∀ i, ExpNormBounded (f₂ i))
    (hd : ∀ x v t, HasDerivAt (fun s : ℝ => f (x+s • v))
      (∑ i, v i*f₁ i (x+t • v)) t)
    (hd₁ : ∀ i x t, HasDerivAt (fun s : ℝ => f₁ i (x+s • Pi.single i 1))
      (f₂ i (x+t • Pi.single i 1)) t) (x : Fin (n+1) → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => ∫ z, f (x+Real.sqrt s • z) ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1))
      ((1/2:ℝ) * ∫ z, ∑ i, f₂ i (x+Real.sqrt t • z) ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) (Ici 0) t := by
  rcases eq_or_lt_of_le ht with ht | ht
  · subst t
    simpa only [Real.sqrt_zero, zero_smul, add_zero, integral_const, probReal_univ, one_smul]
      using hasDerivWithinAt_gaussian_vector_variance_zero hf hf₁ hf₂ hd hd₁ x
  · exact (hasDerivAt_gaussian_vector_variance hf hf₁ hf₂ hd hd₁ x ht).hasDerivWithinAt

end SKFluctuations.GaussianCalculus

end

end OAI
