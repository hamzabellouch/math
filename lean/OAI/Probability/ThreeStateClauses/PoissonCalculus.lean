import Mathlib
import OAI.Probability.ThreeStateClauses.PositiveFixed
import OAI.Probability.ThreeStateClauses.PoissonLaw

namespace OAI

/-! Poisson Calculus. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace ThreeState.TreeClauses.Probability

def exponentialAverage (f : ℕ → ℝ) (t : ℝ) : ℝ := ∑' n, t^n/(n.factorial:ℝ)*f n

def poissonAverage (f : ℕ → ℝ) (t : ℝ) : ℝ := Real.exp (-t)*exponentialAverage f t

lemma exponentialAverage_summable {f : ℕ → ℝ} {B : ℝ} (hB : ∀ n, |f n| ≤ B) (t : ℝ) :
    Summable (fun n ↦ t^n/(n.factorial:ℝ)*f n) := by
  apply Summable.of_norm_bounded ((Real.summable_pow_div_factorial |t|).mul_right B)
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, Nat.abs_cast]
  exact mul_le_mul_of_nonneg_left (hB n) (by positivity)

private def exponentialDerivative (f : ℕ → ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 0
  | n+1, t => t^n/(n.factorial:ℝ)*f (n+1)

private lemma exponentialDerivative_summable {f : ℕ → ℝ} {B : ℝ} (hB : ∀ n, |f n| ≤ B) (t : ℝ) :
    Summable (fun n ↦ exponentialDerivative f n t) := by
  apply (summable_nat_add_iff 1).mp
  exact exponentialAverage_summable (fun n ↦ hB (n+1)) t

private lemma exponentialDerivative_sum {f : ℕ → ℝ} {B : ℝ} (hB : ∀ n, |f n| ≤ B) (t : ℝ) :
    (∑' n, exponentialDerivative f n t) = exponentialAverage (fun n ↦ f (n+1)) t := by
  rw [← (exponentialDerivative_summable hB t).sum_add_tsum_nat_add 1]
  simp [exponentialDerivative, exponentialAverage]

lemma hasDerivAt_exponentialAverage {f : ℕ → ℝ} {B : ℝ} (hB : ∀ n, |f n| ≤ B) (t : ℝ) :
    HasDerivAt (exponentialAverage f) (exponentialAverage (fun n ↦ f (n+1)) t) t := by
  let R := |t|+1
  have hR : 0 < R := by dsimp [R]; positivity
  have ht : t ∈ Ioo (-R) R := by
    constructor <;> dsimp [R] <;> linarith [le_abs_self t, neg_abs_le t]
  let u : ℕ → ℝ := fun n ↦ exponentialDerivative (fun _ ↦ B) n R
  have hu : Summable u := exponentialDerivative_summable (B := |B|) (fun _ ↦ le_refl _) R
  have hd (n : ℕ) (y : ℝ) : HasDerivAt (fun z : ℝ ↦ z^n/(n.factorial:ℝ)*f n)
      (exponentialDerivative f n y) y := by
    cases n with
    | zero => simpa [exponentialDerivative] using hasDerivAt_const y (f 0)
    | succ n =>
      convert (((hasDerivAt_id y).pow (n+1)).div_const ((n+1).factorial:ℝ)).mul_const (f (n+1)) using 1
      all_goals try rfl
      all_goals try simp only [exponentialDerivative, id_eq]
      rw [Nat.factorial_succ, Nat.cast_mul]
      simp only [Nat.add_sub_cancel, mul_one]
      have hn : ((n+1:ℕ):ℝ) ≠ 0 := by positivity
      field_simp
  have hb (n : ℕ) (y : ℝ) (hy : y ∈ Ioo (-R) R) : ‖exponentialDerivative f n y‖ ≤ u n := by
    have hyR : |y| ≤ R := (abs_le).2 ⟨le_of_lt hy.1, le_of_lt hy.2⟩
    cases n with
    | zero => simp [exponentialDerivative, u]
    | succ n =>
      dsimp [exponentialDerivative, u]
      rw [abs_mul, abs_div, abs_pow, Nat.abs_cast]
      exact mul_le_mul (div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg y) hyR n) (by positivity))
        (hB (n+1)) (abs_nonneg _) (by positivity)
  have hh := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo (convex_Ioo (-R) R).isPreconnected
    (fun n y _ ↦ hd n y) hb ht (exponentialAverage_summable hB t) ht
  rw [exponentialDerivative_sum hB t] at hh
  exact hh

theorem hasDerivAt_poissonAverage {f : ℕ → ℝ} {B : ℝ} (hB : ∀ n, |f n| ≤ B) (t : ℝ) :
    HasDerivAt (poissonAverage f)
      (poissonAverage (fun n ↦ f (n+1)) t-poissonAverage f t) t := by
  have hd := ((hasDerivAt_neg t).exp).mul (hasDerivAt_exponentialAverage hB t)
  exact hd.congr_deriv (by unfold poissonAverage; ring)

lemma poissonAverage_eq_tsum {f : ℕ → ℝ} {B : ℝ} (hB : ∀ n, |f n| ≤ B) (t : ℝ) :
    poissonAverage f t = ∑' n, poissonWeight t n*f n := by
  rw [poissonAverage, exponentialAverage, ← (exponentialAverage_summable hB t).tsum_mul_left]
  apply tsum_congr; intro n; unfold poissonWeight; ring

lemma poissonAverage_eq_integral {f : ℕ → ℝ} {B : ℝ} (hB : ∀ n, |f n| ≤ B) (t : ℝ≥0) :
    poissonAverage f t = ∫ n, f n ∂(poissonPMF t).toMeasure := by
  rw [PMF.integral_eq_tsum]
  · simp only [poissonPMF_real, smul_eq_mul]
    exact poissonAverage_eq_tsum hB t
  · exact Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable B
      (Eventually.of_forall (fun n ↦ by simpa only [Real.norm_eq_abs] using hB n))

lemma continuous_poissonAverage {f : ℕ → ℝ} {B : ℝ} (hB : ∀ n, |f n| ≤ B) :
    Continuous (poissonAverage f) := continuous_iff_continuousAt.mpr
  (fun t ↦ (hasDerivAt_poissonAverage hB t).continuousAt)

lemma poissonAverage_zero (f : ℕ → ℝ) : poissonAverage f 0 = f 0 := by
  rw [poissonAverage, neg_zero, Real.exp_zero, one_mul, exponentialAverage, tsum_eq_single 0]
  · simp
  · intro n hn
    simp [zero_pow hn]

end ThreeState.TreeClauses.Probability

end 

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace ThreeState.TreeClauses.Experiment
open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive ThreeState.TreeClauses.Probability

lemma offspring_positive (ρ : PMF ℕ) (Q : Law) {lam : ℝ}
    (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) :
    ∀ᵐ m ∂(offspringLaw ρ Q hl₀ hl₁).probability.toMeasure, PositiveMessage m.1 := by
  apply Measure.ae_sum_iff.mpr
  intro n
  exact Measure.ae_smul_measure (finite_positive Q hl₀ hl₁ n) _

lemma correction_nonneg (m : Message) : 0 ≤ correction m.1 := by
  unfold correction
  apply div_nonneg _ (by norm_num)
  have h := avg_mono (fun i ↦ mul_nonneg (coordinate_nonneg m i) (sq_nonneg (logCentered m.1 i)))
  simpa only [avg_const] using h

private lemma poisson_mixture_integrable_nonneg (t : ℝ≥0) (P : ℕ → ProbabilityMeasure Message)
    {f : Message → ℝ} (hi : ∀ n, Integrable f (P n).toMeasure)
    (hp : ∀ n, ∀ᵐ m ∂(P n).toMeasure, 0 ≤ f m)
    (hs : Summable (fun n ↦ poissonWeight t n*(∫ m, f m ∂(P n).toMeasure))) :
    Integrable f (mixtureProbability (poissonPMF t) P).toMeasure := by
  apply mixture_integrable _ P hi
  simp only [poissonPMF_real]
  apply hs.congr
  intro n
  congr 1
  exact integral_congr_ae ((hp n).mono (fun m hm ↦ (abs_of_nonneg hm).symm))

lemma poisson_integrable_symEntropy (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1)
    (t : ℝ≥0) : Integrable (fun m : Message ↦ symEntropy m.1) (poissonLaw Q hl₀ hl₁ t).probability.toMeasure := by
  apply poisson_mixture_integrable_nonneg t (fun n ↦ finiteProbability Q hl₀ hl₁ n)
    (finite_integrable_symEntropy Q hl₀ hl₁)
    (fun n ↦ (finite_positive Q hl₀ hl₁ n).mono (fun m hm ↦ symEntropy_nonneg hm))
  have he (n : ℕ) : (∫ m, symEntropy m.1 ∂(finiteProbability Q hl₀ hl₁ n).toMeasure) =
      (n:ℝ)*edgeJMean Q lam := finiteLaw_symEntropy Q hl₀ hl₁ n
  simp_rw [he, ← mul_assoc]
  exact (poissonWeight_mean t).summable.mul_right _

lemma poisson_integrable_correction (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1)
    (t : ℝ≥0) : Integrable (fun m : Message ↦ correction m.1) (poissonLaw Q hl₀ hl₁ t).probability.toMeasure := by
  apply poisson_mixture_integrable_nonneg t (fun n ↦ finiteProbability Q hl₀ hl₁ n)
    (finite_integrable_correction Q hl₀ hl₁)
    (fun _ ↦ Filter.Eventually.of_forall correction_nonneg)
  have h := ((poissonWeight_mean t).summable.mul_right
    (∫ m, correction (edgeMessage lam m) ∂Q.probability.toMeasure)).add
    ((poissonWeight_factorial_second t).summable.mul_right (2*(edgeJMean Q lam)^2))
  apply h.congr
  intro n
  have he := finiteLaw_correction Q hl₀ hl₁ n
  change (∫ m, correction m.1 ∂(finiteProbability Q hl₀ hl₁ n).toMeasure) = _ at he
  rw [he]
  unfold edgeJMean
  ring

lemma poissonLaw_symEntropy (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1)
    (t : ℝ≥0) :
    (∫ m, symEntropy m.1 ∂(poissonLaw Q hl₀ hl₁ t).probability.toMeasure) = (t:ℝ)*edgeJMean Q lam := by
  rw [show (poissonLaw Q hl₀ hl₁ t).probability = mixtureProbability (poissonPMF t)
    (fun n ↦ (finiteLaw Q hl₀ hl₁ n).probability) from rfl,
    integral_mixtureProbability _ _ (poisson_integrable_symEntropy Q hl₀ hl₁ t)]
  simp only [poissonPMF_real, finiteLaw_symEntropy]
  exact ((poissonWeight_mean t).mul_right (edgeJMean Q lam)).tsum_eq |> fun h ↦ by
    simpa only [mul_assoc, edgeJMean] using h

lemma poissonLaw_correction (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1)
    (t : ℝ≥0) :
    (∫ m, correction m.1 ∂(poissonLaw Q hl₀ hl₁ t).probability.toMeasure) =
      (t:ℝ)*(∫ m, correction (edgeMessage lam m) ∂Q.probability.toMeasure)+
      2*(t:ℝ)^2*(edgeJMean Q lam)^2 := by
  rw [show (poissonLaw Q hl₀ hl₁ t).probability = mixtureProbability (poissonPMF t)
    (fun n ↦ (finiteLaw Q hl₀ hl₁ n).probability) from rfl,
    integral_mixtureProbability _ _ (poisson_integrable_correction Q hl₀ hl₁ t)]
  simp only [poissonPMF_real, finiteLaw_correction]
  have h := ((poissonWeight_mean t).mul_right
    (∫ m, correction (edgeMessage lam m) ∂Q.probability.toMeasure)).add
    ((poissonWeight_factorial_second t).mul_right (2*(edgeJMean Q lam)^2))
  convert h.tsum_eq using 1
  · apply tsum_congr; intro n; unfold edgeJMean; ring
  · ring

def iMean (Q : Law) : ℝ := ∫ m, info m.1 ∂Q.probability.toMeasure

def edgeIMean (Q : Law) (lam : ℝ) : ℝ := ∫ m, info (edgeMessage lam m) ∂Q.probability.toMeasure

lemma bounded_iMean : ∃ B : ℝ, ∀ Q : Law, |iMean Q| ≤ B := by
  have hc : Continuous (fun m : Message ↦ info m.1) := continuous_info_comp continuous_subtype_val
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨B, fun Q ↦ ?_⟩
  apply (abs_integral_le_integral_abs).trans
  exact (integral_mono (compact_integrable (continuous_info_comp continuous_subtype_val).abs)
    (integrable_const B) (fun m ↦ by simpa only [Real.norm_eq_abs] using hB m (mem_univ m))).trans_eq (by simp)

def poissonCorrelation (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (t : ℝ) : ℝ :=
  t*edgeIMean Q lam-poissonAverage (fun n ↦ iMean (finiteLaw Q hl₀ hl₁ n)) t

lemma poissonLaw_info (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (t : ℝ≥0) :
    iMean (poissonLaw Q hl₀ hl₁ t) = (t:ℝ)*edgeIMean Q lam-poissonCorrelation Q hl₀ hl₁ t := by
  obtain ⟨B,hB⟩ := bounded_iMean
  have he : iMean (poissonLaw Q hl₀ hl₁ t) = poissonAverage (fun n ↦ iMean (finiteLaw Q hl₀ hl₁ n)) t := by
    unfold iMean
    rw [show (poissonLaw Q hl₀ hl₁ t).probability = mixtureProbability (poissonPMF t)
      (fun n ↦ (finiteLaw Q hl₀ hl₁ n).probability) from rfl,
      integral_mixtureProbability _ _ (compact_integrable (continuous_info_comp continuous_subtype_val))]
    change _ = poissonAverage (fun n ↦ iMean (finiteLaw Q hl₀ hl₁ n)) t
    rw [poissonAverage_eq_tsum (fun n ↦ hB (finiteLaw Q hl₀ hl₁ n))]
    simp only [poissonPMF_real, iMean]
  rw [he, poissonCorrelation]
  ring

lemma poissonCorrelation_continuous (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) :
    Continuous (poissonCorrelation Q hl₀ hl₁) := by
  obtain ⟨B,hB⟩ := bounded_iMean
  exact (continuous_id.mul continuous_const).sub
    (continuous_poissonAverage (fun n ↦ hB (finiteLaw Q hl₀ hl₁ n)))

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory
open scoped NNReal
namespace ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Experiment

lemma poisson_fixed_edgeJ (Q : Law) {lam : ℝ} (hl₀ : 0 < lam) (hl₁ : lam < 1) (d : ℝ≥0)
    (hcrit : (d:ℝ)*lam^2 = 1) (hfixed : Q.probability = (poissonLaw Q hl₀.le hl₁ d).probability) :
    edgeJMean Q lam = lam^2*jMean Q := by
  have h := poissonLaw_symEntropy Q hl₀.le hl₁ d
  change (∫ m, symEntropy m.1 ∂((poissonLaw Q hl₀.le hl₁ d).probability).toMeasure) = _ at h
  rw [← hfixed] at h
  change jMean Q = (d:ℝ)*edgeJMean Q lam at h
  rw [h]
  calc
    _ = ((d:ℝ)*lam^2)*edgeJMean Q lam := by rw [hcrit, one_mul]
    _ = _ := by ring

lemma functional_integral {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → Vec)
    (hI : Integrable (fun m ↦ info (f m)) μ)
    (hJ : Integrable (fun m ↦ symEntropy (f m)) μ)
    (hB : Integrable (fun m ↦ correction (f m)) μ) :
    (∫ m, functional (f m) ∂μ) = 3*(∫ m, info (f m) ∂μ)-
      2*(∫ m, symEntropy (f m) ∂μ)+(4/5)*(∫ m, correction (f m) ∂μ) := by
  unfold functional
  rw [integral_add (f := fun m ↦ 3*info (f m)-2*symEntropy (f m))
    (g := fun m ↦ (4/5)*correction (f m)) ((hI.const_mul _).sub (hJ.const_mul _)) (hB.const_mul _),
    integral_sub (f := fun m ↦ 3*info (f m)) (g := fun m ↦ 2*symEntropy (f m))
      (hI.const_mul _) (hJ.const_mul _), integral_const_mul, integral_const_mul, integral_const_mul]

lemma integrated_radial (Q : Law) {lam : ℝ} (hl₀ : 0 < lam) (hl₁ : lam < 1)
    (hp : ∀ᵐ m ∂Q.probability.toMeasure, PositiveMessage m.1)
    (hJ : Integrable (fun m : Message ↦ symEntropy m.1) Q.probability.toMeasure)
    (hB : Integrable (fun m : Message ↦ correction m.1) Q.probability.toMeasure) :
    (1-lam^2)/2*Q.nu ≤ (∫ m, functional m.1 ∂Q.probability.toMeasure)-
    (lam^2)⁻¹*(∫ m, functional (edgeMessage lam m) ∂Q.probability.toMeasure) := by
  have hI : Integrable (fun m : Message ↦ info m.1) Q.probability.toMeasure :=
    compact_integrable (continuous_info_comp continuous_subtype_val)
  have hJe := edgeJ_integrable Q hl₀.le hl₁
  have hIe : Integrable (fun m : Message ↦ info (edgeMessage lam m)) Q.probability.toMeasure :=
    compact_integrable (continuous_info_comp (continuous_edgeMessage lam))
  have hBe : Integrable (fun m : Message ↦ correction (edgeMessage lam m)) Q.probability.toMeasure :=
    compact_integrable (continuous_correction_comp (continuous_edgeMessage lam)
      (fun m i ↦ (edge_positive hl₀.le hl₁ m).1 i))
  have hF : Integrable (fun m : Message ↦ functional m.1) Q.probability.toMeasure :=
    (hI.const_mul 3 |>.sub (hJ.const_mul 2)).add (hB.const_mul (4/5))
  have hFe : Integrable (fun m : Message ↦ functional (edgeMessage lam m)) Q.probability.toMeasure :=
    (hIe.const_mul 3 |>.sub (hJe.const_mul 2)).add (hBe.const_mul (4/5))
  have hrad := integral_mono_ae (μ := Q.probability.toMeasure)
    (f := fun m : Message ↦ (1-lam^2)/2*xMoment m^2)
    (g := fun m ↦ functional m.1-(lam^2)⁻¹*functional (edgeMessage lam m))
    ((compact_integrable (continuous_xMoment.pow 2)).const_mul _) (hF.sub (hFe.const_mul _))
    (hp.mono (fun m hm ↦ radial_inequality m.1 hm lam hl₀ hl₁))
  rw [integral_const_mul, integral_sub hF (hFe.const_mul _), integral_const_mul] at hrad
  exact hrad

lemma poisson_fixed_entropy_radial (Q : Law) {lam : ℝ} (hl₀ : 0 < lam) (hl₁ : lam < 1) (d : ℝ≥0)
    (hcrit : (d:ℝ)*lam^2 = 1) (hfixed : Q.probability = (poissonLaw Q hl₀.le hl₁ d).probability) :
    (1-lam^2)/2*Q.nu ≤ (8/5)*(jMean Q)^2-3*poissonCorrelation Q hl₀.le hl₁ d := by
  have hp := offspring_positive (poissonPMF d) Q hl₀.le hl₁
  have hJ := poisson_integrable_symEntropy Q hl₀.le hl₁ d
  have hB := poisson_integrable_correction Q hl₀.le hl₁ d
  change ∀ᵐ m ∂(poissonLaw Q hl₀.le hl₁ d).probability.toMeasure, PositiveMessage m.1 at hp
  rw [← hfixed] at hp hJ hB
  have hI : Integrable (fun m : Message ↦ info m.1) Q.probability.toMeasure :=
    compact_integrable (continuous_info_comp continuous_subtype_val)
  have hJe := edgeJ_integrable Q hl₀.le hl₁
  have hIe : Integrable (fun m : Message ↦ info (edgeMessage lam m)) Q.probability.toMeasure :=
    compact_integrable (continuous_info_comp (continuous_edgeMessage lam))
  have hBe : Integrable (fun m : Message ↦ correction (edgeMessage lam m)) Q.probability.toMeasure :=
    compact_integrable (continuous_correction_comp (continuous_edgeMessage lam) (fun m i ↦ (edge_positive hl₀.le hl₁ m).1 i))
  have hrad := integrated_radial Q hl₀ hl₁ hp hJ hB
  have hJid := poissonLaw_symEntropy Q hl₀.le hl₁ d
  have hBid := poissonLaw_correction Q hl₀.le hl₁ d
  have hIid := poissonLaw_info Q hl₀.le hl₁ d
  change (∫ m, symEntropy m.1 ∂((poissonLaw Q hl₀.le hl₁ d).probability).toMeasure) = _ at hJid
  change (∫ m, correction m.1 ∂((poissonLaw Q hl₀.le hl₁ d).probability).toMeasure) = _ at hBid
  change (∫ m, info m.1 ∂((poissonLaw Q hl₀.le hl₁ d).probability).toMeasure) = _ at hIid
  rw [← hfixed] at hJid hBid hIid
  have hninv : (lam^2)⁻¹ = (d:ℝ) := by
    apply mul_left_cancel₀ (ne_of_gt (sq_pos_of_pos hl₀))
    rw [mul_inv_cancel₀ (ne_of_gt (sq_pos_of_pos hl₀))]
    nlinarith [hcrit]
  have hFid := functional_integral Q.probability.toMeasure (fun m : Message ↦ m.1) hI hJ hB
  have hFeid := functional_integral Q.probability.toMeasure (edgeMessage lam) hIe hJe hBe
  rw [hFid, hFeid, hninv, hIid, hBid] at hrad
  change jMean Q = (d:ℝ)*edgeJMean Q lam at hJid
  change _ ≤ 3*((d:ℝ)*(∫ m, info (edgeMessage lam m) ∂Q.probability.toMeasure)-poissonCorrelation Q hl₀.le hl₁ d)-
    2*jMean Q+(4/5)*((d:ℝ)*(∫ m, correction (edgeMessage lam m) ∂Q.probability.toMeasure)+
      2*((d:ℝ)^2)*(edgeJMean Q lam)^2)-
    (d:ℝ)*(3*(∫ m, info (edgeMessage lam m) ∂Q.probability.toMeasure)-2*edgeJMean Q lam+
      (4/5)*(∫ m, correction (edgeMessage lam m) ∂Q.probability.toMeasure)) at hrad
  have he : ((d:ℝ)^2)*(edgeJMean Q lam)^2 = (jMean Q)^2 := by
    rw [poisson_fixed_edgeJ Q hl₀ hl₁ d hcrit hfixed]
    have hn : ((d:ℝ)^2)*lam^4 = 1 := by
      nlinarith [sq_nonneg ((d:ℝ)*lam^2-1), hcrit]
    calc
      _ = (((d:ℝ)^2)*lam^4)*(jMean Q)^2 := by ring
      _ = _ := by rw [hn]; ring
  nlinarith [hJid, he]

lemma poisson_fixed_moment_bounds (Q : Law) {lam : ℝ} (hl₀ : 0 < lam) (hl₁ : lam < 1) (d : ℝ≥0)
    (hcrit : (d:ℝ)*lam^2 = 1) (hfixed : Q.probability = (poissonLaw Q hl₀.le hl₁ d).probability) :
    0 ≤ jMean Q ∧ jMean Q ≤ Q.mu-lam*qExact lam*Q.nu ∧ cExact lam*Q.nu ≤ Q.eta := by
  have hp := offspring_positive (poissonPMF d) Q hl₀.le hl₁
  have hJ := poisson_integrable_symEntropy Q hl₀.le hl₁ d
  change ∀ᵐ m ∂(poissonLaw Q hl₀.le hl₁ d).probability.toMeasure, PositiveMessage m.1 at hp
  rw [← hfixed] at hp hJ
  exact expected_moment_bounds Q hl₀ hl₁ hp hJ (poisson_fixed_edgeJ Q hl₀ hl₁ d hcrit hfixed)

end ThreeState.TreeClauses.Positive

end 

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace ThreeState.TreeClauses.Experiment
open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive ThreeState.TreeClauses.Probability

lemma finite_iMean_succ (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (n : ℕ) :
    iMean (finiteLaw Q hl₀ hl₁ (n+1)) = iMean (finiteLaw Q hl₀ hl₁ n)+edgeIMean Q lam-
      pairCorrelation (finiteLaw Q hl₀ hl₁ n) Q lam := by
  unfold iMean edgeIMean
  rw [finiteLaw_info, finiteLaw_info, correlationEntropy_succ Q hl₀ hl₁, Nat.cast_add, Nat.cast_one]
  ring

lemma finite_iMean_zero (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) :
    iMean (finiteLaw Q hl₀ hl₁ 0) = 0 := by
  rw [iMean, finiteLaw_info]
  norm_num [correlationEntropy, normalizer, branchProduct, avg]

lemma poissonCorrelation_zero (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) :
    poissonCorrelation Q hl₀ hl₁ 0 = 0 := by
  simp [poissonCorrelation, poissonAverage_zero, finite_iMean_zero]

def poissonSlope (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (t : ℝ) : ℝ :=
  edgeIMean Q lam-(poissonAverage (fun n ↦ iMean (finiteLaw Q hl₀ hl₁ (n+1))) t-
    poissonAverage (fun n ↦ iMean (finiteLaw Q hl₀ hl₁ n)) t)

lemma hasDerivAt_poissonCorrelation (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (t : ℝ) :
    HasDerivAt (poissonCorrelation Q hl₀ hl₁) (poissonSlope Q hl₀ hl₁ t) t := by
  obtain ⟨B,hB⟩ := bounded_iMean
  unfold poissonCorrelation poissonSlope
  convert ((hasDerivAt_id t).mul_const (edgeIMean Q lam)).sub
    (hasDerivAt_poissonAverage (fun n ↦ hB (finiteLaw Q hl₀ hl₁ n)) t) using 1 <;> first | rfl | simp only [one_mul]

lemma continuous_poissonSlope (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) :
    Continuous (poissonSlope Q hl₀ hl₁) := by
  obtain ⟨B,hB⟩ := bounded_iMean
  exact continuous_const.sub
    ((continuous_poissonAverage (fun n ↦ hB (finiteLaw Q hl₀ hl₁ (n+1)))).sub
      (continuous_poissonAverage (fun n ↦ hB (finiteLaw Q hl₀ hl₁ n))))

lemma bounded_pairCorrelation (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) :
    ∃ B : ℝ, ∀ R : Law, |pairCorrelation R Q lam| ≤ B := by
  have hc := continuous_compact_integral (μ := Q.probability.toMeasure) (continuous_pairEntropy hl₀ hl₁)
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨B, fun R ↦ ?_⟩
  apply (abs_integral_le_integral_abs).trans
  exact (integral_mono (compact_integrable hc.abs) (integrable_const B)
    (fun r ↦ by simpa only [Real.norm_eq_abs] using hB r (mem_univ r))).trans_eq (by simp)

lemma poissonSlope_eq_pairCorrelation (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (t : ℝ≥0) :
    poissonSlope Q hl₀ hl₁ t = pairCorrelation (poissonLaw Q hl₀ hl₁ t) Q lam := by
  obtain ⟨B,hB⟩ := bounded_iMean
  obtain ⟨C,hC⟩ := bounded_pairCorrelation Q hl₀ hl₁
  have hi := pmf_bounded_integrable (poissonPMF t) (fun n ↦ hB (finiteLaw Q hl₀ hl₁ n))
  have hi' := pmf_bounded_integrable (poissonPMF t) (fun n ↦ hB (finiteLaw Q hl₀ hl₁ (n+1)))
  have hc := pmf_bounded_integrable (poissonPMF t) (fun n ↦ hC (finiteLaw Q hl₀ hl₁ n))
  have he : pairCorrelation (poissonLaw Q hl₀ hl₁ t) Q lam =
      ∫ n, pairCorrelation (finiteLaw Q hl₀ hl₁ n) Q lam ∂(poissonPMF t).toMeasure := by
    change (∫ r, (∫ m, pairZ lam r m*Real.log (pairZ lam r m) ∂Q.probability.toMeasure)
      ∂(mixtureProbability (poissonPMF t) (fun n ↦ (finiteLaw Q hl₀ hl₁ n).probability)).toMeasure) = _
    rw [integral_mixtureProbability _ _ (compact_integrable (continuous_compact_integral (continuous_pairEntropy hl₀ hl₁))),
      PMF.integral_eq_tsum _ _ hc]
    rfl
  rw [he, poissonSlope, poissonAverage_eq_integral (fun n ↦ hB (finiteLaw Q hl₀ hl₁ (n+1))),
    poissonAverage_eq_integral (fun n ↦ hB (finiteLaw Q hl₀ hl₁ n))]
  have he' := integral_congr_ae (μ := (poissonPMF t).toMeasure)
    (Filter.Eventually.of_forall (finite_iMean_succ Q hl₀ hl₁))
  rw [integral_sub (f := fun n ↦ iMean (finiteLaw Q hl₀ hl₁ n)+edgeIMean Q lam)
    (g := fun n ↦ pairCorrelation (finiteLaw Q hl₀ hl₁ n) Q lam) (hi.add (integrable_const _)) hc,
    integral_add (f := fun n ↦ iMean (finiteLaw Q hl₀ hl₁ n))
      (g := fun _ ↦ edgeIMean Q lam) hi (integrable_const _)] at he'
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at he'
  linarith

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory
open scoped NNReal
namespace ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Experiment

lemma poisson_increment_bound (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1)
    (d t : ℝ≥0) (htd : t ≤ d)
    (hfixed : Q.probability = (poissonLaw Q hl₀ hl₁ d).probability) :
    3*lam^4*Q.mu^2*(t:ℝ)/(1+(t:ℝ)*(lam^2*Q.mu))-
      lam^4*Q.mu*Q.nu*Real.sqrt t ≤ 3*poissonSlope Q hl₀ hl₁ t := by
  have hmu := Q.mu_nonneg
  have hnuQ := Q.nu_nonneg
  let L : ℝ := (t:ℝ)*(lam^2*Q.mu)/(1+(t:ℝ)*(lam^2*Q.mu))
  have ht : 0 ≤ (t:ℝ) := t.coe_nonneg
  have hd : 1 ≤ 1+(t:ℝ)*(lam^2*Q.mu) := by nlinarith only [mul_nonneg ht (mul_nonneg (sq_nonneg lam) hmu)]
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hproj := poisson_projection Q hl₀ hl₁ t
  have hnu : (poissonLaw Q hl₀ hl₁ t).nu ≤ Q.nu := by
    have hh := poisson_nu_mono Q hl₀ hl₁ htd
    change _ ≤ ∫ m, xMoment m^2 ∂(poissonLaw Q hl₀ hl₁ d).probability.toMeasure at hh
    rwa [← hfixed] at hh
  have hc := correlation_truncated Q (poissonLaw Q hl₀ hl₁ t) hl₀ hl₁ hnu hL hproj
  have hLu : L ≤ (t:ℝ)*(lam^2*Q.mu) := by
    dsimp only [L]
    exact div_le_self (by positivity) hd
  have hs : Real.sqrt L ≤ lam*Real.sqrt Q.mu*Real.sqrt t := by
    have he : (lam*Real.sqrt Q.mu*Real.sqrt t)^2 = (t:ℝ)*(lam^2*Q.mu) := by
      calc
        _ = lam^2*(Real.sqrt Q.mu)^2*(Real.sqrt t)^2 := by ring
        _ = _ := by rw [Real.sq_sqrt Q.mu_nonneg, Real.sq_sqrt ht]; ring
    have hp : 0 ≤ lam*Real.sqrt Q.mu*Real.sqrt t := by positivity
    nlinarith only [he, hp, Real.sq_sqrt hL, Real.sqrt_nonneg L, hLu]
  have hmul := mul_le_mul_of_nonneg_left hs (show 0 ≤ lam^3*Real.sqrt Q.mu*Q.nu by positivity)
  have heq : (lam^3*Real.sqrt Q.mu*Q.nu)*(lam*Real.sqrt Q.mu*Real.sqrt t) =
      lam^4*Q.mu*Q.nu*Real.sqrt t := by
    calc
      _ = lam^4*(Real.sqrt Q.mu)^2*Q.nu*Real.sqrt t := by ring
      _ = _ := by rw [Real.sq_sqrt Q.mu_nonneg]
  rw [heq] at hmul
  have hmain : 3*lam^2*Q.mu*L = 3*lam^4*Q.mu^2*(t:ℝ)/(1+(t:ℝ)*(lam^2*Q.mu)) := by
    dsimp only [L]; ring
  rw [hmain, ← poissonSlope_eq_pairCorrelation] at hc
  linarith only [hc, hmul]

lemma sqrt_intensity_tangent {lam t : ℝ} (hl : 0 < lam) (ht : 0 ≤ t) :
    Real.sqrt t ≤ (2*lam^2*t+1)/(2*lam*Real.sqrt 2) := by
  have hs2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hst := Real.sq_sqrt ht
  have hs2p := Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)
  apply (le_div_iff₀ (by positivity : 0 < 2*lam*Real.sqrt 2)).2
  have he : (lam*Real.sqrt 2*Real.sqrt t)^2 = 2*lam^2*t := by
    calc
      _ = lam^2*(Real.sqrt 2)^2*(Real.sqrt t)^2 := by ring
      _ = _ := by rw [hs2, hst]; ring
  nlinarith only [sq_nonneg (lam*Real.sqrt 2*Real.sqrt t-1), he]

theorem poisson_fixed_correlation_bound (Q : Law) {lam : ℝ} (hl₀ : 0 < lam) (hl₁ : lam < 1)
    (d : ℝ≥0) (hcrit : (d:ℝ)*lam^2 = 1)
    (hfixed : Q.probability = (poissonLaw Q hl₀.le hl₁ d).probability) :
    3*Q.mu^2/(2*(1+2*Q.mu/3))-lam/Real.sqrt 2*Q.mu*Q.nu ≤
      3*poissonCorrelation Q hl₀.le hl₁ d := by
  let q := 2*Q.mu/3
  let β := lam^2*Q.mu
  let A := 3*lam^4*Q.mu^2/(1+q)^2
  let B := lam^3*Q.mu*Q.nu/(2*Real.sqrt 2)
  let P : ℝ → ℝ := fun t ↦ A*((1+2*q)*t^2/2-β*t^3/3)-B*(lam^2*t^2+t)
  let P' : ℝ → ℝ := fun t ↦ A*((1+2*q)*t-β*t^2)-B*(2*lam^2*t+1)
  have hmu := Q.mu_nonneg
  have hnu := Q.nu_nonneg
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hsq : 0 < 1+q := by positivity
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have dP (t : ℝ) : HasDerivAt P (P' t) t := by
    apply ((((((hasDerivAt_id t).pow 2).const_mul (1+2*q)).div_const 2 |>.sub
      ((((hasDerivAt_id t).pow 3).const_mul β).div_const 3)).const_mul A).sub
      (((((hasDerivAt_id t).pow 2).const_mul (lam^2)).add (hasDerivAt_id t)).const_mul B)).congr_deriv
    dsimp [P']; norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one]; ring
  have hbound (t : ℝ) (ht : t ∈ Icc 0 (d:ℝ)) : P' t ≤ 3*poissonSlope Q hl₀.le hl₁ t := by
    let u : ℝ≥0 := ⟨t,ht.1⟩
    have hi := poisson_increment_bound Q hl₀.le hl₁ d u ht.2 hfixed
    have hr := mul_le_mul_of_nonneg_left (reciprocal_tangent (mul_nonneg ht.1 hβ) hq)
      (mul_nonneg hA ht.1)
    have hr' : A*((1+2*q)*t-β*t^2) ≤ 3*lam^4*Q.mu^2*t/(1+t*β) := by
      calc
        _ = A*t*(1+2*q-t*β) := by ring
        _ ≤ A*t*((1+q)^2/(1+t*β)) := hr
        _ = _ := by dsimp only [A]; field_simp
    have hs := mul_le_mul_of_nonneg_left (sqrt_intensity_tangent hl₀ ht.1)
      (show 0 ≤ lam^4*Q.mu*Q.nu by positivity)
    have hs' : lam^4*Q.mu*Q.nu*Real.sqrt t ≤ B*(2*lam^2*t+1) := by
      calc
        _ ≤ lam^4*Q.mu*Q.nu*((2*lam^2*t+1)/(2*lam*Real.sqrt 2)) := hs
        _ = _ := by dsimp only [B]; field_simp
    change 3*lam^4*Q.mu^2*t/(1+t*β)-lam^4*Q.mu*Q.nu*Real.sqrt t ≤
      3*poissonSlope Q hl₀.le hl₁ t at hi
    dsimp only [P']
    linarith only [hr', hs', hi]
  have hm : MonotoneOn (fun t ↦ 3*poissonCorrelation Q hl₀.le hl₁ t-P t) (Icc 0 (d:ℝ)) := by
    apply monotoneOn_Icc_of_hasDerivAt_nonneg
      (fun t _ ↦ ((hasDerivAt_poissonCorrelation Q hl₀.le hl₁ t).const_mul 3).sub (dP t))
    intro t ht
    exact sub_nonneg.mpr (hbound t ⟨ht.1.le,ht.2.le⟩)
  have hh := hm ⟨le_rfl,d.coe_nonneg⟩ ⟨d.coe_nonneg,le_rfl⟩ d.coe_nonneg
  have hz : P 0 = 0 := by dsimp [P]; ring
  change 3*poissonCorrelation Q hl₀.le hl₁ 0-P 0 ≤ 3*poissonCorrelation Q hl₀.le hl₁ d-P d at hh
  rw [poissonCorrelation_zero, hz] at hh
  have hd : (d:ℝ) = 1/lam^2 := (eq_div_iff (ne_of_gt (sq_pos_of_pos hl₀))).2 hcrit
  have hp : P d = 3*Q.mu^2/(2*(1+2*Q.mu/3))-lam/Real.sqrt 2*Q.mu*Q.nu := by
    dsimp only [P,A,B,β,q]
    rw [hd]
    field_simp
    ring
  rw [hp] at hh
  linarith only [hh]

end ThreeState.TreeClauses.Positive

end

end OAI
