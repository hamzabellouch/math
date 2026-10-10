import Mathlib
import OAI.Analysis.CoulombIonization.Localization.ObservationLikelihood

namespace OAI

noncomputable section

namespace CoulombObservation

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SqrtMultiplier_scope

open Filter Set
open scoped Topology NNReal

lemma sqrt_lipschitz_of_fderiv_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} (hf : Differentiable ℝ f)
    (hn : ∀ x, 0 ≤ f x) (K : ℝ≥0)
    (hb : ∀ x, ‖fderiv ℝ f x‖ ≤ 2*(K:ℝ)*Real.sqrt (f x)) :
    LipschitzWith K (fun x => Real.sqrt (f x)) := by
  have hreg (δ : ℝ) (hδ : 0 < δ) : LipschitzWith K (fun x => Real.sqrt (f x + δ)) := by
    have hg (x : E) := ((hf x).hasFDerivAt.add_const δ).sqrt (by linarith [hn x] : f x + δ ≠ 0)
    apply lipschitzWith_of_nnnorm_fderiv_le (fun x => (hg x).differentiableAt)
    intro x
    change ‖fderiv ℝ (fun x => Real.sqrt (f x+δ)) x‖ ≤ (K:ℝ)
    have hs : 0 < 2*Real.sqrt (f x+δ) := by apply mul_pos (by norm_num); exact Real.sqrt_pos.mpr (by linarith [hn x])
    rw [(hg x).fderiv, norm_smul, Real.norm_eq_abs,
      abs_of_pos (one_div_pos.mpr hs), one_div, inv_mul_eq_div, div_le_iff₀ hs]
    calc
      _ ≤ 2*(K:ℝ)*Real.sqrt (f x) := hb x
      _ ≤ (K:ℝ)*(2*Real.sqrt (f x+δ)) := by
        have hh := Real.sqrt_le_sqrt (show f x ≤ f x+δ by linarith)
        nlinarith [K.coe_nonneg]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hc : Continuous (fun δ : ℝ => dist (Real.sqrt (f x+δ)) (Real.sqrt (f y+δ))) := by fun_prop
  have ht : Tendsto (fun δ : ℝ => dist (Real.sqrt (f x+δ)) (Real.sqrt (f y+δ)))
      (𝓝[>] 0) (𝓝 (dist (Real.sqrt (f x)) (Real.sqrt (f y)))) := by
    simpa only [add_zero] using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (hreg δ hδ).dist_le_mul x y

lemma lineDeriv_sqrt_of_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x) (hx : 0 < f x) (v : E) :
    lineDeriv ℝ (fun y => Real.sqrt (f y)) x v =
      (fderiv ℝ f x v)/(2*Real.sqrt (f x)) := by
  rw [((hf.hasFDerivAt.sqrt (ne_of_gt hx)).hasLineDerivAt v).lineDeriv]
  simp only [smul_apply, smul_eq_mul]
  ring

lemma lineDeriv_sqrt_of_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (_hn : ∀ x, 0 ≤ f x) {x : E} (hx : f x = 0) (v : E) :
    lineDeriv ℝ (fun y => Real.sqrt (f y)) x v = 0 := by
  have hm : IsLocalMin (fun y => Real.sqrt (f y)) x := by
    apply Filter.Eventually.of_forall
    intro y
    change Real.sqrt (f x) ≤ Real.sqrt (f y)
    rw [hx, Real.sqrt_zero]
    exact Real.sqrt_nonneg _
  exact congrFun hm.lineDeriv_eq_zero v

end Work_SqrtMultiplier_scope

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators ContDiff

def sqrtLikelihoodLipschitzConstant {J I : Type*} [Fintype J] [Fintype I]
    (b : J → ℝ) : ℝ≥0 :=
  ⟨Real.sqrt (observationMomentConstant * (∑ j, (b j)^2) * Fintype.card I),
    Real.sqrt_nonneg _⟩

lemma arrayLikelihood_fderiv_norm {J I : Type*} [Fintype J] [Fintype I]
    (b : J → ℝ) {s : Set (J × I → ℝ)} (hs : MeasurableSet s) (x : I → ℝ) :
    ‖fderiv ℝ (arrayLikelihood b s) x‖ ≤
      (sqrtLikelihoodLipschitzConstant (I := I) b : ℝ) * Real.sqrt (arrayLikelihood b s x) := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound
  · have hC := observationMomentConstant_pos
    positivity
  intro v
  rw [arrayLikelihood_fderiv b hs, norm_neg, Real.norm_eq_abs]
  have hcs := sum_mul_sq_le_sq_mul_sq univ (fun i => v i) (fun i => arrayScore b s x i)
  have hv : (∑ i, (v i)^2) ≤ (Fintype.card I : ℝ)*‖v‖^2 := by
    calc
      _ ≤ ∑ _ : I, ‖v‖^2 := sum_le_sum (fun i _ => by
        have hh := norm_le_pi_norm v i
        simpa only [Real.norm_eq_abs, sq_abs] using (sq_le_sq₀ (abs_nonneg (v i)) (norm_nonneg v)).mpr hh)
      _ = _ := by simp
  have hsg := arrayScore_sq_one b hs x
  have hC := observationMomentConstant_pos
  have hp := arrayLikelihood_nonneg b hs x
  have hB : 0 ≤ ∑ j, (b j)^2 := sum_nonneg (fun _ _ => sq_nonneg _)
  have hr : 0 ≤ observationMomentConstant * (∑ j, (b j)^2) * Fintype.card I := by positivity
  have hh : (∑ i, v i * arrayScore b s x i)^2 ≤
      (observationMomentConstant * (∑ j, (b j)^2) * Fintype.card I) *
        arrayLikelihood b s x * ‖v‖^2 := by
    calc
      _ ≤ (∑ i, (v i)^2) * ∑ i, (arrayScore b s x i)^2 := hcs
      _ ≤ ((Fintype.card I : ℝ)*‖v‖^2) *
          (observationMomentConstant * (∑ j, (b j)^2) * arrayLikelihood b s x) :=
        mul_le_mul hv hsg (sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)
      _ = _ := by ring
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  change |∑ i, v i * arrayScore b s x i|^2 ≤
    (Real.sqrt (observationMomentConstant * (∑ j, (b j)^2) * Fintype.card I) *
      Real.sqrt (arrayLikelihood b s x) * ‖v‖)^2
  rw [mul_pow, mul_pow, Real.sq_sqrt hr, Real.sq_sqrt hp, sq_abs]
  exact hh

lemma sqrtArrayLikelihood_lipschitz {J I : Type*} [Fintype J] [Fintype I]
    (b : J → ℝ) {s : Set (J × I → ℝ)} (hs : MeasurableSet s) :
    LipschitzWith (sqrtLikelihoodLipschitzConstant (I := I) b)
      (fun x => Real.sqrt (arrayLikelihood b s x)) := by
  apply sqrt_lipschitz_of_fderiv_bound
    ((arrayLikelihood_contDiff b hs (n := 1)).differentiable one_ne_zero)
    (arrayLikelihood_nonneg b hs)
  intro x
  calc
    _ ≤ _ := arrayLikelihood_fderiv_norm b hs x
    _ ≤ _ := by
      have hz : 0 ≤ (sqrtLikelihoodLipschitzConstant (I := I) b : ℝ) *
          Real.sqrt (arrayLikelihood b s x) := by positivity
      nlinarith

lemma sqrtArrayLikelihood_lineDeriv_sq {J I : Type*} [Fintype J] [Fintype I] [DecidableEq I]
    (b : J → ℝ) {s : Set (J × I → ℝ)} (hs : MeasurableSet s) (x : I → ℝ)
    {k : ℕ} (hk : 0 < k) :
    (∑ i, (lineDeriv ℝ (fun y => Real.sqrt (arrayLikelihood b s y)) x
      (Pi.single i 1))^2) ≤
      (observationMomentConstant/4) * (k:ℝ)^5 * (∑ j, (b j)^2) *
        (arrayLikelihood b s x)^(1-(k:ℝ)⁻¹) := by
  classical
  have hp := arrayLikelihood_nonneg b hs x
  have hC := observationMomentConstant_pos
  by_cases hzero : arrayLikelihood b s x = 0
  · have hz (v : I → ℝ) : lineDeriv ℝ (fun y => Real.sqrt (arrayLikelihood b s y)) x v = 0 :=
      lineDeriv_sqrt_of_zero (arrayLikelihood_nonneg b hs) hzero v
    simp only [hz, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sum_const_zero]
    positivity
  have hpos : 0 < arrayLikelihood b s x := lt_of_le_of_ne hp (Ne.symm hzero)
  have hd := (arrayLikelihood_contDiff b hs (n := 1)).differentiable one_ne_zero x
  simp only [lineDeriv_sqrt_of_pos hd hpos, arrayLikelihood_fderiv b hs,
    Pi.single_apply, ite_mul, one_mul, zero_mul, sum_ite_eq', Finset.mem_univ, ite_true,
    div_pow, neg_sq, mul_pow, Real.sq_sqrt hp]
  rw [← sum_div]
  apply (div_le_iff₀ (by positivity : 0 < (2:ℝ)^2*arrayLikelihood b s x)).mpr
  calc
    _ ≤ observationMomentConstant * (k:ℝ)^5 * (∑ j, (b j)^2) *
        (arrayLikelihood b s x)^(2-(k:ℝ)⁻¹) := arrayScore_sq b hs x hk
    _ = (observationMomentConstant/4) * (k:ℝ)^5 * (∑ j, (b j)^2) *
        (arrayLikelihood b s x)^(1-(k:ℝ)⁻¹) * ((2:ℝ)^2*arrayLikelihood b s x) := by
      rw [show (2-(k:ℝ)⁻¹) = (1-(k:ℝ)⁻¹)+1 by ring,
        Real.rpow_add hpos, Real.rpow_one]
      ring

end CoulombObservation

end

end OAI
