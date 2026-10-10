import Mathlib
import OAI.Probability.SKGap.Stability.StableFields

namespace OAI

section
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction

namespace SKGap

def momentBall (R : ℝ) : Set (ProbabilityMeasure ℝ) :=
  {P | ∫⁻ x : ℝ, ENNReal.ofReal (x^2) ∂P ≤ ENNReal.ofReal R}

def momentCut (n : ℕ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => min (n:ℝ) (x^2))
    (by fun_prop) n (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (Nat.cast_nonneg _) (sq_nonneg _))]
      exact min_le_left _ _)

lemma momentCut_nonneg (n : ℕ) (x : ℝ) : 0 ≤ momentCut n x :=
  le_min (Nat.cast_nonneg _) (sq_nonneg _)

lemma momentCut_tendsto (x : ℝ) : Tendsto (fun n => momentCut n x) atTop (𝓝 (x^2)) := by
  have he : ∀ᶠ n : ℕ in atTop, momentCut n x = x^2 := by
    obtain ⟨N,hN⟩ := exists_nat_ge (x^2)
    filter_upwards [eventually_ge_atTop N] with n hn
    exact min_eq_right (hN.trans (by exact_mod_cast hn))
  exact (tendsto_congr' he).2 tendsto_const_nhds

lemma momentBall_iff (R : ℝ) (hR : 0 ≤ R) (P : ProbabilityMeasure ℝ) :
    P ∈ momentBall R ↔ ∀ n, (∫ x, momentCut n x ∂P) ≤ R := by
  constructor
  · intro h n
    apply (ENNReal.ofReal_le_ofReal_iff hR).mp
    rw [ofReal_integral_eq_lintegral_ofReal ((momentCut n).integrable (μ := (P : Measure ℝ)))
      (ae_of_all _ (momentCut_nonneg n))]
    exact (lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (min_le_right _ _))).trans h
  · intro h
    have ht : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (momentCut n x) ∂P) atTop
        (𝓝 (∫⁻ x : ℝ, ENNReal.ofReal (x^2) ∂P)) := by
      apply lintegral_tendsto_of_tendsto_of_monotone
      · intro n; exact (ENNReal.continuous_ofReal.comp (momentCut n).continuous).aemeasurable
      · exact ae_of_all _ (fun x a b hab => ENNReal.ofReal_le_ofReal (min_le_min_right _ (by exact_mod_cast hab)))
      · exact ae_of_all _ (fun x => ENNReal.continuous_ofReal.continuousAt.tendsto.comp (momentCut_tendsto x))
    apply le_of_tendsto ht
    exact Eventually.of_forall (fun n => by
      rw [← ofReal_integral_eq_lintegral_ofReal ((momentCut n).integrable (μ := (P : Measure ℝ))) (ae_of_all _ (momentCut_nonneg n))]
      exact ENNReal.ofReal_le_ofReal (h n))

lemma isClosed_momentBall (R : ℝ) : IsClosed (momentBall R) := by
  have he : momentBall R = momentBall (max 0 R) := by simp only [momentBall, ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_right (show (0:ℝ≥0∞) ≤ ENNReal.ofReal R from bot_le)]
  rw [he]
  have hR : 0 ≤ max 0 R := le_max_left _ _
  have hes : momentBall (max 0 R) = ⋂ n, {P : ProbabilityMeasure ℝ | (∫ x, momentCut n x ∂P) ≤ max 0 R} := by
    ext P; simp only [mem_iInter, mem_ofPred_eq]; exact momentBall_iff _ hR P
  rw [hes]
  exact isClosed_iInter (fun n => isClosed_le (ProbabilityMeasure.continuous_integral_boundedContinuousFunction _) continuous_const)

lemma momentBall_integrable {R : ℝ} {P : ProbabilityMeasure ℝ} (hP : P ∈ momentBall R) :
    Integrable (fun x : ℝ => x^2) (P : Measure ℝ) := by
  refine ⟨(by fun_prop), ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun x : ℝ => sq_nonneg x))]
  exact lt_of_le_of_lt hP ENNReal.ofReal_lt_top

lemma momentBall_integral_le {R : ℝ} (hR : 0 ≤ R) {P : ProbabilityMeasure ℝ} (hP : P ∈ momentBall R) :
    (∫ x : ℝ, x^2 ∂P) ≤ R := by
  apply (ENNReal.ofReal_le_ofReal_iff hR).mp
  rw [ofReal_integral_eq_lintegral_ofReal (momentBall_integrable hP) (ae_of_all _ (fun x : ℝ => sq_nonneg x))]
  exact hP

lemma mem_momentBall {R : ℝ} {P : ProbabilityMeasure ℝ}
    (hi : Integrable (fun x : ℝ => x^2) (P : Measure ℝ)) (hb : (∫ x : ℝ, x^2 ∂P) ≤ R) :
    P ∈ momentBall R := by
  change (∫⁻ x : ℝ, ENNReal.ofReal (x^2) ∂P) ≤ ENNReal.ofReal R
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun x : ℝ => sq_nonneg x))]
  exact ENNReal.ofReal_le_ofReal hb

lemma momentBall_tail {R K : ℝ} (hK : 0 < K) {P : ProbabilityMeasure ℝ}
    (hP : P ∈ momentBall R) :
    (P : Measure ℝ) (Metric.closedBall 0 K)ᶜ ≤ ENNReal.ofReal R / ENNReal.ofReal (K^2) := by
  have hmeas : Measurable (fun x : ℝ => ENNReal.ofReal (x^2)) := by fun_prop
  calc
    _ ≤ (P : Measure ℝ) {x : ℝ | ENNReal.ofReal (K^2) ≤ ENNReal.ofReal (x^2)} := by
      apply measure_mono
      intro x hx
      have hx' : K < |x| := by simpa only [mem_compl_iff, Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] using hx
      apply ENNReal.ofReal_le_ofReal
      nlinarith [sq_abs x]
    _ ≤ (∫⁻ x : ℝ, ENNReal.ofReal (x^2) ∂P) / ENNReal.ofReal (K^2) :=
      meas_ge_le_lintegral_div hmeas.aemeasurable
        (ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_pos hK)) ENNReal.ofReal_ne_top
    _ ≤ _ := ENNReal.div_le_div_right hP _

lemma isTight_momentBall (R : ℝ) :
    IsTightMeasureSet {((P : ProbabilityMeasure ℝ) : Measure ℝ) | P ∈ momentBall R} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨δ, _, hδ, hδε⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
  have hd : 0 < δ := ENNReal.ofReal_pos.mp hδ
  let K := max 0 R / δ + 1
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨Metric.closedBall 0 K, isCompact_closedBall _ _, ?_⟩
  rintro _ ⟨P,hP,rfl⟩
  calc
    _ ≤ ENNReal.ofReal R / ENNReal.ofReal (K^2) := momentBall_tail hK hP
    _ ≤ ENNReal.ofReal δ := by
      rw [← ENNReal.ofReal_div_of_pos (sq_pos_of_pos hK)]
      apply ENNReal.ofReal_le_ofReal
      rw [div_le_iff₀ (sq_pos_of_pos hK)]
      have hK1 : 1 ≤ K := by dsimp [K]; linarith [div_nonneg (le_max_left 0 R) hd.le]
      have he : δ * (K-1) = max 0 R := by dsimp [K]; field_simp; ring
      have hab : 0 ≤ (K-1)^2 := sq_nonneg _
      nlinarith [le_max_right 0 R, mul_nonneg hd.le hab]
    _ ≤ ε := hδε.le

lemma isCompact_momentBall (R : ℝ) : IsCompact (momentBall R) := by
  have h := isCompact_closure_of_isTightMeasureSet (isTight_momentBall R)
  simpa only [(isClosed_momentBall R).closure_eq] using h

lemma integrable_of_linear_bound {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : Integrable (fun x : ℝ => x^2) P) {f : ℝ → ℝ} (hf : Continuous f)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, |f x| ≤ C*(1+|x|)) : Integrable f P := by
  apply (((integrable_const (2:ℝ)).add hP).const_mul C).mono' hf.aestronglyMeasurable
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs]
    have hx : |x| ≤ 1+x^2 := by nlinarith [sq_nonneg (|x|-1), sq_abs x]
    exact (hb x).trans (mul_le_mul_of_nonneg_left (by change 1+|x| ≤ 2+x^2; linarith) hC))

def momentClip {f : ℝ → ℝ} (hf : Continuous f) (n : ℕ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => max (-(n:ℝ)) (min (n:ℝ) (f x)))
    (by fun_prop) n (fun x => by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨le_max_left _ _, max_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (min_le_left _ _)⟩)

lemma momentClip_error {n : ℕ} (hn : 0 < n) (x : ℝ) :
    |x - max (-(n:ℝ)) (min (n:ℝ) x)| ≤ x^2/(n:ℝ) := by
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  rw [le_div_iff₀ hn']
  by_cases hx : x ≤ (n:ℝ)
  · rw [min_eq_right hx]
    by_cases hx' : -(n:ℝ) ≤ x
    · rw [max_eq_right hx', sub_self, abs_zero, zero_mul]; positivity
    · rw [max_eq_left (le_of_not_ge hx'), abs_of_nonpos (by linarith)]
      nlinarith [sq_nonneg (x+(n:ℝ))]
  · rw [min_eq_left (le_of_not_ge hx), max_eq_right (by linarith), abs_of_nonneg (by linarith)]
    nlinarith [sq_nonneg (x-(n:ℝ))]

lemma moment_integral_approx {R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    {f : ℝ → ℝ} (hf : Continuous f) (hb : ∀ x, |f x| ≤ C*(1+|x|))
    {n : ℕ} (hn : 0 < n) {P : ProbabilityMeasure ℝ} (hP : P ∈ momentBall R) :
    |(∫ x, f x ∂P) - (∫ x, momentClip hf n x ∂P)| ≤ 2*C^2*(1+R)/(n:ℝ) := by
  have hpi := momentBall_integrable hP
  have hfi := integrable_of_linear_bound hpi hf hC hb
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  rw [← integral_sub hfi ((momentClip hf n).integrable (μ := (P : Measure ℝ))), ← Real.norm_eq_abs]
  have hbound : ∀ x, ‖f x - momentClip hf n x‖ ≤ (2*C^2/(n:ℝ))*(1+x^2) := by
    intro x
    rw [Real.norm_eq_abs]
    change |f x - max (-(n:ℝ)) (min (n:ℝ) (f x))| ≤ _
    apply (momentClip_error hn (f x)).trans
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hn']
    have hsq : (f x)^2 ≤ (C*(1+|x|))^2 := by
      have h := mul_self_le_mul_self (abs_nonneg (f x)) (hb x)
      simpa only [← sq, sq_abs] using h
    have hs : (1+|x|)^2 ≤ 2*(1+x^2) := by nlinarith [sq_nonneg (|x|-1), sq_abs x]
    calc
      _ ≤ (C*(1+|x|))^2 := hsq
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg C)]
  have he := norm_integral_le_of_norm_le
    (((integrable_const (1:ℝ)).add hpi).const_mul (2*C^2/(n:ℝ))) (ae_of_all _ hbound)
  calc
    _ ≤ ∫ x, (2*C^2/(n:ℝ))*(1+x^2) ∂P := he
    _ = (2*C^2/(n:ℝ))*(1+∫ x : ℝ, x^2 ∂P) := by
      rw [integral_const_mul, integral_add (integrable_const 1) hpi]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    _ ≤ (2*C^2/(n:ℝ))*(1+R) := mul_le_mul_of_nonneg_left
      (by linarith [momentBall_integral_le hR hP]) (by positivity)
    _ = _ := by ring

lemma continuousOn_integral_of_linear_bound {R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    {f : ℝ → ℝ} (hf : Continuous f) (hb : ∀ x, |f x| ≤ C*(1+|x|)) :
    ContinuousOn (fun P : ProbabilityMeasure ℝ => ∫ x, f x ∂P) (momentBall R) := by
  have ht : TendstoUniformlyOn (fun n (P : ProbabilityMeasure ℝ) => ∫ x, momentClip hf n x ∂P)
      (fun P : ProbabilityMeasure ℝ => ∫ x, f x ∂P) atTop (momentBall R) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have he := (tendsto_const_div_atTop_nhds_zero_nat (2*C^2*(1+R))).eventually (gt_mem_nhds hε)
    filter_upwards [he, eventually_gt_atTop 0] with n hn hn0
    intro P hP
    rw [Real.dist_eq]
    exact (moment_integral_approx hR hC hf hb hn0 hP).trans_lt hn
  apply ht.continuousOn
  exact Frequently.of_forall (fun n => (ProbabilityMeasure.continuous_integral_boundedContinuousFunction (momentClip hf n)).continuousOn)

end SKGap

namespace SKGap
open Filter
open scoped Topology

lemma gaussian_affine_hasLaw (d : ℝ) (s : ℝ≥0) :
    HasLaw (fun x : ℝ => d + sqrt s*x) (gaussianReal d s) (gaussianReal 0 1) := by
  have h := gaussianReal_const_add (gaussianReal_const_mul
    (HasLaw.id (μ := gaussianReal 0 1)) (sqrt s)) d
  have hv : (NNReal.mk ((sqrt (s:ℝ))^2) (sq_nonneg _) : ℝ≥0) = s := by
    ext
    exact sq_sqrt s.coe_nonneg
  simp only [id_eq, mul_zero, zero_add, mul_one] at h
  rw [hv] at h
  exact h

def gaussianAverage (f : ℝ → ℝ) (d s : ℝ) : ℝ := ∫ x, f (d + sqrt s*x) ∂gaussianReal 0 1

lemma gaussianAverage_eq_integral {f : ℝ → ℝ} (hf : Continuous f) (d : ℝ) {s : ℝ}
    (hs : 0 ≤ s) : gaussianAverage f d s = ∫ y, f y ∂gaussianReal d s.toNNReal := by
  have h := (gaussian_affine_hasLaw d s.toNNReal).integral_comp hf.aestronglyMeasurable
  simpa only [gaussianAverage, Function.comp_def, Real.coe_toNNReal s hs] using h

lemma integrable_gaussian_comp_of_bound {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) (d s : ℝ) :
    Integrable (fun x => f (d+sqrt s*x)) (gaussianReal 0 1) :=
  Integrable.of_bound (by fun_prop) C (ae_of_all _ (fun x => hC _))

lemma continuous_gaussianAverage {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) : Continuous (fun p : ℝ×ℝ => gaussianAverage f p.1 p.2) := by
  apply continuous_of_dominated (bound := fun _ => C)
  · intro p
    exact (by fun_prop : Continuous (fun x : ℝ => f (p.1+sqrt p.2*x))).aestronglyMeasurable
  · intro p
    exact ae_of_all _ (fun x => hC _)
  · exact integrable_const _
  · exact ae_of_all _ (fun x => by fun_prop)
end SKGap

namespace SKGap
@[fun_prop] theorem continuous_tanh : Continuous tanh :=
  continuous_iff_continuousAt.mpr (fun y => (hasDerivAt_tanh y).continuousAt)
end SKGap

namespace SKGap

abbrev ScalarPoint := ProbabilityMeasure ℝ × (ℝ × ℝ)

def scalarM (P : ProbabilityMeasure ℝ) : ℝ := ∫ x, tanh x ∂P

def scalarQMoment (P : ProbabilityMeasure ℝ) : ℝ := ∫ x, tanh x^2 ∂P

def scalarD (j : ℝ) (p : ScalarPoint) : ℝ := p.2.1+j*scalarM p.1

def scalarS (j : ℝ) (p : ScalarPoint) : ℝ := p.2.1+p.2.2^2+j*scalarQMoment p.1

def scalarA (j : ℝ) (p : ScalarPoint) : ℝ :=
  (∫ x, x*tanh x ∂p.1) - scalarD j p*scalarM p.1

def scalarPsi (j : ℝ) (p : ScalarPoint) : ℝ :=
  j*(scalarA j p-scalarS j p*(1-scalarQMoment p.1))^2 /
    (2*scalarS j p*(scalarS j p+j*scalarQMoment p.1))

def scalarMomentDomain (R : ℝ) : Set ScalarPoint := momentBall R ×ˢ univ

lemma continuous_scalarM : Continuous scalarM := by
  let f : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup tanh continuous_tanh 1
    (fun x => by simpa only [Real.norm_eq_abs] using (abs_tanh_lt_one x).le)
  exact ProbabilityMeasure.continuous_integral_boundedContinuousFunction f

lemma continuous_scalarQMoment : Continuous scalarQMoment := by
  let f : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup (fun x => tanh x^2) (by fun_prop) 1
    (fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (tanh x))] using (tanh_sq_lt_one x).le)
  exact ProbabilityMeasure.continuous_integral_boundedContinuousFunction f

lemma continuous_scalarD (j : ℝ) : Continuous (scalarD j) :=
  (continuous_fst.comp continuous_snd).add (continuous_const.mul (continuous_scalarM.comp continuous_fst))

lemma continuous_scalarS (j : ℝ) : Continuous (scalarS j) :=
  ((continuous_fst.comp continuous_snd).add ((continuous_snd.comp continuous_snd).pow 2)).add
    (continuous_const.mul (continuous_scalarQMoment.comp continuous_fst))

lemma scalarQMoment_bounds (P : ProbabilityMeasure ℝ) : 0 ≤ scalarQMoment P ∧ scalarQMoment P ≤ 1 := by
  refine ⟨integral_nonneg (fun x => sq_nonneg _), ?_⟩
  have hi : Integrable (fun x : ℝ => tanh x^2) (P : Measure ℝ) := Integrable.of_bound
    (by fun_prop) 1 (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (tanh x))] using (tanh_sq_lt_one x).le))
  have h := integral_mono hi (integrable_const (1:ℝ)) (fun x => (tanh_sq_lt_one x).le)
  simpa only [scalarQMoment, integral_const, probReal_univ, smul_eq_mul, one_mul] using h

lemma scalarM_bounds (P : ProbabilityMeasure ℝ) : |scalarM P| ≤ 1 := by
  have h := norm_integral_le_of_norm_le (μ := (P : Measure ℝ)) (f := tanh) (integrable_const (1:ℝ))
    (ae_of_all _ (fun x : ℝ => by simpa only [Real.norm_eq_abs] using (abs_tanh_lt_one x).le))
  simpa only [scalarM, Real.norm_eq_abs, integral_const, probReal_univ, smul_eq_mul, one_mul] using h

lemma continuousOn_scalarA {R : ℝ} (hR : 0 ≤ R) (j : ℝ) :
    ContinuousOn (scalarA j) (scalarMomentDomain R) := by
  have hi := continuousOn_integral_of_linear_bound hR (C := 1) zero_le_one
    (show Continuous (fun x : ℝ => x*tanh x) by fun_prop) (fun x => by
      rw [abs_mul, one_mul]
      have hm := mul_le_mul_of_nonneg_left (abs_tanh_lt_one x).le (abs_nonneg x)
      linarith)
  have hc : ContinuousOn (fun p : ScalarPoint => ∫ x, x*tanh x ∂p.1) (scalarMomentDomain R) :=
    hi.comp continuous_fst.continuousOn (fun p hp => hp.1)
  exact hc.sub ((continuous_scalarD j).mul (continuous_scalarM.comp continuous_fst)).continuousOn

lemma scalarA_eq {R : ℝ} {p : ScalarPoint} (hp : p ∈ scalarMomentDomain R) (j : ℝ) :
    scalarA j p = ∫ x, (x-scalarD j p)*tanh x ∂p.1 := by
  have hi := integrable_of_linear_bound (momentBall_integrable hp.1)
    (show Continuous (fun x : ℝ => x*tanh x) by fun_prop) zero_le_one (fun x => by
      rw [abs_mul, one_mul]
      have hm := mul_le_mul_of_nonneg_left (abs_tanh_lt_one x).le (abs_nonneg x)
      linarith)
  have ht : Integrable tanh (p.1 : Measure ℝ) := Integrable.of_bound
    continuous_tanh.aestronglyMeasurable 1 (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using (abs_tanh_lt_one x).le))
  simp_rw [sub_mul]
  rw [integral_sub hi (ht.const_mul _), integral_const_mul]
  rfl

lemma continuousOn_scalarPsi {R : ℝ} (hR : 0 ≤ R) (j : ℝ) :
    ContinuousOn (scalarPsi j) (scalarMomentDomain R ∩ {p | scalarS j p ≠ 0 ∧ scalarS j p+j*scalarQMoment p.1 ≠ 0}) := by
  unfold scalarPsi
  apply ContinuousOn.div
  · exact continuousOn_const.mul ((((continuousOn_scalarA hR j).mono inter_subset_left).sub
      ((continuous_scalarS j).continuousOn.mul (continuousOn_const.sub (continuous_scalarQMoment.comp continuous_fst).continuousOn))).pow 2)
  · exact (continuous_const.mul (continuous_scalarS j)).continuousOn.mul
      ((continuous_scalarS j).add (continuous_const.mul (continuous_scalarQMoment.comp continuous_fst))).continuousOn
  · intro p hp; exact mul_ne_zero (mul_ne_zero (by norm_num) hp.2.1) hp.2.2

def scalarLogMoment (f : ℝ →ᵇ ℝ) (d s : ℝ) : ℝ :=
  log (gaussianAverage (fun x => exp (f x)) d s)

lemma continuous_scalarLogMoment (f : ℝ →ᵇ ℝ) :
    Continuous (fun p : ℝ×ℝ => scalarLogMoment f p.1 p.2) := by
  have hc := continuous_gaussianAverage (continuous_exp.comp f.continuous)
    (C := exp ‖f‖) (fun x => by
      simp only [Function.comp_def]; rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      exact exp_le_exp.mpr ((le_abs_self _).trans (f.norm_coe_le_norm x)))
  apply hc.log
  intro p
  apply ne_of_gt
  exact integral_pos_iff_support_of_nonneg (fun _ => (exp_pos _).le)
    (integrable_gaussian_comp_of_bound (continuous_exp.comp f.continuous)
      (C := exp ‖f‖) (fun x => by
        simp only [Function.comp_def]; rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
        exact exp_le_exp.mpr ((le_abs_self _).trans (f.norm_coe_le_norm x))) p.1 p.2) |>.mpr
      (by simp [Function.support, (exp_pos _).ne'])

lemma scalarLogMoment_eq (f : ℝ →ᵇ ℝ) (d : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    scalarLogMoment f d s = log (∫ x, exp (f x) ∂gaussianReal d s.toNNReal) := by
  unfold scalarLogMoment
  congr 1
  exact gaussianAverage_eq_integral (continuous_exp.comp f.continuous) d hs

end SKGap
end
end

end OAI
