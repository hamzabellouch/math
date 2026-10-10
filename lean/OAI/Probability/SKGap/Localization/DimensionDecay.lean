import Mathlib
import OAI.Probability.SKGap.Localization.Magnetization

namespace OAI

section
open scoped BigOperators
namespace SKGapCutoff
open Filter Topology

noncomputable def dimensionDecay (a : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-a * Real.log (n : ℝ))

lemma dimensionDecay_tendsto (a : ℝ) (ha : 0 < a) :
    Tendsto (dimensionDecay a) atTop (nhds 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hneg := tendsto_neg_atTop_atBot.comp (hlog.const_mul_atTop ha)
  change Tendsto (fun n : ℕ => Real.exp (-a * Real.log (n : ℝ))) atTop (nhds 0)
  simpa only [Function.comp_def, neg_mul] using Real.tendsto_exp_atBot.comp hneg

lemma dimensionDecay_upper_tendsto (a : ℝ) (ha : 0 < a) :
    Tendsto (fun n => Real.sqrt (Real.exp (dimensionDecay a n) - 1) / 2)
      atTop (nhds 0) := by
  have hexp := (Real.continuous_exp.tendsto 0).comp (dimensionDecay_tendsto a ha)
  have h := ((hexp.sub (tendsto_const_nhds (x := (1 : ℝ)))).sqrt).div_const (2 : ℝ)
  simpa using h

lemma mul_exp_log_identity {n : ℕ} (hn : 0 < n) (a : ℝ) :
    (n : ℝ) * Real.exp (-(1 + a) * Real.log (n : ℝ)) = dimensionDecay a n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    _ = Real.exp (Real.log (n : ℝ)) * Real.exp (-(1 + a) * Real.log (n : ℝ)) := by
      rw [Real.exp_log hn']
    _ = _ := by rw [← Real.exp_add]; unfold dimensionDecay; congr 1; ring

lemma exp_log_div_identity {n : ℕ} (hn : 0 < n) (a : ℝ) :
    Real.exp ((1 - a) * Real.log (n : ℝ)) / (n : ℝ) = dimensionDecay a n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    _ = Real.exp ((1 - a) * Real.log (n : ℝ)) / Real.exp (Real.log (n : ℝ)) := by
      rw [Real.exp_log hn']
    _ = _ := by rw [← Real.exp_sub]; unfold dimensionDecay; congr 1; ring

lemma cutoffTime_one (n : ℕ) : cutoffTime 1 n = Real.log (n : ℝ) / 2 := by
  simp [cutoffTime]

lemma cutoffTime_one_nonneg {n : ℕ} (hn : 0 < n) : 0 ≤ cutoffTime 1 n := by
  rw [cutoffTime_one]
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hn)) (by norm_num)

lemma tendsto_one_of_error (f e : ℕ → ℝ) (he : Tendsto e atTop (nhds 0))
    (hup : ∀ᶠ n in atTop, f n ≤ 1) (hlo : ∀ᶠ n in atTop, 1 - e n ≤ f n) :
    Tendsto f atTop (nhds 1) := by
  have hz : Tendsto (fun n => 1 - f n) atTop (nhds 0) :=
    squeeze_zero' (hup.mono (fun _ h => by linarith))
      (hlo.mono (fun _ h => by linarith)) he
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hz
  simpa using h

lemma continuous_zero_cutoff_upper (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => worstContinuous (0 : Interaction n) ((1 + ε) * cutoffTime 1 n))
      atTop (nhds 0) := by
  apply squeeze_zero (fun n => worstContinuous_nonneg _ _)
    (fun n => ?_) (dimensionDecay_upper_tendsto ε hε)
  by_cases hn : 0 < n
  · have h := worstContinuous_zero_upper (n := n) ((1 + ε) * cutoffTime 1 n)
    have he : (n : ℝ) * Real.exp (-2 * ((1 + ε) * cutoffTime 1 n)) =
        dimensionDecay ε n := by
      rw [cutoffTime_one]
      convert mul_exp_log_identity hn ε using 2; congr 1; ring
    simpa only [he] using h
  · have hn0 : n = 0 := by omega
    subst n
    have hup := worstContinuous_zero_upper (n := 0) ((1 + ε) * cutoffTime 1 0)
    simp only [Nat.cast_zero, zero_mul, Real.exp_zero, sub_self, Real.sqrt_zero,
      zero_div] at hup
    exact hup.trans (by positivity)

lemma continuous_zero_cutoff_lower (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun n => worstContinuous (0 : Interaction n) ((1 - ε) * cutoffTime 1 n))
      atTop (nhds 1) := by
  apply tendsto_one_of_error _ (fun n => 8 * dimensionDecay ε n)
    (by simpa using (dimensionDecay_tendsto ε hε).const_mul 8)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact worstContinuous_le_one _ _
      (mul_nonneg (by linarith) (cutoffTime_one_nonneg hn))
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have h := worstContinuous_zero_lower hn ((1 - ε) * cutoffTime 1 n)
      (mul_nonneg (by linarith) (cutoffTime_one_nonneg hn))
    have he : 8 * Real.exp (2 * ((1 - ε) * cutoffTime 1 n)) / (n : ℝ) =
        8 * dimensionDecay ε n := by
      rw [mul_div_assoc, ← exp_log_div_identity hn ε, cutoffTime_one]
      congr 2
      ring_nf
    simpa only [he] using h

@[simp] lemma sampledInteraction_zero (n : ℕ) :
    sampledInteraction (0 : GaussianCoordinates n) = (0 : Interaction n) := by
  funext i j
  simp [sampledInteraction]

lemma disorderLaw_zero (n : ℕ) : disorderLaw 0 n =
    MeasureTheory.Measure.dirac (0 : GaussianCoordinates n) := by
  unfold disorderLaw
  simp only [zero_pow (by norm_num : 2 ≠ 0), zero_div, Real.toNNReal_zero,
    ProbabilityTheory.gaussianReal_zero_var]
  apply MeasureTheory.Measure.pi_eq
  intro s _
  simp only [MeasureTheory.Measure.dirac_apply, Set.indicator, Pi.one_apply,
    Pi.zero_apply, Set.mem_univ_pi]
  have hm : (0 : GaussianCoordinates n) ∈ Set.univ.pi s ↔
      ∀ i : Fin n × Fin n, (0 : ℝ) ∈ s i := Set.mem_univ_pi
  by_cases h : (0 : GaussianCoordinates n) ∈ Set.univ.pi s
  · simp only [ite_eq_left h]
    symm
    exact Finset.prod_eq_one (fun i _ => ite_eq_left ((hm.mp h) i))
  · simp only [ite_eq_right h]
    symm
    obtain ⟨i, hi⟩ := not_forall.mp (fun hforall => h (hm.mpr hforall))
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

lemma disorderLimit_zero_of_tendsto (F : (n : ℕ) → Interaction n → ℝ) (a : ℝ)
    (h : Tendsto (fun n => F n 0) atTop (nhds a)) : DisorderLimit 0 F a := by
  intro δ hδ
  have habs : Tendsto (fun n => |F n 0 - a|) atTop (nhds 0) := by
    simpa using (h.sub (tendsto_const_nhds (x := a))).abs
  have hlt := habs.eventually_lt_const hδ
  have he : (fun n => (disorderLaw 0 n)
      {g | δ < |F n (sampledInteraction g) - a|}) =ᶠ[atTop] (fun _ => 0) := by
    filter_upwards [hlt] with n hn
    rw [disorderLaw_zero, MeasureTheory.Measure.dirac_apply]
    simp [Set.indicator, not_lt.mpr hn.le]
  exact (tendsto_congr' he).mpr tendsto_const_nhds

lemma discrete_zero_cutoff_upper (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => worstDiscrete (0 : Interaction n)
      ⌈(1 + ε) * (n : ℝ) * cutoffTime 1 n⌉₊) atTop (nhds 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun n => worstDiscrete_nonneg _ _))
    _ (dimensionDecay_upper_tendsto ε hε)
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let k := ⌈(1 + ε) * (n : ℝ) * cutoffTime 1 n⌉₊
  have hceil : (1 + ε) * (n : ℝ) * (Real.log (n : ℝ) / 2) ≤ (k : ℝ) := by
    simpa only [k, cutoffTime_one] using Nat.le_ceil ((1 + ε) * (n : ℝ) * cutoffTime 1 n)
  have hr : -2 * (k : ℝ) / (n : ℝ) ≤ -(1 + ε) * Real.log (n : ℝ) := by
    apply (div_le_iff₀ hn').mpr
    nlinarith only [hceil]
  have hq : (n : ℝ) * Real.exp (-2 * (k : ℝ) / n) ≤ dimensionDecay ε n := by
    rw [← mul_exp_log_identity hn ε]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hr) hn'.le
  apply (worstDiscrete_zero_upper hn k).trans
  gcongr

lemma discrete_zero_cutoff_lower (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun n => worstDiscrete (0 : Interaction n)
      ⌊(1 - ε) * (n : ℝ) * cutoffTime 1 n⌋₊) atTop (nhds 1) := by
  apply tendsto_one_of_error _ (fun n => 8 * dimensionDecay (ε / 2) n)
    (by simpa using (dimensionDecay_tendsto (ε / 2) (by positivity)).const_mul 8)
    (Eventually.of_forall (fun n => worstDiscrete_le_one _ _))
  have hlarge : ∀ᶠ n : ℕ in atTop, 1 ≤ (ε / 2) * (n : ℝ) :=
    ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).const_mul_atTop
      (by positivity : 0 < ε / 2)).eventually (eventually_ge_atTop 1)
  filter_upwards [eventually_ge_atTop 2, hlarge] with n hn hlargeN
  have hn0 : 0 < n := by omega
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hs : 0 < (n : ℝ) - 1 := by linarith
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  let k := ⌊(1 - ε) * (n : ℝ) * cutoffTime 1 n⌋₊
  have hfloor : (k : ℝ) ≤ (1 - ε) * (n : ℝ) * (Real.log (n : ℝ) / 2) := by
    rw [← cutoffTime_one]
    exact Nat.floor_le (mul_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg n))
      (cutoffTime_one_nonneg hn0))
  have hc : (1 - ε) * (n : ℝ) ≤ (1 - ε / 2) * ((n : ℝ) - 1) := by
    nlinarith only [hlargeN, hε]
  have hr : 2 * (k : ℝ) / ((n : ℝ) - 1) ≤ (1 - ε / 2) * Real.log (n : ℝ) := by
    apply (div_le_iff₀ hs).mpr
    nlinarith only [hfloor, mul_le_mul_of_nonneg_right hc hlog]
  have he : 8 * Real.exp (2 * (k : ℝ) / ((n : ℝ) - 1)) / (n : ℝ) ≤
      8 * dimensionDecay (ε / 2) n := by
    rw [← exp_log_div_identity hn0 (ε / 2), ← mul_div_assoc]
    gcongr
  exact (sub_le_sub_left he 1).trans (worstDiscrete_zero_lower hn k)

theorem beta_zero_cutoff : CutoffAtRate 0 1 := by
  intro ε hε hε1
  exact ⟨disorderLimit_zero_of_tendsto _ _ (continuous_zero_cutoff_lower ε hε hε1),
    disorderLimit_zero_of_tendsto _ _ (continuous_zero_cutoff_upper ε hε),
    disorderLimit_zero_of_tendsto _ _ (discrete_zero_cutoff_lower ε hε hε1),
    disorderLimit_zero_of_tendsto _ _ (discrete_zero_cutoff_upper ε hε)⟩

end SKGapCutoff

end

end OAI
