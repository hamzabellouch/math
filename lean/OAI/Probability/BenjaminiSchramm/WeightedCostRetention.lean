import OAI.Probability.BenjaminiSchramm.PeakSprinklingCost
import OAI.Probability.BenjaminiSchramm.RestrictedMomentHolder

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal BigOperators Topology

namespace Percolation.BenjaminiSchramm

lemma weighted_cost_retains_half {ι Ω : Type*} [MeasurableSpace Ω]
    (I : Finset ι) (μ : ι → Measure Ω) (w : ι → ℝ≥0∞)
    (A : ι → Set Ω) (hA : ∀ i ∈ I, MeasurableSet (A i))
    (Z : ι → Ω → ℝ≥0∞) (hZ : ∀ i ∈ I, Measurable (Z i))
    (t : ℝ) (ht : 0 < t)
    (hP : (∑ i ∈ I, w i*μ i (A i)) < ⊤)
    (hcost : (∑ i ∈ I, w i*(∫⁻ ω in A i, Z i ω ∂μ i)) ≤
      (∑ i ∈ I, w i*μ i (A i))*ENNReal.ofReal (t/2)) :
    (∑ i ∈ I, w i*μ i (A i))/2 ≤
      ∑ i ∈ I, w i*μ i (A i ∩ {ω | Z i ω ≤ ENNReal.ofReal t}) := by
  let P := ∑ i ∈ I, w i*μ i (A i)
  let B := ∑ i ∈ I, w i*μ i (A i ∩ {ω | ENNReal.ofReal t < Z i ω})
  let Q := ∑ i ∈ I, w i*μ i (A i ∩ {ω | Z i ω ≤ ENNReal.ofReal t})
  have hBQ : B ≤ P ∧ Q ≤ P := by
    constructor <;> apply Finset.sum_le_sum <;> intro i hi
    all_goals exact mul_le_mul' le_rfl (measure_mono Set.inter_subset_left)
  have hB : B ≠ ⊤ := ne_top_of_le_ne_top hP.ne hBQ.1
  have hQ : Q ≠ ⊤ := ne_top_of_le_ne_top hP.ne hBQ.2
  have hsum : Q+B=P := by
    dsimp [P,Q,B]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [←mul_add]
    congr 1
    have hmeas : MeasurableSet {ω | ENNReal.ofReal t < Z i ω} := (measurable_const.lt (hZ i hi)).setOf
    have hdis : Disjoint (A i ∩ {ω | Z i ω ≤ ENNReal.ofReal t})
        (A i ∩ {ω | ENNReal.ofReal t < Z i ω}) := by
      apply Set.disjoint_left.mpr
      intro ω hω hω'
      exact (not_lt_of_ge (show Z i ω ≤ ENNReal.ofReal t from hω.2)) hω'.2
    rw [←measure_union hdis ((hA i hi).inter hmeas)]
    congr 1
    ext ω
    simp only [Set.mem_union,Set.mem_inter_iff,Set.mem_ofPred_eq]
    constructor
    · exact fun h => h.elim And.left And.left
    · intro h
      rcases le_or_gt (Z i ω) (ENNReal.ofReal t) with hh | hh
      · exact Or.inl ⟨h,hh⟩
      · exact Or.inr ⟨h,hh⟩
  have hmarkov : ENNReal.ofReal t*B ≤ P*ENNReal.ofReal (t/2) := by
    apply le_trans _ hcost
    dsimp [B]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    let S := A i ∩ {ω | ENNReal.ofReal t < Z i ω}
    have hm : MeasurableSet S := (hA i hi).inter (measurable_const.lt (hZ i hi)).setOf
    have hh : ENNReal.ofReal t*μ i S ≤ ∫⁻ ω in A i, Z i ω ∂μ i := by
      calc
        _ = ∫⁻ ω, ENNReal.ofReal t*S.indicator (fun _ => (1 : ℝ≥0∞)) ω ∂μ i := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact congrArg (fun b => ENNReal.ofReal t*b) (lintegral_indicator_fun_one hm).symm
        _ ≤ ∫⁻ ω, (A i).indicator (Z i) ω ∂μ i := by
          apply lintegral_mono
          intro ω
          change ENNReal.ofReal t*S.indicator (fun _ => (1 : ℝ≥0∞)) ω ≤ (A i).indicator (Z i) ω
          by_cases hω : ω ∈ S
          · rw [Set.indicator_of_mem hω (fun _ => (1 : ℝ≥0∞)),Set.indicator_of_mem hω.1 (Z i),mul_one]
            exact hω.2.le
          · rw [Set.indicator_of_notMem hω (fun _ => (1 : ℝ≥0∞)),mul_zero]
            exact bot_le
        _ = _ := lintegral_indicator (hA i hi) (Z i)
    exact (show ENNReal.ofReal t*(w i*μ i S)=(w i)*(ENNReal.ofReal t*μ i S) by ac_rfl).le.trans
      (mul_le_mul' le_rfl hh)
  have hre := ENNReal.toReal_mono
    (ENNReal.mul_ne_top hP.ne ENNReal.ofReal_ne_top) hmarkov
  rw [ENNReal.toReal_mul,ENNReal.toReal_mul,ENNReal.toReal_ofReal ht.le,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ t/2)] at hre
  have hb : B.toReal ≤ P.toReal/2 := by nlinarith
  have hsumreal : Q.toReal+B.toReal=P.toReal := by
    rw [←ENNReal.toReal_add hQ hB,hsum]
  change P/2 ≤ Q
  apply (ENNReal.toReal_le_toReal (ENNReal.div_ne_top hP.ne (by norm_num)) hQ).mp
  rw [ENNReal.toReal_div,ENNReal.toReal_ofNat]
  linarith

lemma sublinear_cost_eventually_small (F : ℕ → ℝ)
    (hF : Tendsto (fun n : ℕ => F n/(n : ℝ)) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) : ∀ᶠ n : ℕ in atTop, F n ≤ ε*n := by
  filter_upwards [hF.eventually (gt_mem_nhds hε),eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact ((div_lt_iff₀ hn0).mp hn).le

theorem weighted_cost_retains_half_eventually {ι Ω : Type*} [MeasurableSpace Ω]
    (I : Finset ι) (μ : ι → Measure Ω) (w : ι → ℝ≥0∞)
    (A : ℕ → ι → Set Ω) (hA : ∀ n i, i ∈ I → MeasurableSet (A n i))
    (Z : ℕ → ι → Ω → ℝ≥0∞) (hZ : ∀ n i, i ∈ I → Measurable (Z n i))
    (F : ℕ → ℝ) (hF : Tendsto (fun n : ℕ => F n/(n : ℝ)) atTop (𝓝 0))
    (hP : ∀ n, (∑ i ∈ I, w i*μ i (A n i)) < ⊤)
    (hcost : ∀ n, (∑ i ∈ I, w i*(∫⁻ ω in A n i, Z n i ω ∂μ i)) ≤
      (∑ i ∈ I, w i*μ i (A n i))*ENNReal.ofReal (F n))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (∑ i ∈ I, w i*μ i (A n i))/2 ≤
      ∑ i ∈ I, w i*μ i (A n i ∩ {ω | Z n i ω ≤ ENNReal.ofReal (ε*n)}) := by
  filter_upwards [sublinear_cost_eventually_small F hF (ε/2) (by positivity),
    eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  apply weighted_cost_retains_half I μ w (A n) (hA n) (Z n) (hZ n)
    (ε*n) (mul_pos hε hn0) (hP n)
  apply (hcost n).trans
  apply mul_le_mul' le_rfl
  exact ENNReal.ofReal_le_ofReal (by nlinarith [hn])

lemma retained_peak_exponential_bound (P Q T : ℝ≥0∞) (c b ε n : ℝ)
    (hP : ENNReal.ofReal (c*Real.exp (-b*n)) ≤ P)
    (hhalf : P/2 ≤ Q) (htransfer : ENNReal.ofReal (Real.exp (-ε*n))*Q ≤ T) :
    ENNReal.ofReal ((c/2)*Real.exp (-(b+ε)*n)) ≤ T := by
  have he : (c/2)*Real.exp (-(b+ε)*n)=
      Real.exp (-ε*n)*((c*Real.exp (-b*n))/2) := by
    have hexp : Real.exp (-(b+ε)*n)=Real.exp (-ε*n)*Real.exp (-b*n) := by
      rw [←Real.exp_add]
      congr 1
      ring
    rw [hexp]
    ring
  calc
    _ = ENNReal.ofReal (Real.exp (-ε*n))*(ENNReal.ofReal (c*Real.exp (-b*n))/2) := by
      rw [he,ENNReal.ofReal_mul (Real.exp_nonneg _),ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ)<2)]
      norm_num
    _ ≤ ENNReal.ofReal (Real.exp (-ε*n))*(P/2) := mul_le_mul' le_rfl (ENNReal.div_le_div_right hP 2)
    _ ≤ ENNReal.ofReal (Real.exp (-ε*n))*Q := mul_le_mul' le_rfl hhalf
    _ ≤ T := htransfer

end Percolation.BenjaminiSchramm

end

end OAI
