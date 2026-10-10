import Mathlib
import OAI.Analysis.RCDHeat.NormalizedSubplan

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: RestrictedDensity, MeasurableDistortion, PointwiseCD, LogCosh, DensityLogMidpoint, DimensionalEntropyIntegral. -/



namespace RegularPointCoordinates

section

 

open Set Filter MeasureTheory
open scoped ENNReal
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

lemma map_restrict_of_ae_factor (ν : Measure A) (f : A → B) (hf : Measurable f)
    {P : Set A} {S : Set B} (hP : MeasurableSet P) (hS : MeasurableSet S)
    (hfactor : ∀ᵐ y ∂ν, y ∈ P ↔ f y ∈ S) :
    (ν.restrict P).map f = (ν.map f).restrict S := by
  apply Measure.ext
  intro T hT
  rw [Measure.map_apply hf hT,Measure.restrict_apply' hP,
    Measure.restrict_apply hT,Measure.map_apply hf (hT.inter hS)]
  apply measure_congr
  filter_upwards [hfactor] with y hy
  exact propext (and_congr Iff.rfl hy)

lemma rnDeriv_normalized_map_restrict
    (μ : Measure B) [SigmaFinite μ] (ν : Measure A) [IsFiniteMeasure ν]
    (f : A → B) (hf : Measurable f) (hac : ν.map f ≪ μ)
    {P : Set A} {S : Set B} (hP : MeasurableSet P) (hS : MeasurableSet S)
    (hfactor : ∀ᵐ y ∂ν, y ∈ P ↔ f y ∈ S)
    {a : ℝ≥0∞} (haf : a ≠ ∞) :
    ∀ᵐ y ∂ν.restrict P,
      ((a • ν.restrict P).map f).rnDeriv μ (f y) = a * (ν.map f).rnDeriv μ (f y) := by
  have hmap := map_restrict_of_ae_factor ν f hf hP hS hfactor
  have hr := Measure.rnDeriv_restrict (ν.map f) μ hS
  have hs := Measure.rnDeriv_smul_left_of_ne_top ((ν.map f).restrict S) μ haf
  have hall : ∀ᵐ x ∂ν.map f,
      (a • (ν.map f).restrict S).rnDeriv μ x = a * S.indicator ((ν.map f).rnDeriv μ) x := by
    filter_upwards [hac.ae_le hr,hac.ae_le hs] with x hx hz
    simpa only [Pi.smul_apply,smul_eq_mul,hx] using hz
  have hpull := ae_of_ae_map hf.aemeasurable hall
  rw [Measure.map_smul _ hf.aemeasurable,hmap]
  filter_upwards [ae_restrict_of_ae hpull,ae_restrict_of_ae hfactor,ae_restrict_mem hP] with y hy he hmem
  simpa only [Set.indicator_of_mem (he.mp hmem)] using hy

lemma rnDeriv_normalized_map_restrict_rpow
    (μ : Measure B) [SigmaFinite μ] (ν : Measure A) [IsFiniteMeasure ν]
    (f : A → B) (hf : Measurable f) (hac : ν.map f ≪ μ)
    {P : Set A} {S : Set B} (hP : MeasurableSet P) (hS : MeasurableSet S)
    (hfactor : ∀ᵐ y ∂ν, y ∈ P ↔ f y ∈ S)
    {a : ℝ≥0∞} (haf : a ≠ ∞) (r : ℝ) :
    ∀ᵐ y ∂ν.restrict P,
      (((a • ν.restrict P).map f).rnDeriv μ (f y)) ^ r =
        a ^ r * ((ν.map f).rnDeriv μ (f y)) ^ r := by
  have hh := rnDeriv_normalized_map_restrict μ ν f hf hac hP hS hfactor haf
  have hfin := ae_of_ae_map hf.aemeasurable (hac.ae_le (Measure.rnDeriv_ne_top (ν.map f) μ))
  filter_upwards [hh,ae_restrict_of_ae hfin] with y hy hz
  rw [hy,ENNReal.mul_rpow_of_ne_top haf hz]

lemma renyiIntegral_eq_inverse_density
    (μ ν : Measure B) [SigmaFinite μ] [IsFiniteMeasure ν]
    (hac : ν ≪ μ) {N : ℝ} (hN : 1 < N) :
    renyiIntegral μ ν N = ∫⁻ y, (ν.rnDeriv μ y) ^ (-(1/N)) ∂ν := by
  rw [←lintegral_rnDeriv_mul hac ((Measure.measurable_rnDeriv ν μ).pow_const _).aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [Measure.rnDeriv_ne_top ν μ] with y hy
  by_cases hz : ν.rnDeriv μ y = 0
  · have hpos : 0 < 1-1/N := by have := (div_lt_one (by linarith : 0 < N)).mpr hN; linarith
    rw [hz,ENNReal.zero_rpow_of_pos hpos,zero_mul]
  · rw [show 1-1/N = 1+(-(1/N)) by ring,ENNReal.rpow_add _ _ hz hy,ENNReal.rpow_one]

end

 
section

 

open Set MeasureTheory
open scoped ENNReal
lemma measurable_sigma (K N t : ℝ) : Measurable (sigma K N t) := by
  unfold sigma
  apply Measurable.ite
  · exact (measurableSet_eq_fun measurable_id measurable_const).union
      (MeasurableSet.const (K = 0))
  · exact measurable_const
  · apply Measurable.ite
    · exact measurableSet_le measurable_const (measurable_const.mul (measurable_id.pow_const _))
    · exact measurable_const
    · by_cases h : 0 < K <;> simp only [h,ite_true,ite_false] <;> fun_prop

lemma measurable_tau (K N t : ℝ) : Measurable (tau K N t) := by
  unfold tau
  by_cases ht : t = 0
  · simp only [ht,ite_true]; exact measurable_const
  · simp only [ht,ite_false]
    by_cases ht1 : t = 1
    · simp only [ht1,ite_true]; exact measurable_const
    · simp only [ht1,ite_false]
      exact measurable_const.mul ((measurable_sigma K N t).pow_const _)
end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.compressed_plan_pointwise_fullCD
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (plan : Measure C(Time,X)) [IsProbabilityMeasure plan]
    (hg : ∀ᵐ γ ∂plan, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (plan.map (fun γ => (γ 0,γ 1))))
    (C : ℝ≥0) (hc : ∀ t : Time,
      plan.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X) :
      ∀ (N : ℝ), (n : ℝ) ≤ N → ∀ t : Time,
        ∀ᵐ γ ∂plan,
          tau K N (1 - (t : ℝ)) (dist (γ 0) (γ 1)) *
            (ν₀.rnDeriv (hausdorff n X) (γ 0)) ^ (-(1 / N)) +
          tau K N (t : ℝ) (dist (γ 0) (γ 1)) *
            (ν₁.rnDeriv (hausdorff n X) (γ 1)) ^ (-(1 / N)) ≤
          ((plan.map (fun γ => γ t)).rnDeriv (hausdorff n X) (γ t)) ^ (-(1 / N))
 := by
  let : SeparableSpace X := hX.separable
  let : ProperSpace X := hX.proper K n hn
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  have hac (s : Time) : plan.map (fun γ => γ s) ≪ μ :=
    Measure.absolutelyContinuous_of_le_smul (hc s)
  have he := optimalPlan_endpoints ν₀ ν₁ plan hp
  intro N hN t
  have hN' : 1 < N := lt_of_lt_of_le (by exact_mod_cast (show 1 < n by omega)) hN
  let r := -(1/N)
  let F := fun γ : C(Time,X) =>
    tau K N (1-(t:ℝ)) (dist (γ 0) (γ 1)) * (ν₀.rnDeriv μ (γ 0)) ^ r +
    tau K N (t:ℝ) (dist (γ 0) (γ 1)) * (ν₁.rnDeriv μ (γ 1)) ^ r
  let G := fun γ : C(Time,X) => ((plan.map (fun γ => γ t)).rnDeriv μ (γ t)) ^ r
  have hF : Measurable F := by
    have hd : Measurable (fun γ : C(Time,X) => dist (γ 0) (γ 1)) :=
      (measurable_path_eval 0).dist (measurable_path_eval 1)
    exact (((measurable_tau K N (1-(t:ℝ))).comp hd).mul
      (((Measure.measurable_rnDeriv ν₀ μ).comp (measurable_path_eval 0)).pow_const r)).add
      (((measurable_tau K N (t:ℝ)).comp hd).mul
      (((Measure.measurable_rnDeriv ν₁ μ).comp (measurable_path_eval 1)).pow_const r))
  have hG : Measurable G :=
    ((Measure.measurable_rnDeriv _ μ).comp (measurable_path_eval t)).pow_const r
  change F ≤ᵐ[plan] G
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite hF
  intro P hP hPfin
  by_cases hz : plan P = 0
  · simp only [Measure.restrict_eq_zero.mpr hz,lintegral_zero_measure,le_refl]
  let κ := plan.restrict P
  let a := (κ univ)⁻¹
  have hκ0 : κ univ ≠ 0 := by simpa only [κ,Measure.restrict_apply_univ] using hz
  have ha : a ≠ ∞ := ENNReal.inv_ne_top.mpr hκ0
  have ha0 : a ≠ 0 := ENNReal.inv_ne_zero.mpr (measure_ne_top κ univ)
  let q := a • κ
  have hcost : transportCost (plan.map (fun γ => (γ 0,γ 1))) ≠ ∞ := by
    rw [←wassersteinSq_eq_cost hp]
    exact wassersteinSq_finite (finiteSecondMoment_of_ae_dist_le _ p hs0)
      (finiteSecondMoment_of_ae_dist_le _ p hs1)
  obtain ⟨hqprob,hqg,hqp,hq0,hq1⟩ := optimalPlan_normalized_subplan ν₀ ν₁ plan hg hp hcost
    κ Measure.restrict_le_self hκ0
  let : IsProbabilityMeasure q := hqprob
  let η₀ := q.map (fun γ => γ 0)
  let η₁ := q.map (fun γ => γ 1)
  let : IsProbabilityMeasure η₀ := inferInstance
  let : IsProbabilityMeasure η₁ := inferInstance
  have hqc (s : Time) : q.map (fun γ => γ s) ≤ ENNReal.ofReal (a.toReal*C) • μ := by
    calc
      _ ≤ a • plan.map (fun γ => γ s) := by
        rw [Measure.map_smul _ (measurable_path_eval s).aemeasurable]
        exact _root_.smul_le_smul_left a (Measure.map_mono Measure.restrict_le_self (measurable_path_eval s))
      _ ≤ a • (ENNReal.ofReal C • μ) := _root_.smul_le_smul_left a (hc s)
      _ = _ := by rw [smul_smul,ENNReal.ofReal_mul ENNReal.toReal_nonneg,ENNReal.ofReal_toReal ha]
  have hqs0 : ∀ᵐ x ∂η₀, dist x p ≤ R :=
    hs0.filter_mono (Measure.absolutelyContinuous_of_le_smul hq0).ae_le
  have hqs1 : ∀ᵐ x ∂η₁, dist x p ≤ R :=
    hs1.filter_mono (Measure.absolutelyContinuous_of_le_smul hq1).ae_le
  let D : ℝ≥0 := ⟨a.toReal*C,mul_nonneg ENNReal.toReal_nonneg C.2⟩
  have hcd := hX.compressed_optimal_plan_fullCD K n hn η₀ η₁ p hR hqs0 hqs1 q hqg hqp D hqc N hN t
  have hRN (s : Time) : ∀ᵐ γ ∂q,
      ((q.map (fun γ => γ s)).rnDeriv μ (γ s)) ^ r =
        a ^ r * ((plan.map (fun γ => γ s)).rnDeriv μ (γ s)) ^ r := by
    obtain ⟨S,hS,hfactor⟩ :=
      hX.compressed_plan_evaluation_set_factor K n hn ν₀ ν₁ p hR hs0 hs1 plan hg hp C hc s hP
    exact (rnDeriv_normalized_map_restrict_rpow μ plan _ (measurable_path_eval s) (hac s)
      hP hS hfactor ha r).filter_mono Measure.smul_absolutelyContinuous.ae_le
  have hRN0 : ∀ᵐ γ ∂q, (η₀.rnDeriv μ (γ 0)) ^ r = a ^ r * (ν₀.rnDeriv μ (γ 0)) ^ r := by
    simpa only [he.1] using hRN 0
  have hRN1 : ∀ᵐ γ ∂q, (η₁.rnDeriv μ (γ 1)) ^ r = a ^ r * (ν₁.rnDeriv μ (γ 1)) ^ r := by
    simpa only [he.2] using hRN 1
  have hleft : (∫⁻ γ,
      tau K N (1-(t:ℝ)) (dist (γ 0) (γ 1)) * (η₀.rnDeriv μ (γ 0)) ^ r +
      tau K N (t:ℝ) (dist (γ 0) (γ 1)) * (η₁.rnDeriv μ (γ 1)) ^ r ∂q) =
      a * (a ^ r * (∫⁻ γ in P, F γ ∂plan)) := by
    calc
      _ = ∫⁻ γ, a ^ r * F γ ∂q := by
        apply lintegral_congr_ae
        filter_upwards [hRN0,hRN1] with γ h0 h1
        rw [h0,h1]
        dsimp only [F]
        rw [mul_add,mul_left_comm (a^r) _ _,mul_left_comm (a^r) _ _]
      _ = _ := by rw [lintegral_smul_measure,lintegral_const_mul _ hF, smul_eq_mul]
  have hright : renyiIntegral μ (q.map (fun γ => γ t)) N =
      a * (a ^ r * (∫⁻ γ in P, G γ ∂plan)) := by
    let : IsProbabilityMeasure (q.map (fun γ => γ t)) := inferInstance
    rw [renyiIntegral_eq_inverse_density μ _ (Measure.absolutelyContinuous_of_le_smul (hqc t)) hN']
    rw [lintegral_map ((Measure.measurable_rnDeriv _ μ).pow_const r)
      (measurable_path_eval t)]
    calc
      _ = ∫⁻ γ, a ^ r * G γ ∂q := lintegral_congr_ae (hRN t)
      _ = _ := by
        rw [lintegral_smul_measure,lintegral_const_mul _ hG, smul_eq_mul]
  change (∫⁻ γ, _ ∂q) ≤ renyiIntegral μ (q.map (fun γ => γ t)) N at hcd
  rw [hleft,hright] at hcd
  have har0 : a ^ r ≠ 0 := by simp [ENNReal.rpow_eq_zero_iff,ha0,ha]
  have harf : a ^ r ≠ ∞ := by simp [ENNReal.rpow_eq_top_iff,ha0,ha]
  exact (ENNReal.mul_le_mul_iff_right har0 harf).mp
    ((ENNReal.mul_le_mul_iff_right ha0 ha).mp hcd)

end

 
section

 

open Set MeasureTheory

lemma hasDerivAt_log_cosh (x : ℝ) :
    HasDerivAt (fun y => Real.log (Real.cosh y)) (Real.sinh x / Real.cosh x) x :=
  (Real.hasDerivAt_cosh x).log (Real.cosh_pos x).ne'

lemma hasDerivAt_sinh_div_cosh (x : ℝ) :
    HasDerivAt (fun y => Real.sinh y / Real.cosh y) (1 / (Real.cosh x)^2) x := by
  have hh := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne'
  have he : (Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / Real.cosh x ^ 2 =
      1 / Real.cosh x ^ 2 := by rw [←pow_two,←pow_two,Real.cosh_sq_sub_sinh_sq]
  rw [he] at hh
  exact hh

lemma convexOn_log_cosh : ConvexOn ℝ univ (fun y => Real.log (Real.cosh y)) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg convex_univ
    (f' := fun x => Real.sinh x / Real.cosh x) (f'' := fun x => 1/(Real.cosh x)^2)
  · exact (Real.continuous_cosh.log (fun x => (Real.cosh_pos x).ne')).continuousOn
  · exact fun x _ => (hasDerivAt_log_cosh x).hasDerivWithinAt
  · exact fun x _ => (hasDerivAt_sinh_div_cosh x).hasDerivWithinAt
  · exact fun x _ => by positivity

lemma log_cosh_tangent (a b : ℝ) :
    Real.log (Real.cosh a) + (Real.sinh a / Real.cosh a)*(b-a) ≤ Real.log (Real.cosh b) := by
  rcases lt_trichotomy a b with h|h|h
  · have hh := convexOn_log_cosh.le_slope_of_hasDerivAt (mem_univ a) (mem_univ b) h
      (hasDerivAt_log_cosh a)
    rw [slope_def_field] at hh
    have hm := (le_div_iff₀ (sub_pos.mpr h)).mp hh
    linarith
  · subst b; simp
  · have hh := convexOn_log_cosh.slope_le_of_hasDerivAt (mem_univ b) (mem_univ a) h
      (hasDerivAt_log_cosh a)
    rw [slope_def_field] at hh
    have hm := (div_le_iff₀ (sub_pos.mpr h)).mp hh
    nlinarith only [hm]

lemma exp_average_cosh (u v : ℝ) :
    (Real.exp u + Real.exp v)/2 = Real.exp ((u+v)/2)*Real.cosh ((u-v)/2) := by
  rw [Real.cosh_eq, ←mul_div_assoc, mul_add, ←Real.exp_add, ←Real.exp_add]
  congr 2 <;> ring_nf

lemma log_exp_average (u v : ℝ) :
    Real.log ((Real.exp u + Real.exp v)/2) = (u+v)/2+Real.log (Real.cosh ((u-v)/2)) := by
  rw [exp_average_cosh, Real.log_mul (Real.exp_ne_zero _) (Real.cosh_pos _).ne',Real.log_exp]

lemma dimensional_log_midpoint {N : ℝ} (hN : 0 < N) (a b c q : ℝ)
    (h : Real.exp (q/N) * ((Real.exp (-a/N)+Real.exp (-b/N))/2) ≤ Real.exp (-c/N)) :
    c ≤ (a+b)/2-q-N*Real.log (Real.cosh ((a-b)/(2*N))) := by
  have hp : 0 < Real.exp (q/N)*((Real.exp (-a/N)+Real.exp (-b/N))/2) := by positivity
  have hh := Real.log_le_log hp h
  rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt (by positivity :
    0 < (Real.exp (-a/N)+Real.exp (-b/N))/2)),Real.log_exp,Real.log_exp,
    log_exp_average] at hh
  have he : (-a/N- -b/N)/2 = -((a-b)/(2*N)) := by ring
  rw [he,Real.cosh_neg] at hh
  have hm := mul_le_mul_of_nonneg_left hh hN.le
  have hN0 := hN.ne'
  field_simp at hm ⊢
  nlinarith only [hm]

end

 
section

 

open Set MeasureTheory
open scoped ENNReal

lemma density_dimensional_log_midpoint (K N θ : ℝ) (hN : 1 < N) (hθ : 0 ≤ θ)
    (A B D : ℝ≥0∞) (hA0 : A ≠ 0) (hAf : A ≠ ∞) (hB0 : B ≠ 0) (hBf : B ≠ ∞)
    (hD0 : D ≠ 0) (hDf : D ≠ ∞)
    (h : tau K N (1/2) θ * A ^ (-(1/N)) + tau K N (1/2) θ * B ^ (-(1/N)) ≤ D ^ (-(1/N))) :
    Real.log D.toReal ≤ (Real.log A.toReal+Real.log B.toReal)/2-K*θ^2/8-
      N*Real.log (Real.cosh ((Real.log A.toReal-Real.log B.toReal)/(2*N))) := by
  have hN0 : 0 < N := zero_lt_one.trans hN
  have hexp := tau_signed_gaussian_lower K N θ (1/2) hN hθ (by norm_num) (by norm_num)
  have he : K*θ^2*(1-(1/2:ℝ)^2)/(6*N) = (K*θ^2/8)/N := by ring
  rw [he] at hexp
  have hh := (add_le_add (mul_le_mul_left hexp (A^(-(1/N))))
    (mul_le_mul_left hexp (B^(-(1/N))))).trans h
  have hAr : A ^ (-(1/N)) ≠ ∞ := by simp [ENNReal.rpow_eq_top_iff,hA0,hAf]
  have hBr : B ^ (-(1/N)) ≠ ∞ := by simp [ENNReal.rpow_eq_top_iff,hB0,hBf]
  have hDr : D ^ (-(1/N)) ≠ ∞ := by simp [ENNReal.rpow_eq_top_iff,hD0,hDf]
  have hreal := ENNReal.toReal_mono hDr hh
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAr)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBr)] at hreal
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity :
      0 ≤ (1/2:ℝ)*Real.exp ((K*θ^2/8)/N)),←ENNReal.toReal_rpow] at hreal
  rw [Real.rpow_def_of_pos (ENNReal.toReal_pos hA0 hAf),
    Real.rpow_def_of_pos (ENNReal.toReal_pos hB0 hBf),
    Real.rpow_def_of_pos (ENNReal.toReal_pos hD0 hDf)] at hreal
  apply dimensional_log_midpoint hN0 (Real.log A.toReal) (Real.log B.toReal) (Real.log D.toReal) (K*θ^2/8)
  convert hreal using 1 <;> congr 1 <;> ring_nf

end

 

 

open Set Filter MeasureTheory
variable {Y : Type*} [MeasurableSpace Y]

lemma dimensional_log_midpoint_integral (π : Measure Y) [IsProbabilityMeasure π]
    (f g h q : Y → ℝ) (hf : Integrable f π) (hg : Integrable g π)
    (hh : Integrable h π) (hq : Integrable q π) {N : ℝ} (hN : 0 < N)
    (hpoint : ∀ᵐ y ∂π, h y ≤ (f y+g y)/2-q y-
      N*Real.log (Real.cosh ((f y-g y)/(2*N)))) :
    (∫ y, h y ∂π) ≤ ((∫ y, f y ∂π)+(∫ y, g y ∂π))/2-(∫ y, q y ∂π)-
      N*Real.log (Real.cosh (((∫ y, f y ∂π)-(∫ y, g y ∂π))/(2*N))) := by
  let ξ := ((∫ y, f y ∂π)-(∫ y, g y ∂π))/(2*N)
  let m := Real.sinh ξ / Real.cosh ξ
  let B := fun y => (f y+g y)/2
  let T := fun y => (f y-g y)/(2*N)
  have hB : Integrable B π := (hf.add hg).div_const 2
  have hT : Integrable T π := (hf.sub hg).div_const (2*N)
  have hTm : Integrable (fun y => m*(T y-ξ)) π := (hT.sub (integrable_const ξ)).const_mul m
  have hJ : Integrable (fun y => Real.log (Real.cosh ξ)+m*(T y-ξ)) π :=
    (integrable_const _).add hTm
  have hbound : ∀ᵐ y ∂π, h y ≤ B y-q y-N*(Real.log (Real.cosh ξ)+m*(T y-ξ)) := by
    filter_upwards [hpoint] with y hy
    have hj := mul_le_mul_of_nonneg_left (log_cosh_tangent ξ (T y)) hN.le
    dsimp only [B,T,m] at *
    linarith
  have hi := integral_mono_ae hh ((hB.sub hq).sub (hJ.const_mul N)) hbound
  have hb : (∫ y, B y ∂π) = ((∫ y, f y ∂π)+(∫ y, g y ∂π))/2 := by
    rw [show B = (fun y => (f y+g y)/2) from rfl,integral_div,integral_add hf hg]
  have ht : (∫ y, T y ∂π) = ξ := by
    rw [show T = (fun y => (f y-g y)/(2*N)) from rfl,integral_div,integral_sub hf hg]
  change (∫ y, h y ∂π) ≤ ∫ y, B y-q y-N*(Real.log (Real.cosh ξ)+m*(T y-ξ)) ∂π at hi
  rw [integral_sub (f := fun y => B y-q y) (g := fun y => N*(Real.log (Real.cosh ξ)+m*(T y-ξ))) (hB.sub hq) (hJ.const_mul N),integral_sub hB hq,integral_const_mul,
    integral_add (integrable_const _) hTm,integral_const_mul,
    integral_sub hT (integrable_const ξ),hb,ht] at hi
  simpa only [integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul,sub_self,mul_zero,add_zero,ξ] using hi


end RegularPointCoordinates

end OAI
