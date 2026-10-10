import Mathlib
import OAI.Analysis.RCDHeat.CompactSquareIntegrability

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: CouplingRepair, RetainedCoupling, RetainedConvergence, CouplingCost, DensityCouplingRecovery, CompactSobolevDescent. -/



namespace RegularPointCoordinates

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
variable {X : Type*} [MeasurableSpace X]
 

 theorem coupling_repair {η ν : Measure X} [IsProbabilityMeasure η] [IsProbabilityMeasure ν]
    {π τ : Measure (X×X)} [IsFiniteMeasure π] [IsFiniteMeasure τ]
    (hπ₁ : π.map Prod.snd = ν)
    (hτ : τ ≤ π) (hη : τ.map Prod.fst ≤ η) :
    ∃ κ : Measure (X×X),
      (τ+κ).map Prod.fst = η ∧ (τ+κ).map Prod.snd = ν ∧
      κ = ((η-τ.map Prod.fst) univ)⁻¹ •
        ((η-τ.map Prod.fst).prod (ν-τ.map Prod.snd)) := by
  have hν : τ.map Prod.snd ≤ ν := by rw [← hπ₁]; exact Measure.map_mono hτ measurable_snd
  let d := η-τ.map Prod.fst
  let e := ν-τ.map Prod.snd
  have hm : e univ = d univ := by
    simp only [d,e,Measure.sub_apply MeasurableSet.univ hη,
      Measure.sub_apply MeasurableSet.univ hν,measure_univ,
      Measure.map_apply measurable_fst MeasurableSet.univ,
      Measure.map_apply measurable_snd MeasurableSet.univ,preimage_univ]
  have hmfin : d univ ≠ ∞ := measure_ne_top _ _
  refine ⟨(d univ)⁻¹ • d.prod e,?_,?_,rfl⟩
  · rw [Measure.map_add _ _ measurable_fst,Measure.map_smul _ measurable_fst.aemeasurable,
      Measure.map_fst_prod,hm,smul_smul]
    by_cases hz : d univ = 0
    · have hd : d = 0 := Measure.measure_univ_eq_zero.mp hz
      simp only [hd,smul_zero,add_zero]
      have heq := Measure.sub_add_cancel_of_le hη
      simpa only [← show d = η-τ.map Prod.fst from rfl,hd,zero_add] using heq
    · rw [ENNReal.inv_mul_cancel hz hmfin,one_smul,add_comm]
      exact Measure.sub_add_cancel_of_le hη
  · rw [Measure.map_add _ _ measurable_snd,Measure.map_smul _ measurable_snd.aemeasurable,
      Measure.map_snd_prod,smul_smul]
    by_cases hz : d univ = 0
    · have he : e = 0 := Measure.measure_univ_eq_zero.mp (hm.trans hz)
      simp only [he,smul_zero,add_zero]
      have heq := Measure.sub_add_cancel_of_le hν
      simpa only [← show e = ν-τ.map Prod.snd from rfl,he,zero_add] using heq
    · rw [ENNReal.inv_mul_cancel hz hmfin,one_smul,add_comm]
      exact Measure.sub_add_cancel_of_le hν
end

 
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
 theorem map_withDensity_pullback (μ : Measure X) {T : X → Y} (hT : Measurable T)
    {a : Y → ℝ≥0∞} (ha : Measurable a) :
    (μ.withDensity (a ∘ T)).map T = (μ.map T).withDensity a := by
  ext s hs
  rw [Measure.map_apply hT hs,withDensity_apply _ (hT hs),withDensity_apply _ hs,
    ← lintegral_indicator (hT hs),← lintegral_indicator hs,
    lintegral_map (ha.indicator hs) hT]
  exact lintegral_congr (fun _ => Set.indicator_comp_right T)
 
noncomputable def retainedFraction (q r : ℝ≥0∞) : ℝ≥0∞ := min 1 (r/q)
 theorem retainedFraction_le (q r : ℝ≥0∞) : retainedFraction q r ≤ 1 := min_le_left _ _
 theorem retainedFraction_mul {q r : ℝ≥0∞} (hq : q ≠ ∞) :
    q*retainedFraction q r = min q r := by
  by_cases hz : q = 0
  · simp [hz,retainedFraction]
  · rw [retainedFraction,mul_min, mul_one,ENNReal.mul_div_cancel hz hq]
 theorem retainedFraction_measurable {q r : X → ℝ≥0∞} (hq : Measurable q) (hr : Measurable r) :
    Measurable (fun x => retainedFraction (q x) (r x)) := measurable_const.min (hr.div hq)
 theorem retainedCoupling_le (π : Measure (X×X)) (q r : X → ℝ≥0∞) :
    π.withDensity (fun xy => retainedFraction (q xy.1) (r xy.1)) ≤ π := by
  calc
    _ ≤ π.withDensity 1 := withDensity_mono (Eventually.of_forall fun xy => retainedFraction_le _ _)
    _ = π := withDensity_one
 theorem retainedCoupling_fst (μ : Measure X) (π : Measure (X×X))
    {q r : X → ℝ≥0∞} (hq : Measurable q) (hr : Measurable r) (hqfin : ∀ x, q x ≠ ∞)
    (hπ : π.map Prod.fst = μ.withDensity q) :
    (π.withDensity (fun xy => retainedFraction (q xy.1) (r xy.1))).map Prod.fst =
      μ.withDensity (fun x => min (q x) (r x)) := by
  change (π.withDensity ((fun x => retainedFraction (q x) (r x)) ∘ Prod.fst)).map Prod.fst = _
  rw [map_withDensity_pullback π measurable_fst (retainedFraction_measurable hq hr),hπ,
    ← withDensity_mul μ hq (retainedFraction_measurable hq hr)]
  congr 1
  funext x
  exact retainedFraction_mul (hqfin x)
end

 
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
variable {X : Type*} [MeasurableSpace X]
 theorem retainedFraction_tendsto {q : ℝ≥0∞} (hq0 : q ≠ 0) (hqfin : q ≠ ∞)
    {rs : ℕ → ℝ≥0∞} (hr : Tendsto rs atTop (𝓝 q)) :
    Tendsto (fun i => retainedFraction q (rs i)) atTop (𝓝 1) := by
  have hdiv := ENNReal.Tendsto.mul_const (b := q⁻¹) hr
    (Or.inr (ENNReal.inv_ne_top.mpr hq0))
  have heq : q*q⁻¹ = 1 := ENNReal.mul_inv_cancel hq0 hqfin
  simpa only [retainedFraction,div_eq_mul_inv,heq,min_self] using (tendsto_const_nhds (x := (1:ℝ≥0∞))).min hdiv
 theorem retainedCoupling_fraction_tendsto (μ : Measure X) (π : Measure (X×X))
    {q : X → ℝ≥0∞} {rs : ℕ → X → ℝ≥0∞} (hq : Measurable q) (hqfin : ∀ x, q x ≠ ∞)
    (hπ : π.map Prod.fst = μ.withDensity q)
    (hr : ∀ᵐ x ∂μ, Tendsto (fun i => rs i x) atTop (𝓝 (q x))) :
    ∀ᵐ xy ∂π, Tendsto (fun i => retainedFraction (q xy.1) (rs i xy.1)) atTop (𝓝 1) := by
  have h : ∀ᵐ x ∂μ.withDensity q, Tendsto (fun i => retainedFraction (q x) (rs i x)) atTop (𝓝 1) := by
    apply (ae_withDensity_iff hq).mpr
    filter_upwards [hr] with x hx
    intro hq0
    exact retainedFraction_tendsto hq0 (hqfin x) hx
  rw [← hπ] at h
  exact ae_of_ae_map measurable_fst.aemeasurable h
 theorem withDensity_complement_add (π : Measure X) {a : X → ℝ≥0∞}
    (ha : Measurable a) (ha1 : ∀ x, a x ≤ 1) :
    π.withDensity (fun x => 1-a x)+π.withDensity a = π := by
  have hsub : Measurable (fun x => (1:ℝ≥0∞)-a x) := measurable_const.sub ha
  rw [← withDensity_add_left hsub a]
  have heq : (fun x => 1-a x)+a = 1 := by
    funext x
    exact tsub_add_cancel_of_le (ha1 x)
  rw [heq,withDensity_one]
 theorem complement_lintegral_tendsto_zero (π : Measure X) {as : ℕ → X → ℝ≥0∞}
    (ha : ∀ i, Measurable (as i))
    (hlim : ∀ᵐ x ∂π, Tendsto (fun i => as i x) atTop (𝓝 1))
    {v : X → ℝ≥0∞} (hv : Measurable v) (hvfin : ∀ x, v x ≠ ∞)
    (hint : ∫⁻x, v x ∂π ≠ ∞) :
    Tendsto (fun i => ∫⁻x, v x ∂π.withDensity (fun x => 1-as i x)) atTop (𝓝 0) := by
  have hsub (i : ℕ) : Measurable (fun x => (1:ℝ≥0∞)-as i x) := measurable_const.sub (ha i)
  simp_rw [lintegral_withDensity_eq_lintegral_mul π (hsub _) hv,Pi.mul_apply]
  have h := tendsto_lintegral_of_dominated_convergence v
    (fun i => (measurable_const.sub (ha i)).mul hv)
    (fun i => Eventually.of_forall fun x => by
      calc
        (1-as i x)*v x ≤ 1*v x := by gcongr; exact tsub_le_self
        _ = v x := one_mul _)
    hint (show ∀ᵐ x ∂π, Tendsto (fun i => (1-as i x)*v x) atTop (𝓝 0) from by
      filter_upwards [hlim] with x hx
      have hc := (ENNReal.continuous_sub_left (by norm_num : (1:ℝ≥0∞) ≠ ∞)).continuousAt.tendsto.comp hx
      have hc0 : Tendsto (fun i => 1-as i x) atTop (𝓝 0) := by simpa only [tsub_self, Function.comp_def] using hc
      simpa only [zero_mul] using ENNReal.Tendsto.mul_const hc0 (Or.inr (hvfin x)))
  simpa only [lintegral_zero, Pi.sub_apply, Pi.mul_apply, Pi.one_apply] using h
end

 
section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]
 theorem transportCost_le_marginal_moments (π : Measure (X×X)) (p : X) :
    transportCost π ≤
      2*(∫⁻x, ENNReal.ofReal (dist p x)^2 ∂π.map Prod.fst)+
      2*(∫⁻x, ENNReal.ofReal (dist p x)^2 ∂π.map Prod.snd) := by
  have hv : Measurable (fun x : X => ENNReal.ofReal (dist p x)^2) := by fun_prop
  rw [lintegral_map hv measurable_fst,
    lintegral_map hv measurable_snd,
    ← lintegral_const_mul _ ((measurable_const.dist measurable_fst).ennreal_ofReal.pow_const 2),
    ← lintegral_const_mul _ ((measurable_const.dist measurable_snd).ennreal_ofReal.pow_const 2)]
  rw [← lintegral_add_left (show Measurable (fun xy : X×X => (2:ℝ≥0∞)*ENNReal.ofReal (dist p xy.1)^2) from by fun_prop)]
  apply lintegral_mono
  intro xy
  dsimp only
  rw [← ENNReal.ofReal_pow dist_nonneg,← ENNReal.ofReal_pow dist_nonneg,← ENNReal.ofReal_pow dist_nonneg,
    ← ENNReal.ofReal_ofNat 2,← ENNReal.ofReal_mul (by norm_num : 0 ≤ (2:ℝ)),
    ← ENNReal.ofReal_mul (by norm_num : 0 ≤ (2:ℝ)),← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hd := dist_triangle xy.1 p xy.2
  rw [dist_comm xy.1 p] at hd
  nlinarith [dist_nonneg (x := xy.1) (y := xy.2),sq_nonneg (dist p xy.1-dist p xy.2)]
omit [MetricSpace X] [BorelSpace X] [SeparableSpace X] in
 theorem equalMass_product_marginals (d e : Measure X) [IsFiniteMeasure d] [IsFiniteMeasure e]
    (hm : e univ = d univ) :
    ((d univ)⁻¹ • d.prod e).map Prod.fst = d ∧
    ((d univ)⁻¹ • d.prod e).map Prod.snd = e := by
  by_cases hz : d univ = 0
  · have hd : d = 0 := Measure.measure_univ_eq_zero.mp hz
    have he : e = 0 := Measure.measure_univ_eq_zero.mp (hm.trans hz)
    simp [hd,he]
  · constructor
    · rw [Measure.map_smul _ measurable_fst.aemeasurable,Measure.map_fst_prod,hm,smul_smul,
        ENNReal.inv_mul_cancel hz (measure_ne_top _ _),one_smul]
    · rw [Measure.map_smul _ measurable_snd.aemeasurable,Measure.map_snd_prod,smul_smul,
        ENNReal.inv_mul_cancel hz (measure_ne_top _ _),one_smul]
 theorem equalMass_product_cost_le (d e : Measure X) [IsFiniteMeasure d] [IsFiniteMeasure e]
    (hm : e univ = d univ) (p : X) :
    transportCost ((d univ)⁻¹ • d.prod e) ≤
      2*(∫⁻x, ENNReal.ofReal (dist p x)^2 ∂d)+
      2*(∫⁻x, ENNReal.ofReal (dist p x)^2 ∂e) := by
  have h := transportCost_le_marginal_moments ((d univ)⁻¹ • d.prod e) p
  rw [(equalMass_product_marginals d e hm).1,(equalMass_product_marginals d e hm).2] at h
  exact h
end

 
section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]
 

 theorem density_coupling_recovery (μ : Measure X) (ν : Measure X) [IsProbabilityMeasure ν]
    (π : Measure (X×X)) [IsProbabilityMeasure π]
    {q : X → ℝ≥0∞} {rs : ℕ → X → ℝ≥0∞}
    (hq : Measurable q) (hqfin : ∀ x, q x ≠ ∞) (hr : ∀ i, Measurable (rs i))
    (hrP : ∀ i, IsProbabilityMeasure (μ.withDensity (rs i)))
    (hπ₀ : π.map Prod.fst = μ.withDensity q) (hπ₁ : π.map Prod.snd = ν)
    (hlim : ∀ᵐx ∂μ, Tendsto (fun i => rs i x) atTop (𝓝 (q x)))
    (p : X) (R : ℝ) (hs : ∀ i x, rs i x ≠ 0 → dist p x ≤ R)
    (hint : ∫⁻x, ENNReal.ofReal (dist p x)^2 ∂ν ≠ ∞) :
    ∃ (plans : ℕ → Measure (X×X)) (costs : ℕ → ℝ≥0∞),
      (∀ i, (plans i).map Prod.fst = μ.withDensity (rs i)) ∧
      (∀ i, (plans i).map Prod.snd = ν) ∧
      (∀ i, transportCost (plans i) ≤ costs i) ∧
      Tendsto costs atTop (𝓝 (transportCost π)) := by
  let a := fun i (xy : X×X) => retainedFraction (q xy.1) (rs i xy.1)
  have ha (i : ℕ) : Measurable (a i) := (retainedFraction_measurable hq (hr i)).comp measurable_fst
  have ha1 (i : ℕ) (xy : X×X) : a i xy ≤ 1 := retainedFraction_le _ _
  let τ := fun i => π.withDensity (a i)
  let δ := fun i => π.withDensity (fun xy => 1-a i xy)
  have hτ (i : ℕ) : τ i ≤ π := retainedCoupling_le π q (rs i)
  have hδ (i : ℕ) : δ i ≤ π := by
    calc
      _ ≤ π.withDensity 1 := withDensity_mono (Eventually.of_forall fun _ => tsub_le_self)
      _ = π := withDensity_one
  have hτfin (i : ℕ) : IsFiniteMeasure (τ i) := isFiniteMeasure_of_le π (hτ i)
  have hδfin (i : ℕ) : IsFiniteMeasure (δ i) := isFiniteMeasure_of_le π (hδ i)
  have hsum (i : ℕ) : δ i+τ i = π := withDensity_complement_add π (ha i) (ha1 i)
  let η := fun i => μ.withDensity (rs i)
  have hη (i : ℕ) : (τ i).map Prod.fst ≤ η i := by
    dsimp [τ,a,η]
    rw [retainedCoupling_fst μ π hq (hr i) hqfin hπ₀]
    exact withDensity_mono (Eventually.of_forall fun _ => min_le_right _ _)
  let d := fun i => η i-(τ i).map Prod.fst
  let e := fun i => (δ i).map Prod.snd
  have hdFin (i : ℕ) : IsFiniteMeasure (d i) := by
    let := hrP i
    dsimp [d,η]
    infer_instance
  have heFin (i : ℕ) : IsFiniteMeasure (e i) := by
    let := hδfin i
    dsimp [e]
    infer_instance
  have headd (i : ℕ) : e i+(τ i).map Prod.snd = ν := by
    change (δ i).map Prod.snd+(τ i).map Prod.snd = ν
    rw [← Measure.map_add _ _ measurable_snd,hsum i,hπ₁]
  have hm (i : ℕ) : e i univ = d i univ := by
    let := hrP i
    let := hτfin i
    let := hδfin i
    have heq : e i = ν-(τ i).map Prod.snd := by
      rw [← headd i,Measure.add_sub_cancel]
    rw [heq,Measure.sub_apply MeasurableSet.univ (by rw [← hπ₁]; exact Measure.map_mono (hτ i) measurable_snd)]
    change _ = (η i-(τ i).map Prod.fst) univ
    rw [Measure.sub_apply MeasurableSet.univ (hη i)]
    simp only [Measure.map_apply measurable_snd MeasurableSet.univ,
      Measure.map_apply measurable_fst MeasurableSet.univ,preimage_univ,measure_univ]
  let κ := fun i => (d i univ)⁻¹ • (d i).prod (e i)
  have hκ (i : ℕ) : (κ i).map Prod.fst = d i ∧ (κ i).map Prod.snd = e i := by
    let := hdFin i
    let := heFin i
    exact equalMass_product_marginals (d i) (e i) (hm i)
  let costs := fun i => transportCost π+
    2*(ENNReal.ofReal R)^2*(δ i univ)+
    2*(∫⁻xy : X×X, ENNReal.ofReal (dist p xy.2)^2 ∂δ i)
  refine ⟨fun i => τ i+κ i,costs,?_,?_,?_,?_⟩
  · intro i
    let := hτfin i
    rw [Measure.map_add _ _ measurable_fst,(hκ i).1,add_comm]
    exact Measure.sub_add_cancel_of_le (hη i)
  · intro i
    rw [Measure.map_add _ _ measurable_snd,(hκ i).2,add_comm]
    exact headd i
  · intro i
    let := hdFin i
    let := heFin i
    have hb : ∀ᵐx ∂d i, dist p x ≤ R := by
      have hηb : ∀ᵐx ∂η i, dist p x ≤ R :=
        (ae_withDensity_iff (hr i)).mpr (Eventually.of_forall (hs i))
      exact (Measure.absolutelyContinuous_of_le (show d i ≤ η i from Measure.sub_le)).ae_le hηb
    have hdi : (∫⁻x, ENNReal.ofReal (dist p x)^2 ∂d i) ≤ (ENNReal.ofReal R)^2*(δ i univ) := by
      calc
        _ ≤ ∫⁻_x, (ENNReal.ofReal R)^2 ∂d i := lintegral_mono_ae (hb.mono fun x hx => pow_le_pow_left' (ENNReal.ofReal_le_ofReal hx) _)
        _ = (ENNReal.ofReal R)^2*(δ i univ) := by
          rw [lintegral_const,← hm i,Measure.map_apply measurable_snd MeasurableSet.univ]
          rfl
    have heint : (∫⁻x, ENNReal.ofReal (dist p x)^2 ∂e i) =
        ∫⁻xy : X×X, ENNReal.ofReal (dist p xy.2)^2 ∂δ i :=
      lintegral_map (by fun_prop) measurable_snd
    calc
      _ = transportCost (τ i)+transportCost (κ i) := lintegral_add_measure _ _ _
      _ ≤ transportCost π+(2*(∫⁻x, ENNReal.ofReal (dist p x)^2 ∂d i)+
          2*(∫⁻x, ENNReal.ofReal (dist p x)^2 ∂e i)) :=
        add_le_add (lintegral_mono' (hτ i) le_rfl) (equalMass_product_cost_le (d i) (e i) (hm i) p)
      _ ≤ costs i := by
        dsimp only [costs]
        rw [heint,← add_assoc]
        apply add_le_add _ le_rfl
        apply add_le_add le_rfl
        calc
          _ ≤ 2*((ENNReal.ofReal R)^2*(δ i univ)) := by gcongr
          _ = _ := (mul_assoc _ _ _).symm
  · have halim := retainedCoupling_fraction_tendsto μ π hq hqfin hπ₀ hlim
    have hmass : Tendsto (fun i => δ i univ) atTop (𝓝 0) := by
      have hh := complement_lintegral_tendsto_zero π ha halim (v := fun _ => 1) measurable_const
        (fun _ => by norm_num) (by simp)
      simpa only [lintegral_const,one_mul,δ] using hh
    have hv : Measurable (fun xy : X×X => ENNReal.ofReal (dist p xy.2)^2) := by fun_prop
    have hsecond : Tendsto (fun i => ∫⁻xy : X×X, ENNReal.ofReal (dist p xy.2)^2 ∂δ i) atTop (𝓝 0) := by
      apply complement_lintegral_tendsto_zero π ha halim hv
      · intro xy
        finiteness
      · rw [← lintegral_map (by fun_prop : Measurable (fun x : X => ENNReal.ofReal (dist p x)^2)) measurable_snd,hπ₁]
        exact hint
    have h1 := ENNReal.Tendsto.const_mul (a := 2*(ENNReal.ofReal R)^2) hmass (Or.inr (by finiteness))
    have h2 := ENNReal.Tendsto.const_mul (a := 2) hsecond (Or.inr (by norm_num))
    simpa only [costs,mul_zero,add_zero] using (tendsto_const_nhds.add h1).add h2
end

 
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X]
 

 theorem FullCD.compact_sobolev_HWI (μ : Measure X)
    [IsFiniteMeasureOnCompacts μ] [NeZero μ] [SigmaFinite μ]
    (K : ℝ) (n : ℕ) (hcd : FullCD μ K n)
    (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (Metric.closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f G : Lp ℝ 2 μ) (hG : IsRelaxedSlope μ f G) (hfM : ‖f‖ = 1)
    (M : ℝ≥0) (hf : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ M)
    {r : ℝ} (hfS : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r)
    (ν : Measure X) [IsProbabilityMeasure ν] (hν : ν ≪ μ)
    (hνE : Integrable (fun x => (ν.rnDeriv μ x).toReal*Real.log (ν.rnDeriv μ x).toReal) μ)
    (hνExp : Integrable (fun x => Real.exp ((3*(B+1))*dist p x)) ν)
    (hνDist : Integrable (fun x => dist p x^2) ν)
    (π : Measure (X×X))
    (hπ₀ : π.map Prod.fst = μ.withDensity (fun x => ENNReal.ofReal (f x^2)))
    (hπ₁ : π.map Prod.snd = ν) :
    ENNReal.ofReal ((∫x, f x^2*Real.log (f x^2) ∂μ)-boltzmannEntropy μ ν) ≤
      ENNReal.ofReal (2*‖G‖)*(transportCost π)^(1/(2:ℝ))+
      ENNReal.ofReal (|K|/2)*transportCost π := by
  have hfm : Measurable (fun x => f x) := (Lp.stronglyMeasurable f).measurable
  have hfi : Integrable (fun x => f x^2) μ := by
    simpa only [Real.norm_eq_abs,sq_abs] using
      (Lp.memLp f).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
  have hfmass : ∫x, f x^2 ∂μ = 1 := by rw [integral_sq_Lp,hfM,one_pow]
  let ρ := μ.withDensity (fun x => ENNReal.ofReal (f x^2))
  let : IsProbabilityMeasure ρ := squareDensity_probability μ hfi hfmass
  let : IsProbabilityMeasure π := by
    have : IsProbabilityMeasure (π.map Prod.fst) := by rw [hπ₀]; exact inferInstanceAs (IsProbabilityMeasure ρ)
    exact Measure.isProbabilityMeasure_of_map measurable_fst.aemeasurable
  have hρs : ∀ᵐ x ∂ρ, dist p x ≤ r := by
    apply (ae_withDensity_iff (hfm.pow_const 2).ennreal_ofReal).mpr
    filter_upwards [hfS] with x hx
    intro hq
    apply hx
    intro hz
    simp only [hz,zero_pow (by norm_num : (2:ℕ) ≠ 0),ENNReal.ofReal_zero] at hq
    exact hq rfl
  have hρdist : Integrable (fun x => dist p x^2) ρ := by
    apply (integrable_const ((max r 0)^2)).mono' (by fun_prop)
    filter_upwards [hρs] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ dist_nonneg (hx.trans (le_max_left _ _)) 2
  have hπfin := coupling_transportCost_ne_top hπ₀ hπ₁ p hρdist hνDist
  obtain ⟨gs,Gs,H,R,hl,hg,hlim,hH,hb,hs,hm,ha,hEnt⟩ :=
    hG.compact_probability_recovery μ hfM M hf p hfS
  have hgs (i : ℕ) : Measurable (gs i) := (hl i).choose_spec.continuous.measurable
  have hgprob (i : ℕ) : IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (gs i x^2))) :=
    squareDensity_probability μ
      (compactSquare_integrable μ (hl i).choose_spec.continuous (compactSupport_of_dist_bound p (hs i))) (hm i)
  have hνlin : ∫⁻x, ENNReal.ofReal (dist p x)^2 ∂ν ≠ ∞ := by
    have h := ofReal_integral_eq_lintegral_ofReal hνDist (Eventually.of_forall fun x => sq_nonneg (dist p x))
    simp only [ENNReal.ofReal_pow dist_nonneg] at h
    rw [← h]
    exact ENNReal.ofReal_ne_top
  obtain ⟨plans,costs,hp0,hp1,hpc,hCost⟩ := density_coupling_recovery μ ν π
    (hfm.pow_const 2).ennreal_ofReal (fun _ => ENNReal.ofReal_ne_top)
    (fun i => ((hgs i).pow_const 2).ennreal_ofReal) hgprob hπ₀ hπ₁
    (ha.mono fun x hx => ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hx.pow 2)) p R
    (fun i x hx => hs i x (by intro hz; simp only [hz,zero_pow (by norm_num : (2:ℕ) ≠ 0),ENNReal.ofReal_zero] at hx; exact hx rfl)) hνlin
  have hineq (i : ℕ) :
      ENNReal.ofReal ((∫x, gs i x^2*Real.log (gs i x^2) ∂μ)-boltzmannEntropy μ ν) ≤
        ENNReal.ofReal (2*‖Gs i‖)*(costs i)^(1/(2:ℝ))+
        ENNReal.ofReal (|K|/2)*costs i := by
    have hi := hcd.compact_density_HWI μ K n p hA hB hvol (gs i)
      (hl i).choose_spec (M := 2*M) (fun x => by simpa only [abs_of_nonneg (hb i x).1,NNReal.coe_mul,NNReal.coe_ofNat] using (hb i x).2)
      (hs i) (hm i) (Gs i) (hg i) ν hν hνE hνExp hνDist (plans i) (hp0 i) (hp1 i)
    apply hi.trans
    gcongr <;> exact hpc i
  have hLeft := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hEnt.sub_const (boltzmannEntropy μ ν))
  have hMaj := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hlim.norm.const_mul 2)
  have hSqrt := (ENNReal.continuous_rpow_const (y := (1/(2:ℝ)))).continuousAt.tendsto.comp hCost
  have hRight := (ENNReal.Tendsto.mul hMaj
    (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by norm_num : 0 ≤ 1/(2:ℝ)) hπfin)) hSqrt (Or.inr ENNReal.ofReal_ne_top)).add
      (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (|K|/2)) hCost (Or.inr ENNReal.ofReal_ne_top))
  have hres := le_of_tendsto_of_tendsto hLeft hRight (Eventually.of_forall hineq)
  apply hres.trans
  gcongr

end RegularPointCoordinates

end OAI
