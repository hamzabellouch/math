import Mathlib
import OAI.Analysis.RCDHeat.CouplingRepair

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: NormalizedCutoff, DensityFactorEntropy, DensityResidual, DominatedCouplingRecovery, BoundedSobolevDescent. -/



namespace RegularPointCoordinates

section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X)
 

 theorem IsRelaxedSlope.normalized_cutoff_recovery {f G : Lp ℝ 2 μ}
    (hG : IsRelaxedSlope μ f G) (hfM : ‖f‖ = 1) (p : X) :
    ∃ (us Gs : ℕ → Lp ℝ 2 μ) (ws : ℕ → X → ℝ) (Rs : ℕ → ℝ),
      (∀ i, IsRelaxedSlope μ (us i) (Gs i)) ∧
      Tendsto us atTop (𝓝 f) ∧ Tendsto Gs atTop (𝓝 G) ∧
      (∀ i, ‖us i‖ = 1) ∧ (∀ i, Measurable (ws i)) ∧
      (∀ i x, 0 ≤ ws i x ∧ ws i x ≤ 2) ∧
      (∀ i x, ws i x ≠ 0 → dist p x ≤ Rs i) ∧
      (∀ x, Tendsto (fun i => ws i x) atTop (𝓝 1)) ∧
      (∀ i, ⇑(us i) =ᵐ[μ] fun x => ws i x*f x) := by
  let R : ℕ → ℝ := fun i => (i:ℝ)+1
  have hR (i : ℕ) : 0 < R i := by dsimp [R]; positivity
  have hRL : Tendsto R atTop atTop := tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  let θ := fun i => radialCutoff p (R i)
  have hθm (i : ℕ) : Measurable (θ i) := (radialCutoff_lipschitz p (hR i)).continuous.measurable
  have hθb (i : ℕ) (x : X) : |θ i x| ≤ 1 := by
    rw [abs_of_nonneg (radialCutoff_bounds p (R i) x).1]
    exact (radialCutoff_bounds p (R i) x).2
  let Θ := fun i => boundedMultiplier μ (θ i) (hθm i) 1 (hθb i)
  have hΘ (i : ℕ) : ⇑(Θ i) =ᵐ[μ] θ i := boundedMultiplier_coe μ _ _ _ _
  let c := fun i => (R i)⁻¹
  have hc (i : ℕ) : 0 ≤ c i := inv_nonneg.mpr (hR i).le
  let Η := fun i => boundedMultiplier μ (fun _ : X => c i) measurable_const
    ⟨c i,hc i⟩ (fun _ => by rw [abs_of_nonneg (hc i)]; rfl)
  have hΗ (i : ℕ) : ⇑(Η i) =ᵐ[μ] fun _ => c i := boundedMultiplier_coe μ _ _ _ _
  let vs := fun i => lpMultiplier μ (Θ i) f
  let Hs := fun i => lpMultiplier μ (Θ i) G+c i • lpAbs μ f
  have hcMul (i : ℕ) : lpMultiplier μ (Η i) (lpAbs μ f) = c i • lpAbs μ f := by
    apply Lp.ext
    filter_upwards [lpMultiplier_coe μ (Η i) (lpAbs μ f),hΗ i,Lp.coeFn_smul (c i) (lpAbs μ f)] with x hx he hs
    simpa only [hx,he,Pi.smul_apply,smul_eq_mul] using hs.symm
  have hRelax (i : ℕ) : IsRelaxedSlope μ (vs i) (Hs i) := by
    have hh := hG.mul_lipschitz μ (B := 1) (radialCutoff_lipschitz p (hR i)) 0
      (by simpa only [sub_zero] using radialCutoff_hasCompactSupport p (hR i))
      (hθb i) (fun x => (radialCutoff_bounds p (R i) x).1)
      (fun _ => hc i) (fun x => by
        exact (localSlope_le_of_lipschitz (radialCutoff_lipschitz p (hR i)) x).trans_eq
          (ENNReal.coe_nnreal_eq _))
      (Θ i) (Η i) (hΘ i) (hΗ i)
    simpa only [hcMul] using hh
  have hθL (x : X) : Tendsto (fun i => θ i x) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hRL.eventually (radialCutoff_eventually_one p x)] with i hi
    exact hi.symm
  have hmul (u : Lp ℝ 2 μ) : Tendsto (fun i => lpMultiplier μ (Θ i) u) atTop (𝓝 u) := by
    have hh := lpMultiplier_tendsto_of_ae μ u θ (fun _ => 1) hθm measurable_const 1 hθb
      (fun _ => by norm_num) (Eventually.of_forall hθL)
    have he : lpMultiplier μ (boundedMultiplier μ (fun _ : X => 1) measurable_const 1 (fun _ => by norm_num)) u = u := by
      apply Lp.ext
      filter_upwards [lpMultiplier_coe μ (boundedMultiplier μ (fun _ : X => 1) measurable_const 1 (fun _ => by norm_num)) u,
        boundedMultiplier_coe μ (fun _ : X => 1) measurable_const 1 (fun _ => by norm_num)] with x hx he
      simpa only [he,one_mul] using hx
    simpa only [he] using hh
  have hvL : Tendsto vs atTop (𝓝 f) := hmul f
  have hcL : Tendsto c atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hRL
  have hHL : Tendsto Hs atTop (𝓝 G) := by
    simpa only [Hs,zero_smul,add_zero] using (hmul G).add (hcL.smul_const (lpAbs μ f))
  have hvNorm : Tendsto (fun i => ‖vs i‖) atTop (𝓝 (1:ℝ)) := by simpa only [hfM] using hvL.norm
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hvNorm.eventually (lt_mem_nhds (by norm_num : (1:ℝ)/2 < 1)))
  let a : ℕ → ℝ := fun i => ‖vs (i+N)‖⁻¹
  have hnu (i : ℕ) : (1:ℝ)/2 < ‖vs (i+N)‖ := hN _ (Nat.le_add_left N i)
  have hnpos (i : ℕ) : 0 < ‖vs (i+N)‖ := by linarith [hnu i]
  have haP (i : ℕ) : 0 < a i := inv_pos.mpr (hnpos i)
  have haB (i : ℕ) : a i ≤ 2 := by
    dsimp [a]
    calc
      _ ≤ ((1:ℝ)/2)⁻¹ := (inv_le_inv₀ (hnpos i) (by norm_num)).mpr (hnu i).le
      _ = 2 := by norm_num
  have haL : Tendsto a atTop (𝓝 (1:ℝ)) := by
    simpa only [a,Function.comp_def,inv_one] using (hvNorm.comp (tendsto_add_atTop_nat N)).inv₀ one_ne_zero
  refine ⟨fun i => a i • vs (i+N),fun i => a i • Hs (i+N),fun i x => a i*θ (i+N) x,
    fun i => 2*R (i+N),fun i => (hRelax (i+N)).const_mul μ (haP i).le,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Function.comp_def,one_smul] using haL.smul (hvL.comp (tendsto_add_atTop_nat N))
  · simpa only [Function.comp_def,one_smul] using haL.smul (hHL.comp (tendsto_add_atTop_nat N))
  · intro i
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (haP i)]
    exact inv_mul_cancel₀ (ne_of_gt (hnpos i))
  · intro i
    exact measurable_const.mul (hθm (i+N))
  · intro i x
    have hb := radialCutoff_bounds p (R (i+N)) x
    refine ⟨mul_nonneg (haP i).le hb.1,?_⟩
    exact (mul_le_mul (haB i) hb.2 hb.1 (by norm_num)).trans_eq (mul_one _)
  · intro i x hx
    by_contra hn
    apply hx
    dsimp only
    rw [show θ (i+N) x = 0 from radialCutoff_eq_zero p (hR (i+N)) (le_of_not_ge hn),mul_zero]
  · intro x
    simpa only [Function.comp_def,mul_one] using haL.mul ((hθL x).comp (tendsto_add_atTop_nat N))
  · intro i
    filter_upwards [Lp.coeFn_smul (a i) (vs (i+N)),lpMultiplier_coe μ (Θ (i+N)) f,hΘ (i+N)] with x hs hm hθx
    simp only [Pi.smul_apply,smul_eq_mul] at hs
    rw [hs,hm,hθx,mul_assoc]
end

 
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
 

 theorem density_factor_entropy_tendsto {q : X → ℝ} (hq : Measurable q)
    (hqn : ∀ᵐ x ∂μ, 0 ≤ q x) (hqi : Integrable q μ)
    (hqe : Integrable (fun x => q x*Real.log (q x)) μ)
    {ws : ℕ → X → ℝ} (hw : ∀ i, Measurable (ws i))
    (C : ℝ≥0) (hb : ∀ i, ∀ᵐ x ∂μ, 0 ≤ ws i x ∧ ws i x ≤ C)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i => ws i x) atTop (𝓝 1)) :
    Tendsto (fun i => ∫x, (ws i x*q x)*Real.log (ws i x*q x) ∂μ) atTop
      (𝓝 (∫x, q x*Real.log (q x) ∂μ)) := by
  obtain ⟨D,hD⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) C)).exists_bound_of_continuousOn
    Real.continuous_mul_log.continuousOn
  apply tendsto_integral_of_dominated_convergence (fun x => (C:ℝ)*|q x*Real.log (q x)|+|D| *q x)
  · intro i
    exact (Real.continuous_mul_log.measurable.comp ((hw i).mul hq)).aestronglyMeasurable
  · exact (hqe.abs.const_mul C).add (hqi.const_mul |D|)
  · intro i
    filter_upwards [hb i,hqn] with x hx hqx
    rw [Real.norm_eq_abs,mul_log_mul]
    calc
      _ ≤ |ws i x*(q x*Real.log (q x))|+|(ws i x*Real.log (ws i x))*q x| := abs_add_le _ _
      _ = ws i x*|q x*Real.log (q x)|+|ws i x*Real.log (ws i x)| *q x := by
        simp only [abs_mul,abs_of_nonneg hx.1,abs_of_nonneg hqx]
      _ ≤ _ := by
        apply add_le_add (mul_le_mul_of_nonneg_right hx.2 (abs_nonneg _))
        apply mul_le_mul_of_nonneg_right _ hqx
        have hd : |ws i x*Real.log (ws i x)| ≤ D := by
          simpa only [Real.norm_eq_abs] using hD (ws i x) hx
        exact hd.trans (le_abs_self D)
  · filter_upwards [hlim] with x hx
    have hh := Real.continuous_mul_log.continuousAt.tendsto.comp (hx.mul_const (q x))
    simpa only [Function.comp_def,one_mul] using hh
end

 
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
variable {X : Type*} [MeasurableSpace X]
 

 theorem density_residual_lintegral_tendsto_zero (μ : Measure X)
    {q : X → ℝ≥0∞} {rs : ℕ → X → ℝ≥0∞}
    (hq : Measurable q) (hqfin : ∀ x, q x ≠ ∞) (hr : ∀ i, Measurable (rs i))
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hb : ∀ i, ∀ᵐ x ∂μ, rs i x ≤ C*q x)
    (hlim : ∀ᵐx ∂μ, Tendsto (fun i => rs i x) atTop (𝓝 (q x)))
    {v : X → ℝ≥0∞} (hv : Measurable v) (hvfin : ∀ x, v x ≠ ∞)
    (hint : ∫⁻x, q x*v x ∂μ ≠ ∞) :
    Tendsto (fun i => ∫⁻x, (rs i x-min (q x) (rs i x))*v x ∂μ) atTop (𝓝 0) := by
  have hdom (i : ℕ) : ∀ᵐ x ∂μ, (rs i x-min (q x) (rs i x))*v x ≤ C*(q x*v x) := by
    filter_upwards [hb i] with x hx
    calc
      (rs i x-min (q x) (rs i x))*v x ≤ rs i x*v x := by gcongr; exact tsub_le_self
      _ ≤ (C*q x)*v x := by gcongr
      _ = _ := mul_assoc _ _ _
  have hInt : ∫⁻x, C*(q x*v x) ∂μ ≠ ∞ := by
    rw [lintegral_const_mul' C _ hC]
    exact ENNReal.mul_ne_top hC hint
  have hPt : ∀ᵐx ∂μ, Tendsto (fun i => (rs i x-min (q x) (rs i x))*v x) atTop (𝓝 0) := by
    filter_upwards [hlim] with x hx
    have hm : Tendsto (fun i => min (q x) (rs i x)) atTop (𝓝 (q x)) := by
      simpa only [min_self] using (tendsto_const_nhds (x := q x)).min hx
    have hh := ENNReal.Tendsto.sub hx hm (Or.inl (hqfin x))
    simpa only [tsub_self,zero_mul] using
      ENNReal.Tendsto.mul_const hh (Or.inr (hvfin x))
  have hh := tendsto_lintegral_of_dominated_convergence (fun x => C*(q x*v x))
    (fun i => ((hr i).sub (hq.min (hr i))).mul hv) hdom hInt hPt
  simpa only [Pi.mul_apply,Pi.sub_apply,lintegral_zero] using hh
end

 
section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]
 

 theorem dominated_density_coupling_recovery (μ : Measure X) (ν : Measure X) [IsProbabilityMeasure ν]
    (π : Measure (X×X)) [IsProbabilityMeasure π]
    {q : X → ℝ≥0∞} {rs : ℕ → X → ℝ≥0∞}
    (hq : Measurable q) (hqfin : ∀ x, q x ≠ ∞) (hr : ∀ i, Measurable (rs i))
    (hrP : ∀ i, IsProbabilityMeasure (μ.withDensity (rs i)))
    (hπ₀ : π.map Prod.fst = μ.withDensity q) (hπ₁ : π.map Prod.snd = ν)
    (hlim : ∀ᵐx ∂μ, Tendsto (fun i => rs i x) atTop (𝓝 (q x)))
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hb : ∀ i, ∀ᵐ x ∂μ, rs i x ≤ C*q x)
    (p : X) (hqint : ∫⁻x, q x*ENNReal.ofReal (dist p x)^2 ∂μ ≠ ∞)
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
    2*(∫⁻x, ENNReal.ofReal (dist p x)^2 ∂d i)+
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
    have heint : (∫⁻x, ENNReal.ofReal (dist p x)^2 ∂e i) =
        ∫⁻xy : X×X, ENNReal.ofReal (dist p xy.2)^2 ∂δ i :=
      lintegral_map (by fun_prop) measurable_snd
    calc
      _ = transportCost (τ i)+transportCost (κ i) := lintegral_add_measure _ _ _
      _ ≤ transportCost π+(2*(∫⁻x, ENNReal.ofReal (dist p x)^2 ∂d i)+
          2*(∫⁻x, ENNReal.ofReal (dist p x)^2 ∂e i)) :=
        add_le_add (lintegral_mono' (hτ i) le_rfl) (equalMass_product_cost_le (d i) (e i) (hm i) p)
      _ = costs i := by
        dsimp only [costs]
        rw [heint,add_assoc]
  · have halim := retainedCoupling_fraction_tendsto μ π hq hqfin hπ₀ hlim
    have hfirst : Tendsto (fun i => ∫⁻x, ENNReal.ofReal (dist p x)^2 ∂d i) atTop (𝓝 0) := by
      have hv : Measurable (fun x : X => ENNReal.ofReal (dist p x)^2) := by fun_prop
      have hd (i : ℕ) : d i = μ.withDensity (fun x => rs i x-min (q x) (rs i x)) := by
        let := hτfin i
        have hmf : IsFiniteMeasure (μ.withDensity (fun x => min (q x) (rs i x))) := by
          rw [← retainedCoupling_fst μ π hq (hr i) hqfin hπ₀]
          exact inferInstanceAs (IsFiniteMeasure ((τ i).map Prod.fst))
        dsimp only [d,η,τ,a]
        rw [retainedCoupling_fst μ π hq (hr i) hqfin hπ₀,
          ← Measure.withDensity_sub (hr i) (hq.min (hr i))]
        rfl
      have hh := density_residual_lintegral_tendsto_zero μ hq hqfin hr hC hb hlim hv (fun _ => by finiteness) hqint
      apply hh.congr
      intro i
      rw [hd i]
      exact (lintegral_withDensity_eq_lintegral_mul μ ((hr i).sub (hq.min (hr i))) hv).symm
    have hv : Measurable (fun xy : X×X => ENNReal.ofReal (dist p xy.2)^2) := by fun_prop
    have hsecond : Tendsto (fun i => ∫⁻xy : X×X, ENNReal.ofReal (dist p xy.2)^2 ∂δ i) atTop (𝓝 0) := by
      apply complement_lintegral_tendsto_zero π ha halim hv
      · intro xy
        finiteness
      · rw [← lintegral_map (by fun_prop : Measurable (fun x : X => ENNReal.ofReal (dist p x)^2)) measurable_snd,hπ₁]
        exact hint
    have h1 := ENNReal.Tendsto.const_mul (a := 2) hfirst (Or.inr (by norm_num))
    have h2 := ENNReal.Tendsto.const_mul (a := 2) hsecond (Or.inr (by norm_num))
    simpa only [costs,mul_zero,add_zero] using (tendsto_const_nhds.add h1).add h2
end

 
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X]
 

 theorem FullCD.bounded_sobolev_HWI (μ : Measure X)
    [IsFiniteMeasureOnCompacts μ] [NeZero μ] [SigmaFinite μ]
    (K : ℝ) (n : ℕ) (hcd : FullCD μ K n)
    (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (Metric.closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f G : Lp ℝ 2 μ) (hG : IsRelaxedSlope μ f G) (hfM : ‖f‖ = 1)
    (M : ℝ≥0) (hf : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ M)
    (hfE : Integrable (fun x => f x^2*Real.log (f x^2)) μ)
    (hfDist : Integrable (fun x => dist p x^2)
      (μ.withDensity (fun x => ENNReal.ofReal (f x^2))))
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
    have : IsProbabilityMeasure (π.map Prod.fst) := by
      rw [hπ₀]; exact inferInstanceAs (IsProbabilityMeasure ρ)
    exact Measure.isProbabilityMeasure_of_map measurable_fst.aemeasurable
  have hπfin := coupling_transportCost_ne_top hπ₀ hπ₁ p hfDist hνDist
  obtain ⟨us,Gs,ws,Rs,hGus,huL,hGL,huM,hw,hwB,hwS,hwL,hue⟩ :=
    hG.normalized_cutoff_recovery μ hfM p
  have hum (i : ℕ) : Measurable (fun x => us i x) := (Lp.stronglyMeasurable (us i)).measurable
  have huBound (i : ℕ) : ∀ᵐx ∂μ, 0 ≤ us i x ∧ us i x ≤ (2*M:ℝ≥0) := by
    filter_upwards [hue i,hf] with x hx hfx
    rw [hx]
    refine ⟨mul_nonneg (hwB i x).1 hfx.1,?_⟩
    simpa only [NNReal.coe_mul,NNReal.coe_ofNat] using
      mul_le_mul (hwB i x).2 hfx.2 hfx.1 (by norm_num : (0:ℝ) ≤ 2)
  have huS (i : ℕ) : ∀ᵐx ∂μ, us i x ≠ 0 → dist p x ≤ Rs i := by
    filter_upwards [hue i] with x hx
    intro hn
    apply hwS i x
    intro hz
    apply hn
    rw [hx,hz,zero_mul]
  have huP (i : ℕ) : IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (us i x^2))) := by
    apply squareDensity_probability μ
    · simpa only [Real.norm_eq_abs,sq_abs] using
        (Lp.memLp (us i)).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
    · rw [integral_sq_Lp,huM i,one_pow]
  have hsq (i : ℕ) : (fun x => us i x^2) =ᵐ[μ] fun x => ws i x^2*f x^2 := by
    filter_upwards [hue i] with x hx
    rw [hx,mul_pow]
  have hw2B (i : ℕ) (x : X) : 0 ≤ ws i x^2 ∧ ws i x^2 ≤ (4:ℝ) := by
    have hb := hwB i x
    exact ⟨sq_nonneg _,by nlinarith⟩
  have hEnt := density_factor_entropy_tendsto μ (hfm.pow_const 2)
    (Eventually.of_forall fun x => sq_nonneg (f x)) hfi hfE
    (fun i => (hw i).pow_const 2) 4 (fun i => Eventually.of_forall (hw2B i))
    (Eventually.of_forall fun x => by simpa only [one_pow] using (hwL x).pow 2)
  have hEntL : Tendsto (fun i => ∫x, us i x^2*Real.log (us i x^2) ∂μ) atTop
      (𝓝 (∫x, f x^2*Real.log (f x^2) ∂μ)) := by
    apply hEnt.congr
    intro i
    apply integral_congr_ae
    filter_upwards [hsq i] with x hx
    rw [hx]
  have hrsL : ∀ᵐx ∂μ, Tendsto (fun i => ENNReal.ofReal (us i x^2)) atTop
      (𝓝 (ENNReal.ofReal (f x^2))) := by
    filter_upwards [ae_all_iff.mpr hsq] with x hx
    simp_rw [hx]
    apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    simpa only [one_pow,one_mul] using ((hwL x).pow 2).mul_const (f x^2)
  have hrsB (i : ℕ) : ∀ᵐx ∂μ, ENNReal.ofReal (us i x^2) ≤ 4*ENNReal.ofReal (f x^2) := by
    filter_upwards [hsq i] with x hx
    rw [hx,ENNReal.ofReal_mul (sq_nonneg _)]
    gcongr
    exact (ENNReal.ofReal_le_ofReal (hw2B i x).2).trans_eq (by norm_num)
  have hνlin : ∫⁻x, ENNReal.ofReal (dist p x)^2 ∂ν ≠ ∞ := by
    have h := ofReal_integral_eq_lintegral_ofReal hνDist (Eventually.of_forall fun x => sq_nonneg (dist p x))
    simp only [ENNReal.ofReal_pow dist_nonneg] at h
    rw [← h]
    exact ENNReal.ofReal_ne_top
  have hflin : ∫⁻x, ENNReal.ofReal (f x^2)*ENNReal.ofReal (dist p x)^2 ∂μ ≠ ∞ := by
    have he : (∫⁻x, ENNReal.ofReal (f x^2)*ENNReal.ofReal (dist p x)^2 ∂μ) =
        ∫⁻x, ENNReal.ofReal (dist p x)^2 ∂(μ.withDensity (fun x => ENNReal.ofReal (f x^2))) :=
      (lintegral_withDensity_eq_lintegral_mul μ (hfm.pow_const 2).ennreal_ofReal
        (by fun_prop : Measurable (fun x : X => ENNReal.ofReal (dist p x)^2))).symm
    rw [he]
    have h := ofReal_integral_eq_lintegral_ofReal hfDist (Eventually.of_forall fun x => sq_nonneg (dist p x))
    simp only [ENNReal.ofReal_pow dist_nonneg] at h
    rw [← h]
    exact ENNReal.ofReal_ne_top
  obtain ⟨plans,costs,hp0,hp1,hpc,hCost⟩ := dominated_density_coupling_recovery μ ν π
    (hfm.pow_const 2).ennreal_ofReal (fun _ => ENNReal.ofReal_ne_top)
    (fun i => ((hum i).pow_const 2).ennreal_ofReal) huP hπ₀ hπ₁ hrsL
    (by norm_num : (4:ℝ≥0∞) ≠ ∞) hrsB p hflin hνlin
  have hineq (i : ℕ) :
      ENNReal.ofReal ((∫x, us i x^2*Real.log (us i x^2) ∂μ)-boltzmannEntropy μ ν) ≤
        ENNReal.ofReal (2*‖Gs i‖)*(costs i)^(1/(2:ℝ))+
        ENNReal.ofReal (|K|/2)*costs i := by
    have hi := hcd.compact_sobolev_HWI μ K n p hA hB hvol (us i) (Gs i) (hGus i)
      (huM i) (2*M) (huBound i) (huS i) ν hν hνE hνExp hνDist (plans i) (hp0 i) (hp1 i)
    apply hi.trans
    gcongr <;> exact hpc i
  have hLeft := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hEntL.sub_const (boltzmannEntropy μ ν))
  have hMaj := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hGL.norm.const_mul 2)
  have hSqrt := (ENNReal.continuous_rpow_const (y := (1/(2:ℝ)))).continuousAt.tendsto.comp hCost
  have hRight := (ENNReal.Tendsto.mul hMaj
    (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by norm_num : 0 ≤ 1/(2:ℝ)) hπfin)) hSqrt (Or.inr ENNReal.ofReal_ne_top)).add
      (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (|K|/2)) hCost (Or.inr ENNReal.ofReal_ne_top))
  exact le_of_tendsto_of_tendsto hLeft hRight (Eventually.of_forall hineq)

end RegularPointCoordinates

end OAI
