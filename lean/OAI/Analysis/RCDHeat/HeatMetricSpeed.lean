import Mathlib
import OAI.Analysis.RCDHeat.CouplingRepair
import OAI.Analysis.RCDHeat.HeatHopfZero

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: HeatMetricSpeed, CouplingGluing, TransportMinkowski, WassersteinTriangle, WassersteinFinite, WassersteinMetric, HeatMetricAC. -/



section
open Set Metric Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
 

 theorem NoncollapsedRCD.heat_right_transport_speed (K : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (p : X) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) :=
      locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∀ (f : Lp ℝ 2 (hausdorff n X)), 0 ≤ f →
      (∃ r : ℝ, ∀ᵐ x ∂hausdorff n X, f x ≠ 0 → dist p x ≤ r) →
      (∫x, f x ∂hausdorff n X) = 1 → ∀ C : ℝ≥0,
      (∀ᵐ x ∂hausdorff n X, |f x| ≤ C) → ∀ T : ℝ, 0 < T →
      let μ := hausdorff n X
      let ρ := fun r => heatMeasure μ hX.quadratic r f
      ∀ᵐ s : ℝ, s ∈ Ioo 0 T →
        fisherInformation μ hX.quadratic f s ≠ ∞ ∧
        Tendsto (fun t => Real.sqrt (wassersteinSq (ρ s) (ρ t)).toReal/(t-s))
          (𝓝[>] s) (𝓝 (Real.sqrt (fisherInformation μ hX.quadratic f s).toReal)) := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let : IsLocallyFiniteMeasure (hausdorff n X) :=
    locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  let μ := hausdorff n X
  intro f hf0 hfs hfm C hfC T hT
  change ∀ᵐ s : ℝ, s ∈ Ioo 0 T → _
  obtain ⟨r,hfr⟩ := hfs
  obtain ⟨A,B,hA,hB,hvol⟩ := hX.exponential_volume K n hn p
  have hfi := lp_integrable_of_bounded_support μ f p hfr
  have hmeas := fisherInformation_aemeasurable_nonneg μ hX.quadratic f (b := T) le_rfl
  have hfin := heatAt_fisher_time_finite_nonneg μ hX.quadratic p hA hB hvol f hf0 hfi hfr
    le_rfl hT.le
  have hfinAE := (ae_restrict_iff' measurableSet_Ioc).mp (ae_lt_top' hmeas hfin.ne)
  have hder := heatAt_entropy_ae_hasDerivAt_nonneg μ hX.quadratic p hA hB hvol f hf0 hfi
    hfr le_rfl hT.le
  filter_upwards [hfinAE,hder] with s hsfin hsder
  intro hs
  have hIs : fisherInformation μ hX.quadratic f s ≠ ∞ := (hsfin ⟨hs.1,hs.2.le⟩).ne
  refine ⟨hIs,?_⟩
  apply entropy_action_descent_right_speed (E := fun t => boltzmannEntropy μ
      (heatMeasure μ hX.quadratic t f)) ENNReal.toReal_nonneg
      (by positivity : 0 ≤ |K|/2)
  · simpa only [boltzmannEntropy_heatMeasure_eq μ hX.quadratic f hf0] using hsder hs
  · exact Eventually.of_forall fun _ => ENNReal.toReal_nonneg
  · filter_upwards [self_mem_nhdsWithin (s := Ioi s)] with t ht
    exact (hX.heat_wasserstein_entropy_action K n hn p f hf0 ⟨r,hfr⟩ hfm C hfC s t hs.1.le ht).2
  · filter_upwards [self_mem_nhdsWithin (s := Ioi s)] with t ht
    exact hX.heat_wasserstein_HWI K n hn p f hf0 ⟨r,hfr⟩ hfm C hfC s t hs.1
      (hs.1.le.trans ht.le) hIs
end RegularPointCoordinates
end

 
section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace RegularPointCoordinates
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  [StandardBorelSpace Z] [Nonempty Z]
 

 theorem exists_glued_measure (π : Measure (X×Y)) (κ : Measure (Y×Z))
    [IsFiniteMeasure π] [IsFiniteMeasure κ] (h : π.map Prod.snd = κ.map Prod.fst) :
    ∃ γ : Measure ((X×Y)×Z), IsFiniteMeasure γ ∧
      γ.map Prod.fst = π ∧ γ.map (fun z => (z.1.2,z.2)) = κ := by
  let η : Kernel (X×Y) Z := κ.condKernel.comap Prod.snd measurable_snd
  let γ := π ⊗ₘ η
  refine ⟨γ,inferInstance,?_,?_⟩
  · exact Measure.fst_compProd π η
  · ext s hs
    rw [Measure.map_apply (measurable_fst.snd.prodMk measurable_snd) hs]
    rw [show γ = π ⊗ₘ η from rfl,
      Measure.compProd_apply ((measurable_fst.snd.prodMk measurable_snd) hs)]
    have he : (∫⁻ y, κ.condKernel y {z | (y,z) ∈ s} ∂π.map Prod.snd) =
        ∫⁻ xy, κ.condKernel xy.2 {z | (xy.2,z) ∈ s} ∂π :=
      lintegral_map (Kernel.measurable_kernel_prodMk_left hs) measurable_snd
    change (∫⁻ xy, κ.condKernel xy.2 {z | (xy.2,z) ∈ s} ∂π) = _
    rw [← he,h]
    exact Measure.lintegral_condKernel_mem hs
end RegularPointCoordinates
end

 
section
open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]
omit [BorelSpace X] [SeparableSpace X] in
 theorem transportCost_sqrt_eq_eLpNorm' (π : Measure (X×X)) :
    transportCost π ^ (1/(2:ℝ)) = eLpNorm' (fun xy : X×X => dist xy.1 xy.2) (2:ℝ) π := by
  rw [eLpNorm'_eq_lintegral_enorm]
  simp only [Real.enorm_eq_ofReal dist_nonneg, ENNReal.rpow_two, transportCost]
 theorem transportCost_sqrt_eq_eLpNorm (π : Measure (X×X)) :
    transportCost π ^ (1/(2:ℝ)) = eLpNorm (fun xy : X×X => dist xy.1 xy.2) 2 π := by
  rw [eLpNorm_eq_eLpNorm' (by norm_num : (2:ℝ≥0∞) ≠ 0) (by norm_num)
    (measurable_fst.dist measurable_snd).aestronglyMeasurable, ENNReal.toReal_ofNat]
  exact transportCost_sqrt_eq_eLpNorm' π
 theorem transportCost_triangle_marginals (γ : Measure ((X×X)×X)) :
    transportCost (γ.map (fun z => (z.1.1,z.2))) ^ (1/(2:ℝ)) ≤
      transportCost (γ.map Prod.fst) ^ (1/(2:ℝ))+
      transportCost (γ.map (fun z => (z.1.2,z.2))) ^ (1/(2:ℝ)) := by
  simp only [transportCost_sqrt_eq_eLpNorm]
  rw [eLpNorm_map_measure (measurable_fst.dist measurable_snd).aestronglyMeasurable
      (measurable_fst.fst.prodMk measurable_snd).aemeasurable,
    eLpNorm_map_measure (measurable_fst.dist measurable_snd).aestronglyMeasurable
      measurable_fst.aemeasurable,
    eLpNorm_map_measure (measurable_fst.dist measurable_snd).aestronglyMeasurable
      (measurable_fst.snd.prodMk measurable_snd).aemeasurable]
  apply (eLpNorm_mono_real (g := fun z : (X×X)×X => dist z.1.1 z.1.2+dist z.1.2 z.2)
    (measurable_fst.fst.dist measurable_snd).aestronglyMeasurable
    (fun z => ?_)).trans
      (eLpNorm_add_le (by norm_num))
  simpa only [Function.comp_apply,Real.norm_eq_abs,abs_of_nonneg dist_nonneg] using
    dist_triangle z.1.1 z.1.2 z.2
variable [StandardBorelSpace X] [Nonempty X]
 

 theorem exists_coupling_triangle {ν₀ ν₁ ν₂ : Measure X} (π κ : Measure (X×X))
    [IsFiniteMeasure π] [IsFiniteMeasure κ]
    (hπ₀ : π.map Prod.fst = ν₀) (hπ₁ : π.map Prod.snd = ν₁)
    (hκ₀ : κ.map Prod.fst = ν₁) (hκ₁ : κ.map Prod.snd = ν₂) :
    ∃ η : Measure (X×X), IsFiniteMeasure η ∧ η.map Prod.fst = ν₀ ∧
      η.map Prod.snd = ν₂ ∧ transportCost η ^ (1/(2:ℝ)) ≤
        transportCost π ^ (1/(2:ℝ))+transportCost κ ^ (1/(2:ℝ)) := by
  obtain ⟨γ,hγ,h0,h1⟩ := exists_glued_measure π κ (hπ₁.trans hκ₀.symm)
  let := hγ
  let η := γ.map (fun z => (z.1.1,z.2))
  refine ⟨η,inferInstance,?_,?_,?_⟩
  · rw [show η = γ.map (fun z => (z.1.1,z.2)) from rfl,
      Measure.map_map measurable_fst (measurable_fst.fst.prodMk measurable_snd)]
    rw [← hπ₀,← h0,Measure.map_map measurable_fst measurable_fst]
    rfl
  · rw [show η = γ.map (fun z => (z.1.1,z.2)) from rfl,
      Measure.map_map measurable_snd (measurable_fst.fst.prodMk measurable_snd)]
    rw [← hκ₁,← h1,Measure.map_map measurable_snd (measurable_fst.snd.prodMk measurable_snd)]
    rfl
  · simpa only [h0,h1] using transportCost_triangle_marginals γ
end RegularPointCoordinates
end

 
section
open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
 
noncomputable def wassersteinEDist (ν σ : Measure X) : ℝ≥0∞ :=
  wassersteinSq ν σ ^ (1/(2:ℝ))
 theorem wassersteinSq_eq_iInf_coupling (ν σ : Measure X) :
    wassersteinSq ν σ = ⨅ π : {π : Measure (X×X) //
      π.map Prod.fst = ν ∧ π.map Prod.snd = σ}, transportCost π.1 := by
  apply le_antisymm
  · exact le_iInf fun π => wassersteinSq_le_cost π.2.1 π.2.2
  · apply le_sInf
    rintro _ ⟨π,h0,h1,rfl⟩
    exact iInf_le (fun π : {π : Measure (X×X) //
      π.map Prod.fst = ν ∧ π.map Prod.snd = σ} => transportCost π.1) ⟨π,h0,h1⟩
 theorem wassersteinEDist_eq_iInf_coupling (ν σ : Measure X) :
    wassersteinEDist ν σ = ⨅ π : {π : Measure (X×X) //
      π.map Prod.fst = ν ∧ π.map Prod.snd = σ}, transportCost π.1 ^ (1/(2:ℝ)) := by
  change ENNReal.orderIsoRpow (1/(2:ℝ)) (by norm_num) (wassersteinSq ν σ) = _
  rw [wassersteinSq_eq_iInf_coupling,OrderIso.map_iInf]
  rfl
 theorem wassersteinEDist_le_cost {ν σ : Measure X} {π : Measure (X×X)}
    (h0 : π.map Prod.fst = ν) (h1 : π.map Prod.snd = σ) :
    wassersteinEDist ν σ ≤ transportCost π ^ (1/(2:ℝ)) :=
  ENNReal.rpow_le_rpow (wassersteinSq_le_cost h0 h1) (by norm_num)
variable [BorelSpace X] [SeparableSpace X]
 theorem transportCost_swap (π : Measure (X×X)) : transportCost (π.map Prod.swap) = transportCost π := by
  rw [transportCost,lintegral_map (by fun_prop) measurable_swap]
  simp only [Prod.swap, dist_comm,transportCost]
 theorem wassersteinEDist_symm (ν σ : Measure X) : wassersteinEDist ν σ = wassersteinEDist σ ν := by
  have hh : ∀ ν σ : Measure X, wassersteinEDist ν σ ≤ wassersteinEDist σ ν := by
    intro ν σ
    conv_rhs => rw [wassersteinEDist_eq_iInf_coupling]
    apply le_iInf
    intro π
    have h0 : (π.1.map Prod.swap).map Prod.fst = ν := by
      rw [Measure.map_map measurable_fst measurable_swap]
      exact π.2.2
    have h1 : (π.1.map Prod.swap).map Prod.snd = σ := by
      rw [Measure.map_map measurable_snd measurable_swap]
      exact π.2.1
    simpa only [transportCost_swap] using wassersteinEDist_le_cost h0 h1
  exact le_antisymm (hh ν σ) (hh σ ν)
 theorem wassersteinSq_self (ν : Measure X) : wassersteinSq ν ν = 0 := by
  have h0 : (ν.map (fun x => (x,x))).map Prod.fst = ν := by
    rw [Measure.map_map measurable_fst (by fun_prop : Measurable (fun x : X => (x,x)))]
    exact Measure.map_id
  have h1 : (ν.map (fun x => (x,x))).map Prod.snd = ν := by
    rw [Measure.map_map measurable_snd (by fun_prop : Measurable (fun x : X => (x,x)))]
    exact Measure.map_id
  apply le_antisymm ((wassersteinSq_le_cost h0 h1).trans _) bot_le
  rw [transportCost,lintegral_map (by fun_prop) (by fun_prop : Measurable (fun x : X => (x,x)))]
  simp
 theorem wassersteinEDist_self (ν : Measure X) : wassersteinEDist ν ν = 0 := by
  simp only [wassersteinEDist,wassersteinSq_self,ENNReal.zero_rpow_of_pos (by norm_num : 0 < 1/(2:ℝ))]
variable [StandardBorelSpace X] [Nonempty X]
 theorem wassersteinEDist_triangle (ν η σ : Measure X) [IsFiniteMeasure ν] [IsFiniteMeasure η] :
    wassersteinEDist ν σ ≤ wassersteinEDist ν η+wassersteinEDist η σ := by
  conv_rhs => rw [wassersteinEDist_eq_iInf_coupling,wassersteinEDist_eq_iInf_coupling]
  apply ENNReal.le_iInf_add_iInf
  intro π κ
  have : IsFiniteMeasure (π.1.map Prod.fst) := π.2.1.symm ▸ inferInstance
  have : IsFiniteMeasure π.1 := Measure.isFiniteMeasure_of_map measurable_fst.aemeasurable
  have : IsFiniteMeasure (κ.1.map Prod.fst) := κ.2.1.symm ▸ inferInstance
  have : IsFiniteMeasure κ.1 := Measure.isFiniteMeasure_of_map measurable_fst.aemeasurable
  obtain ⟨ξ,_,h0,h1,hc⟩ := exists_coupling_triangle π.1 κ.1 π.2.1 π.2.2 κ.2.1 κ.2.2
  exact (wassersteinEDist_le_cost h0 h1).trans hc
end RegularPointCoordinates
end

 
section
open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Topology
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]
 theorem FiniteSecondMoment.integrable_dist_sq {ν : Measure X} [IsFiniteMeasure ν]
    (hν : FiniteSecondMoment ν) (p : X) : Integrable (fun x => dist p x^2) ν := by
  obtain ⟨o,ho⟩ := hν
  have ho' : Integrable (fun x => dist o x^2) ν := by
    apply (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
      (Eventually.of_forall fun _ => sq_nonneg _)).mp
    simpa only [ENNReal.ofReal_pow dist_nonneg,dist_comm o] using ho.ne
  apply ((integrable_const (2*dist p o^2)).add (ho'.const_mul 2)).mono' (by fun_prop)
  filter_upwards with x
  simp only [Pi.add_apply,Real.norm_eq_abs,abs_pow,abs_of_nonneg dist_nonneg]
  have hd := dist_triangle p o x
  nlinarith [dist_nonneg (x := p) (y := x),sq_nonneg (dist p o-dist o x)]
 theorem finite_second_moment_cost {ν σ : Measure X} [IsFiniteMeasure ν] [IsFiniteMeasure σ]
    (hν : FiniteSecondMoment ν) (hσ : FiniteSecondMoment σ)
    {π : Measure (X×X)} (h0 : π.map Prod.fst = ν) (h1 : π.map Prod.snd = σ) :
    transportCost π ≠ ∞ := by
  obtain ⟨p,hp⟩ := hν
  have hν' : FiniteSecondMoment ν := ⟨p,hp⟩
  have hfin (τ : Measure X) [IsFiniteMeasure τ] (hτ : FiniteSecondMoment τ) :
      (∫⁻x, ENNReal.ofReal (dist p x)^2 ∂τ) ≠ ∞ := by
    have hi := hτ.integrable_dist_sq p
    have he := (lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable
      (Eventually.of_forall fun _ => sq_nonneg _)).mpr hi
    simpa only [ENNReal.ofReal_pow dist_nonneg] using he
  have hb := transportCost_le_marginal_moments π p
  rw [h0,h1] at hb
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top (by norm_num) (hfin ν hν'),ENNReal.mul_ne_top (by norm_num) (hfin σ hσ)⟩) hb
 theorem wassersteinSq_finite {ν σ : Measure X} [IsProbabilityMeasure ν] [IsProbabilityMeasure σ]
    (hν : FiniteSecondMoment ν) (hσ : FiniteSecondMoment σ) : wassersteinSq ν σ ≠ ∞ := by
  have h0 : (ν.prod σ).map Prod.fst = ν := by simp only [Measure.map_fst_prod,measure_univ,one_smul]
  have h1 : (ν.prod σ).map Prod.snd = σ := by simp only [Measure.map_snd_prod,measure_univ,one_smul]
  exact wassersteinSq_ne_top h0 h1 (finite_second_moment_cost hν hσ h0 h1)
 theorem wassersteinEDist_finite {ν σ : Measure X} [IsProbabilityMeasure ν] [IsProbabilityMeasure σ]
    (hν : FiniteSecondMoment ν) (hσ : FiniteSecondMoment σ) : wassersteinEDist ν σ ≠ ∞ :=
  ENNReal.rpow_ne_top_of_nonneg (by norm_num) (wassersteinSq_finite hν hσ)
 theorem coupling_cost_zero_endpoints {ν σ : Measure X} {π : Measure (X×X)}
    (h0 : π.map Prod.fst = ν) (h1 : π.map Prod.snd = σ) (hc : transportCost π = 0) : ν = σ := by
  have hz : ∀ᵐ xy ∂π, ENNReal.ofReal (dist xy.1 xy.2)^2 = 0 :=
    (lintegral_eq_zero_iff (by fun_prop)).mp hc
  have he : Prod.fst =ᵐ[π] (Prod.snd : X×X → X) := by
    filter_upwards [hz] with xy hxy
    have hd : ENNReal.ofReal (dist xy.1 xy.2) = 0 := (pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0)).mp hxy
    exact dist_eq_zero.mp (le_antisymm (ENNReal.ofReal_eq_zero.mp hd) dist_nonneg)
  exact h0.symm.trans ((Measure.map_congr he).trans h1)
 theorem wassersteinEDist_eq_zero_iff_optimal {ν σ : Measure X} {π : Measure (X×X)}
    (ho : IsOptimalCoupling ν σ π) : wassersteinEDist ν σ = 0 ↔ ν = σ := by
  constructor
  · intro h
    have hW : wassersteinSq ν σ = 0 := by
      exact (ENNReal.rpow_eq_zero_iff_of_pos (by norm_num : 0 < 1/(2:ℝ))).mp h
    exact coupling_cost_zero_endpoints ho.1 ho.2.1 ((wassersteinSq_eq_cost ho).symm.trans hW)
  · rintro rfl
    exact wassersteinEDist_self _
attribute [local instance] pathBorel pathBorelSpace
 theorem FullCD.wassersteinEDist_eq_zero_iff (μ : Measure X) (K : ℝ) (n : ℕ)
    (hcd : FullCD μ K n) (ν σ : Measure X) [IsProbabilityMeasure ν] [IsProbabilityMeasure σ]
    (hν : ν ≪ μ) (hσ : σ ≪ μ) (hmν : FiniteSecondMoment ν) (hmσ : FiniteSecondMoment σ) :
    wassersteinEDist ν σ = 0 ↔ ν = σ := by
  obtain ⟨plan,_,_,ho,_⟩ := hcd ν σ inferInstance inferInstance hν hσ hmν hmσ
  exact wassersteinEDist_eq_zero_iff_optimal ho
end RegularPointCoordinates
end

 
section
open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Topology
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
 
def ACWassersteinProbability (μ : Measure X) :=
  {ν : Measure X // IsProbabilityMeasure ν ∧ ν ≪ μ ∧ FiniteSecondMoment ν}
namespace ACWassersteinProbability
variable (μ : Measure X)
instance prob (ν : ACWassersteinProbability μ) : IsProbabilityMeasure ν.val := ν.property.1
 theorem finite [SeparableSpace X] (ν σ : ACWassersteinProbability μ) :
    wassersteinEDist ν.val σ.val ≠ ∞ := wassersteinEDist_finite ν.property.2.2 σ.property.2.2
 

@[instance_reducible] noncomputable def metric [ProperSpace X] [SeparableSpace X] (K : ℝ) (n : ℕ)
    (hcd : FullCD μ K n) : MetricSpace (ACWassersteinProbability μ) where
  dist ν σ := (wassersteinEDist ν.val σ.val).toReal
  dist_self ν := by rw [wassersteinEDist_self,ENNReal.toReal_zero]
  dist_comm ν σ := by rw [wassersteinEDist_symm]
  dist_triangle ν σ τ := by
    let : Nonempty X := nonempty_of_isProbabilityMeasure ν.val
    have hh := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨finite μ ν σ,finite μ σ τ⟩)
      (wassersteinEDist_triangle ν.val σ.val τ.val)
    simpa only [ENNReal.toReal_add (finite μ ν σ) (finite μ σ τ)] using hh
  eq_of_dist_eq_zero := by
    intro ν σ h
    apply Subtype.ext
    apply (hcd.wassersteinEDist_eq_zero_iff μ K n ν.val σ.val ν.property.2.1 σ.property.2.1
      ν.property.2.2 σ.property.2.2).mp
    rw [← ENNReal.ofReal_toReal (finite μ ν σ),h,ENNReal.ofReal_zero]
end ACWassersteinProbability
 
 theorem absolutelyContinuous_of_dist_le {Y Z : Type*} [PseudoMetricSpace Y] [PseudoMetricSpace Z]
    {f : ℝ → Y} {g : ℝ → Z} {a b : ℝ} (hg : AbsolutelyContinuousOnInterval g a b)
    (h : ∀ s ∈ uIcc a b, ∀ t ∈ uIcc a b, dist (f s) (f t) ≤ dist (g s) (g t)) :
    AbsolutelyContinuousOnInterval f a b := by
  rw [absolutelyContinuousOnInterval_iff] at hg ⊢
  intro ε hε
  obtain ⟨δ,hδ,hg⟩ := hg ε hε
  refine ⟨δ,hδ,?_⟩
  intro E hE hlen
  apply lt_of_le_of_lt _ (hg E hE hlen)
  apply Finset.sum_le_sum
  intro i hi
  exact h _ (hE.1 i hi).1 _ (hE.1 i hi).2
end RegularPointCoordinates
end

 
open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Topology
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
 

noncomputable def NoncollapsedRCD.heatProbability (K : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (p : X) (f : Lp ℝ 2 (hausdorff n X)) (hf0 : 0 ≤ f)
    (hfs : ∃ r : ℝ, ∀ᵐ x ∂hausdorff n X, f x ≠ 0 → dist p x ≤ r)
    (hfm : (∫x, f x ∂hausdorff n X) = 1) (t : ℝ) :
    ACWassersteinProbability (hausdorff n X) := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let : IsLocallyFiniteMeasure (hausdorff n X) :=
    locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  let ν := heatMeasure (hausdorff n X) hX.quadratic (max t 0) f
  have h := hX.heat_law K n hn p f hf0 hfs hfm (max t 0) (le_max_right t 0)
  exact ⟨ν,h.1,h.2.1,h.2.2.1⟩
 

 theorem NoncollapsedRCD.heat_probability_absolutelyContinuous (K : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (p : X) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) :=
      locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    letI := ACWassersteinProbability.metric (hausdorff n X) K n hX.cd
    ∀ (f : Lp ℝ 2 (hausdorff n X)) (hf0 : 0 ≤ f)
      (hfs : ∃ r : ℝ, ∀ᵐ x ∂hausdorff n X, f x ≠ 0 → dist p x ≤ r)
      (hfm : (∫x, f x ∂hausdorff n X) = 1), ∀ C : ℝ≥0,
      (∀ᵐ x ∂hausdorff n X, |f x| ≤ C) → ∀ T : ℝ, 0 ≤ T →
      AbsolutelyContinuousOnInterval (hX.heatProbability K n hn p f hf0 hfs hfm) 0 T := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let : IsLocallyFiniteMeasure (hausdorff n X) :=
    locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  let := ACWassersteinProbability.metric (hausdorff n X) K n hX.cd
  let μ := hausdorff n X
  intro f hf0 hfs hfm C hfC T hT
  let E := fun t => boltzmannEntropy μ (heatMeasure μ hX.quadratic t f)
  let ρ := hX.heatProbability K n hn p f hf0 hfs hfm
  obtain ⟨r,hfr⟩ := hfs
  obtain ⟨A,B,hA,hB,hvol⟩ := hX.exponential_volume K n hn p
  have hfi := lp_integrable_of_bounded_support μ f p hfr
  have hE : AbsolutelyContinuousOnInterval E 0 T := by
    simpa only [E,boltzmannEntropy_heatMeasure_eq μ hX.quadratic f hf0] using
      heatAt_entropy_absolutelyContinuous_nonneg μ hX.quadratic p hA hB hvol f hf0 hfi
        hfr le_rfl hT
  have hG : AbsolutelyContinuousOnInterval (fun t => t-E t) 0 T :=
    (LipschitzWith.id.lipschitzOnWith.absolutelyContinuousOnInterval).sub hE
  apply absolutelyContinuous_of_dist_le hG
  have hb (s t : ℝ) (hs : s ∈ uIcc 0 T) (hst : s < t) :
      dist (ρ s) (ρ t) ≤ dist (s-E s) (t-E t) := by
    have hs0 : 0 ≤ s := ((uIcc_of_le hT).symm ▸ hs).1
    have ht0 := hs0.trans hst.le
    have h := (hX.heat_wasserstein_entropy_action K n hn p f hf0 ⟨r,hfr⟩ hfm C hfC s t hs0 hst).2
    change (wassersteinSq _ _).toReal ≤ (t-s)*(E s-E t) at h
    have hEn : 0 ≤ E s-E t := by nlinarith [ENNReal.toReal_nonneg (a := wassersteinSq
      (heatMeasure μ hX.quadratic s f) (heatMeasure μ hX.quadratic t f))]
    have hg : s-E s ≤ t-E t := by linarith
    change (wassersteinEDist (heatMeasure μ hX.quadratic (max s 0) f)
      (heatMeasure μ hX.quadratic (max t 0) f)).toReal ≤ _
    rw [max_eq_left hs0,max_eq_left ht0,wassersteinEDist,← ENNReal.toReal_rpow,← Real.sqrt_eq_rpow,
      Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hg)]
    have hsqrt := Real.sq_sqrt (ENNReal.toReal_nonneg (a := wassersteinSq
      (heatMeasure μ hX.quadratic s f) (heatMeasure μ hX.quadratic t f)))
    have hnon := Real.sqrt_nonneg (wassersteinSq
      (heatMeasure μ hX.quadratic s f) (heatMeasure μ hX.quadratic t f)).toReal
    nlinarith [sq_nonneg ((t-s)-(E s-E t))]
  intro s hs t ht
  rcases lt_trichotomy s t with hst | rfl | hts
  · exact hb s t hs hst
  · simp
  · simpa only [dist_comm] using hb t s ht hts
end RegularPointCoordinates

end OAI
