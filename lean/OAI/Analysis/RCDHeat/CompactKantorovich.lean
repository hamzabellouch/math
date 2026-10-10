import Mathlib
import OAI.Analysis.RCDHeat.CompactCostTransform
import OAI.Analysis.RCDHeat.EntropyWassersteinGeodesic
import OAI.Analysis.RCDHeat.SobolevTestPlan

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: CompactKantorovich, CompactDualSlackness, CompactSquaredCost, KantorovichTestPlan, CompactOptimalPotentials. -/



namespace RegularPointCoordinates

section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal CompactlySupported
universe u v
variable {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
  [CompactSpace X] [CompactSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
  [BorelSpace X] [BorelSpace Y]
  (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

 theorem transportEnvelope_support (h : C(X×Y,ℝ)) :
    ∃ L : C(X×Y,ℝ) →ₗ[ℝ] ℝ, L h = transportEnvelope μ ν h ∧
      (∀ f : C(X×Y,ℝ), 0 ≤ f → 0 ≤ L f) ∧
      (∀ f : C(X,ℝ), ∀ g : C(Y,ℝ), L (separatedSum f g) = (∫ x, f x ∂μ)+(∫ y, g y ∂ν)) := by
  obtain ⟨L,hL,hp⟩ := exists_support_sublinear (transportEnvelope μ ν) (transportEnvelope_zero μ ν)
    (transportEnvelope_add μ ν) (fun c hc f => transportEnvelope_smul μ ν hc f) h
  refine ⟨L,hL,?_,?_⟩
  · intro f hf
    have hn := (hp (-f)).trans (transportEnvelope_le μ ν (-f) 0 0 (by
      intro xy
      change -f xy ≤ 0+0
      have hh : (0:ℝ) ≤ f xy := hf xy
      linarith))
    simpa only [ContinuousMap.zero_apply, integral_zero, add_zero, map_neg, neg_nonpos] using hn
  · intro f g
    apply le_antisymm ((hp _).trans_eq (transportEnvelope_separatedSum μ ν f g))
    have he : -(separatedSum f g) = separatedSum (-f) (-g) := by ext xy; simp [separatedSum]; ring
    have hn := hp (-(separatedSum f g))
    rw [map_neg, he, transportEnvelope_separatedSum] at hn
    simp only [ContinuousMap.neg_apply, integral_neg] at hn
    linarith

 theorem compact_transport_primal_dual (h : C(X×Y,ℝ)) :
    ∃ π : Measure (X×Y), IsProbabilityMeasure π ∧ π.map Prod.fst = μ ∧
      π.map Prod.snd = ν ∧ (∫ xy, h xy ∂π) = transportEnvelope μ ν h := by
  obtain ⟨L,hL,hpos,hsep⟩ := transportEnvelope_support μ ν h
  let j : C_c(X×Y,ℝ) →ₗ[ℝ] C(X×Y,ℝ) :=
    { toFun := fun f => f.toContinuousMap
      map_add' := fun f g => by ext; rfl
      map_smul' := fun c f => by ext; rfl }
  let Λ : C_c(X×Y,ℝ) →ₚ[ℝ] ℝ := PositiveLinearMap.mk₀ (L.comp j) (fun f hf => hpos (j f) hf)
  let π : Measure (X×Y) := RealRMK.rieszMeasure Λ
  have he (f : C(X×Y,ℝ)) : (∫ xy, f xy ∂π) = L f := by
    let fc : C_c(X×Y,ℝ) := ⟨f, HasCompactSupport.of_compactSpace f⟩
    exact RealRMK.integral_rieszMeasure Λ fc
  have h1 : L (1 : C(X×Y,ℝ)) = 1 := by
    have heq : (1 : C(X×Y,ℝ)) = separatedSum (1 : C(X,ℝ)) (0 : C(Y,ℝ)) := by
      ext; simp [separatedSum]
    rw [heq, hsep]
    simp
  have hprob : IsProbabilityMeasure π := by
    apply isProbabilityMeasure_iff_real.mpr
    have hi := (he 1).trans h1
    simpa using hi
  let : IsProbabilityMeasure π := hprob
  refine ⟨π,hprob,?_,?_,(he h).trans hL⟩
  · apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    rw [integral_map measurable_fst.aemeasurable (show AEStronglyMeasurable (fun x => f x) (π.map Prod.fst) from f.continuous.aestronglyMeasurable)]
    have hx : (∫ xy, f xy.1 ∂π) = L (separatedSum f.toContinuousMap (0:C(Y,ℝ))) := by
      convert he (separatedSum f.toContinuousMap (0:C(Y,ℝ))) using 1
      congr 1
      funext xy
      change f xy.1 = f xy.1+0
      exact (add_zero _).symm
    rw [hx, hsep]
    simp
  · apply Measure.ext_of_integral_eq_on_compactlySupported
    intro g
    rw [integral_map measurable_snd.aemeasurable (show AEStronglyMeasurable (fun x => g x) (π.map Prod.snd) from g.continuous.aestronglyMeasurable)]
    have hx : (∫ xy, g xy.2 ∂π) = L (separatedSum (0:C(X,ℝ)) g.toContinuousMap) := by
      convert he (separatedSum (0:C(X,ℝ)) g.toContinuousMap) using 1
      congr 1
      funext xy
      change g xy.2 = 0+g xy.2
      exact (zero_add _).symm
    rw [hx, hsep]
    simp
end

 
section
open Set Filter MeasureTheory
open scoped NNReal Topology
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace X] [CompactSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
 theorem compact_coupling_separated_integral (π : Measure (X×Y)) [IsProbabilityMeasure π]
    (hfst : π.map Prod.fst = μ) (hsnd : π.map Prod.snd = ν)
    (f : C(X,ℝ)) (g : C(Y,ℝ)) :
    (∫xy, separatedSum f g xy ∂π) = (∫x, f x ∂μ)+(∫y, g y ∂ν) := by
  have hf : Integrable (fun xy : X×Y => f xy.1) π :=
    (f.continuous.comp continuous_fst).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hg : Integrable (fun xy : X×Y => g xy.2) π :=
    (g.continuous.comp continuous_snd).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change (∫xy, f xy.1+g xy.2 ∂π) = _
  rw [integral_add hf hg, ←hfst, ←hsnd,
    integral_map measurable_fst.aemeasurable f.continuous.aestronglyMeasurable,
    integral_map measurable_snd.aemeasurable g.continuous.aestronglyMeasurable]

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
 theorem compact_dual_slackness (h : C(X×Y,ℝ)) (π : Measure (X×Y)) [IsProbabilityMeasure π]
    (hfst : π.map Prod.fst = μ) (hsnd : π.map Prod.snd = ν)
    (hπ : (∫xy, h xy ∂π) = transportEnvelope μ ν h)
    (f : C(X,ℝ)) (g : C(Y,ℝ)) (had : h ≤ separatedSum f g)
    (hdual : transportEnvelope μ ν h = (∫x, f x ∂μ)+(∫y, g y ∂ν)) :
    ∀ᵐ xy ∂π, h xy = f xy.1+g xy.2 := by
  have hi := compact_continuous_integrable π (separatedSum f g-h)
  have hzero : (∫xy, (separatedSum f g-h) xy ∂π) = 0 := by
    simp only [ContinuousMap.sub_apply]
    rw [integral_sub (compact_continuous_integrable π (separatedSum f g))
      (compact_continuous_integrable π h),compact_coupling_separated_integral μ ν π hfst hsnd,
      hπ,hdual,sub_self]
  have hn : 0 ≤ᵐ[π] (fun xy => (separatedSum f g-h) xy) :=
    Filter.Eventually.of_forall (fun xy => sub_nonneg.mpr (had xy))
  have he := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp hzero
  filter_upwards [he] with xy hxy
  change f xy.1+g xy.2-h xy = 0 at hxy
  linarith

 

 theorem compact_transport_primal_dual_attained (h : C(X×Y,ℝ)) {K : ℝ≥0}
    (hK : LipschitzWith K h) :
    ∃ π : Measure (X×Y), ∃ f : C(X,ℝ), ∃ g : C(Y,ℝ),
      IsProbabilityMeasure π ∧ π.map Prod.fst = μ ∧ π.map Prod.snd = ν ∧
      LipschitzWith K f ∧ LipschitzWith K g ∧
      (∀ x, |f x| ≤ 2*‖h‖) ∧ (∀ y, |g y| ≤ 3*‖h‖) ∧
      h ≤ separatedSum f g ∧ (∀ᵐ xy ∂π, h xy = f xy.1+g xy.2) ∧
      ((∫xy, h xy ∂π) = transportEnvelope μ ν h) ∧
      transportEnvelope μ ν h = (∫x, f x ∂μ)+(∫y, g y ∂ν) := by
  obtain ⟨π,hprob,hfst,hsnd,hπ⟩ := compact_transport_primal_dual μ ν h
  let : IsProbabilityMeasure π := hprob
  obtain ⟨f,g,hf,hg,hfb,hgb,had,hdual⟩ := compact_transport_dual_attainment μ ν h hK
  exact ⟨π,f,g,hprob,hfst,hsnd,hf,hg,hfb,hgb,had,
    compact_dual_slackness μ ν h π hfst hsnd hπ f g had hdual,hπ,hdual⟩

end

 
section
open Set Filter MeasureTheory
open scoped NNReal Topology
variable {X : Type*} [MetricSpace X] [CompactSpace X]

noncomputable def compactDistanceCost : C(X×X,ℝ) :=
  ⟨fun xy => dist xy.1 xy.2, continuous_fst.dist continuous_snd⟩

noncomputable def compactSquaredCost : C(X×X,ℝ) :=
  ⟨fun xy => dist xy.1 xy.2^2/2, (continuous_fst.dist continuous_snd).pow 2 |>.div_const 2⟩

 theorem compactSquaredCost_lipschitz :
    LipschitzWith (2*⟨‖compactDistanceCost (X := X)‖, norm_nonneg _⟩)
      (compactSquaredCost (X := X)) := by
  apply LipschitzWith.of_dist_le_mul
  rintro ⟨x,y⟩ ⟨z,w⟩
  let D := ‖compactDistanceCost (X := X)‖
  have hxy : dist x y ≤ D := by
    simpa only [D,compactDistanceCost,ContinuousMap.coe_mk,Real.norm_eq_abs,abs_of_nonneg dist_nonneg]
      using (compactDistanceCost (X := X)).norm_coe_le_norm (x,y)
  have hzw : dist z w ≤ D := by
    simpa only [D,compactDistanceCost,ContinuousMap.coe_mk,Real.norm_eq_abs,abs_of_nonneg dist_nonneg]
      using (compactDistanceCost (X := X)).norm_coe_le_norm (z,w)
  have h1 : dist x y-dist z w ≤ 2*max (dist x z) (dist y w) := by
    have ht := dist_triangle4 x z w y
    rw [dist_comm w y] at ht
    have ha := le_max_left (dist x z) (dist y w)
    have hb := le_max_right (dist x z) (dist y w)
    linarith
  have h2 : dist z w-dist x y ≤ 2*max (dist x z) (dist y w) := by
    have ht := dist_triangle4 z x y w
    rw [dist_comm z x] at ht
    have ha := le_max_left (dist x z) (dist y w)
    have hb := le_max_right (dist x z) (dist y w)
    linarith
  have hd : 0 ≤ max (dist x z) (dist y w) := le_trans dist_nonneg (le_max_left _ _)
  have hsum : 0 ≤ dist x y+dist z w := add_nonneg dist_nonneg dist_nonneg
  have hmul1 := mul_le_mul_of_nonneg_right h1 hsum
  have hmul2 := mul_le_mul_of_nonneg_right h2 hsum
  have hsumBound := mul_le_mul_of_nonneg_left (add_le_add hxy hzw) hd
  change |dist x y^2/2-dist z w^2/2| ≤ (2*D)*max (dist x z) (dist y w)
  rw [abs_le]
  constructor <;> nlinarith only [hmul1,hmul2,hsumBound]

variable [MeasurableSpace X] [BorelSpace X]
  (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

 

 theorem compact_squared_cost_potentials :
    ∃ π : Measure (X×X), ∃ φ ψ : C(X,ℝ),
      IsProbabilityMeasure π ∧ π.map Prod.fst = μ ∧ π.map Prod.snd = ν ∧
      (∃ K : ℝ≥0, LipschitzWith K φ ∧ LipschitzWith K ψ) ∧
      (∀ x y, φ x+ψ y ≤ dist x y^2/2) ∧
      (∀ᵐ xy ∂π, φ xy.1+ψ xy.2 = dist xy.1 xy.2^2/2) ∧
      (∫xy, dist xy.1 xy.2^2/2 ∂π) =
        -transportEnvelope μ ν (-compactSquaredCost (X := X)) := by
  obtain ⟨π,f,g,hprob,hfst,hsnd,hf,hg,_,_,had,hcontact,hπ,_⟩ :=
    compact_transport_primal_dual_attained μ ν (-compactSquaredCost (X := X))
      compactSquaredCost_lipschitz.neg
  refine ⟨π,-f,-g,hprob,hfst,hsnd,⟨_,hf.neg,hg.neg⟩,?_,?_,?_⟩
  · intro x y
    have hh := had (x,y)
    change -(dist x y^2/2) ≤ f x+g y at hh
    change -f x+-g y ≤ dist x y^2/2
    linarith
  · filter_upwards [hcontact] with xy hh
    change -(dist xy.1 xy.2^2/2) = f xy.1+g xy.2 at hh
    change -f xy.1+-g xy.2 = dist xy.1 xy.2^2/2
    linarith
  · change (∫xy, -(dist xy.1 xy.2^2/2) ∂π) = _ at hπ
    rw [integral_neg] at hπ
    linarith
end

 
section
open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology
variable {X : Type*} [MetricSpace X]

 
 theorem IsGeodesic.kantorovich_increment {γ : C(Time,X)} (hγ : IsGeodesic γ)
    {φ ψ : X → ℝ} (had : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    (hcontact : φ (γ 0)+ψ (γ 1) = dist (γ 0) (γ 1)^2/2) (t : Time) :
    ((t:ℝ)-(t:ℝ)^2/2)*dist (γ 0) (γ 1)^2 ≤ φ (γ 0)-φ (γ t) := by
  have hdist : dist (γ t) (γ 1) = (1-(t:ℝ))*dist (γ 0) (γ 1) := by
    rw [hγ]
    change |(t:ℝ)-1| * _ = _
    rw [abs_of_nonpos (sub_nonpos.mpr t.2.2)]
    ring
  have hh := had (γ t) (γ 1)
  rw [hdist] at hh
  nlinarith only [hh,hcontact]

variable [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

 

 theorem IsRelaxedSlope.kantorovich_action_le_pairing (μ : Measure X)
    [ProperSpace X] [μ.Regular] (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    {u G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ u G)
    {φ ψ : X → ℝ} (hu : φ =ᵐ[μ] u)
    (had : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    (hcontact : ∀ᵐ γ ∂π, φ (γ 0)+ψ (γ 1) = dist (γ 0) (γ 1)^2/2) :
    (∫γ : C(Time,X), dist (γ 0) (γ 1)^2 ∂π) ≤
      ∫γ : C(Time,X), dist (γ 0) (γ 1)*G (γ 0) ∂π := by
  have hrep (t : Time) : ∀ᵐ γ ∂π, φ (γ t) = u (γ t) :=
    ae_of_ae_map (measurable_path_eval t).aemeasurable
      ((Measure.absolutelyContinuous_of_le_smul (hcomp t)).ae_eq hu)
  have hinc (t : Time) :
      ((t:ℝ)-(t:ℝ)^2/2)*(∫γ : C(Time,X),dist (γ 0) (γ 1)^2 ∂π) ≤
        ∫γ : C(Time,X), |u (γ t)-u (γ 0)| ∂π := by
    have hiu (s : Time) : MemLp (fun γ : C(Time,X) => u (γ s)) 2 π :=
      compressionPullback_memLp μ π _ (measurable_path_eval s) hC (hcomp s) u
    have hiD : Integrable (fun γ : C(Time,X) => dist (γ 0) (γ 1)^2) π :=
      (memLp_two_iff_integrable_sq hD.aestronglyMeasurable).mp hD
    rw [←integral_const_mul]
    apply integral_mono_ae (hiD.const_mul _) (((hiu t).sub (hiu 0)).integrable (by norm_num)).abs
    filter_upwards [hgeo,hcontact,hrep 0,hrep t] with γ hg hc h0 ht
    have hh := hg.kantorovich_increment had hc t
    rw [h0,ht] at hh
    exact hh.trans (by simpa only [Pi.sub_apply,abs_sub_comm] using (le_abs_self (u (γ 0)-u (γ t))))
  let A := ∫γ : C(Time,X),dist (γ 0) (γ 1)^2 ∂π
  have htend : Tendsto (fun t : ℝ => (1-t/2)*A) (𝓝[>] (0:ℝ)) (𝓝 A) := by
    have hh : Continuous (fun t : ℝ => (1-t/2)*A) := by fun_prop
    simpa only [zero_div,sub_zero,one_mul] using (hh.continuousAt (x := (0:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_forall_pos_le_add
  intro ε hε
  apply le_of_tendsto htend
  have hi := hG.testPlan_initial_bound μ π hgeo hC hcomp hD hε
  have hsmall : ∀ᶠ t in 𝓝[>] (0:ℝ), t < 1 :=
    (gt_mem_nhds (show (0:ℝ) < 1 from zero_lt_one)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hi,hsmall,self_mem_nhdsWithin] with t ht ht1 ht0
  have ht01 : t ∈ Icc (0:ℝ) 1 := ⟨le_of_lt ht0,le_of_lt ht1⟩
  have hb := hinc (⟨t,ht01⟩:Time)
  have hge (γ : C(Time,X)) : geodesicExtension γ t = γ (⟨t,ht01⟩:Time) :=
    geodesicExtension_eq γ (⟨t,ht01⟩:Time)
  simp_rw [hge] at ht
  apply le_trans _ ht.le
  apply (le_div_iff₀ ht0).mpr
  change (1-t/2)*A*t ≤ _
  convert hb using 1
  dsimp only
  ring

 

 theorem IsRelaxedSlope.kantorovich_action_le_gradient_square (μ : Measure X)
    [ProperSpace X] [μ.Regular] (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    {u G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ u G)
    {φ ψ : X → ℝ} (hu : φ =ᵐ[μ] u)
    (had : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    (hcontact : ∀ᵐ γ ∂π, φ (γ 0)+ψ (γ 1) = dist (γ 0) (γ 1)^2/2) :
    (∫γ : C(Time,X), dist (γ 0) (γ 1)^2 ∂π) ≤
      ∫γ : C(Time,X), G (γ 0)^2 ∂π := by
  have hb := hG.kantorovich_action_le_pairing μ π hgeo hC hcomp hD hu had hcontact
  have hiG : MemLp (fun γ : C(Time,X) => G (γ 0)) 2 π :=
    compressionPullback_memLp μ π _ (measurable_path_eval 0) hC (hcomp 0) G
  have hiD2 := (memLp_two_iff_integrable_sq hD.aestronglyMeasurable).mp hD
  have hiG2 := (memLp_two_iff_integrable_sq hiG.aestronglyMeasurable).mp hiG
  have hiDG := hD.integrable_mul hiG
  have hy := integral_mono (hiDG.const_mul 2) (hiD2.add hiG2)
    (fun γ => show 2*(dist (γ 0) (γ 1)*G (γ 0)) ≤ dist (γ 0) (γ 1)^2+G (γ 0)^2 by
      nlinarith only [sq_nonneg (dist (γ 0) (γ 1)-G (γ 0))])
  simp only [Pi.add_apply,Pi.mul_apply,integral_const_mul,integral_add hiD2 hiG2] at hy
  linarith

end

 
open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

 theorem compact_transportCost_integral (π : Measure (X×X)) [IsFiniteMeasure π] :
    transportCost π = ENNReal.ofReal (∫xy : X×X, dist xy.1 xy.2^2 ∂π) := by
  have hi : Integrable (fun xy : X×X => dist xy.1 xy.2^2) π :=
    ((continuous_fst.dist continuous_snd).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ => sq_nonneg _)]
  simp only [transportCost,ENNReal.ofReal_pow dist_nonneg]

omit [MetricSpace X] [CompactSpace X] [BorelSpace X] in
 theorem coupling_probability_of_fst {μ : Measure X} [IsProbabilityMeasure μ]
    {π : Measure (X×X)} (hfst : π.map Prod.fst = μ) : IsProbabilityMeasure π := by
  constructor
  have hh := congrArg (fun m : Measure X => m univ) hfst
  simpa only [Measure.map_apply measurable_fst MeasurableSet.univ,preimage_univ,measure_univ] using hh

 theorem compact_contact_isOptimal {μ ν : Measure X} [IsProbabilityMeasure μ]
    {π : Measure (X×X)} (hfst : π.map Prod.fst = μ) (hsnd : π.map Prod.snd = ν)
    (φ ψ : C(X,ℝ)) (had : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    (hc : ∀ᵐ xy ∂π, φ xy.1+ψ xy.2 = dist xy.1 xy.2^2/2) :
    IsOptimalCoupling μ ν π := by
  let := coupling_probability_of_fst hfst
  refine ⟨hfst,hsnd,?_⟩
  intro π' hfst' hsnd'
  let := coupling_probability_of_fst hfst'
  have hi (ζ : Measure (X×X)) [IsFiniteMeasure ζ] :
      Integrable (fun xy : X×X => dist xy.1 xy.2^2) ζ :=
    ((continuous_fst.dist continuous_snd).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he := integral_congr_ae hc
  change (∫xy, separatedSum φ ψ xy ∂π) = _ at he
  rw [compact_coupling_separated_integral μ ν π hfst hsnd,integral_div] at he
  have hb := integral_mono (compact_continuous_integrable π' (separatedSum φ ψ))
    ((hi π').div_const 2) (fun xy => had xy.1 xy.2)
  change (∫xy,separatedSum φ ψ xy ∂π') ≤ (∫xy,dist xy.1 xy.2^2/2 ∂π') at hb
  rw [compact_coupling_separated_integral μ ν π' hfst' hsnd',integral_div] at hb
  rw [compact_transportCost_integral,compact_transportCost_integral]
  exact ENNReal.ofReal_le_ofReal (by linarith)

omit [CompactSpace X] [BorelSpace X] in
 theorem compact_optimal_cost_eq {μ ν : Measure X} {π π' : Measure (X×X)}
    (hp : IsOptimalCoupling μ ν π) (hq : IsOptimalCoupling μ ν π') :
    transportCost π = transportCost π' :=
  le_antisymm (hp.2.2 π' hq.1 hq.2.1) (hq.2.2 π hp.1 hp.2.1)

 

 theorem IsOptimalCoupling.compact_potentials (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {π : Measure (X×X)} (hp : IsOptimalCoupling μ ν π) :
    ∃ φ ψ : C(X,ℝ), (∃ K : ℝ≥0, LipschitzWith K φ ∧ LipschitzWith K ψ) ∧
      (∀ x y, φ x+ψ y ≤ dist x y^2/2) ∧
      (∀ᵐ xy ∂π, φ xy.1+ψ xy.2 = dist xy.1 xy.2^2/2) := by
  obtain ⟨π',φ,ψ,hprob,hfst,hsnd,hLip,had,hcontact,_⟩ := compact_squared_cost_potentials μ ν
  have hq := compact_contact_isOptimal hfst hsnd φ ψ had hcontact
  let := hprob
  let := coupling_probability_of_fst hp.1
  have he := compact_optimal_cost_eq hp hq
  rw [compact_transportCost_integral,compact_transportCost_integral] at he
  have he' := (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun _ => sq_nonneg _)
    (integral_nonneg fun _ => sq_nonneg _)).mp he
  have hec := integral_congr_ae hcontact
  change (∫xy,separatedSum φ ψ xy ∂π') = _ at hec
  rw [compact_coupling_separated_integral μ ν π' hfst hsnd,integral_div,←he'] at hec
  let h : C(X×X,ℝ) := compactSquaredCost-separatedSum φ ψ
  have hi := compact_continuous_integrable π h
  have hz : (∫xy,h xy ∂π) = 0 := by
    change (∫xy,compactSquaredCost xy-separatedSum φ ψ xy ∂π) = 0
    rw [integral_sub (compact_continuous_integrable π compactSquaredCost)
      (compact_continuous_integrable π (separatedSum φ ψ))]
    change (∫xy,dist xy.1 xy.2^2/2 ∂π)-(∫xy,separatedSum φ ψ xy ∂π) = 0
    rw [integral_div,
      compact_coupling_separated_integral μ ν π hp.1 hp.2.1,hec,sub_self]
  have hn : 0 ≤ᵐ[π] (fun xy => h xy) :=
    Eventually.of_forall (fun xy => sub_nonneg.mpr (had xy.1 xy.2))
  refine ⟨φ,ψ,hLip,had,?_⟩
  filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hn hi).mp hz] with xy hxy
  change dist xy.1 xy.2^2/2-(φ xy.1+ψ xy.2) = 0 at hxy
  linarith

end RegularPointCoordinates

end OAI
