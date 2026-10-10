import Mathlib
import OAI.Analysis.RCDHeat.UpperLipschitzEnvelope

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: CompactCostTransform, CompactTransportEnvelope, CompactLipschitzDual, CompactDualImprovement, CompactDualAttainment. -/



namespace RegularPointCoordinates

section
open Set Filter MeasureTheory
open scoped NNReal Topology
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace X] [CompactSpace Y]

 
noncomputable def compactCostTransform (h : C(X×Y,ℝ)) (g : C(Y,ℝ)) (x : X) : ℝ :=
  sSup (range (fun y : Y => h (x,y)-g y))

 theorem compactCostTransform_bdd (h : C(X×Y,ℝ)) (g : C(Y,ℝ)) (x : X) :
    BddAbove (range (fun y : Y => h (x,y)-g y)) := by
  refine ⟨‖h‖+‖g‖,?_⟩
  rintro _ ⟨y,rfl⟩
  have hh := (abs_le.mp (h.norm_coe_le_norm (x,y))).2
  have hg := (abs_le.mp (g.norm_coe_le_norm y)).1
  linarith

 theorem le_compactCostTransform (h : C(X×Y,ℝ)) (g : C(Y,ℝ)) (x : X) (y : Y) :
    h (x,y)-g y ≤ compactCostTransform h g x :=
  le_csSup (compactCostTransform_bdd h g x) (mem_range_self y)

omit [CompactSpace X] [CompactSpace Y] in
 theorem compactCostTransform_le [Nonempty Y] (h : C(X×Y,ℝ)) (g : C(Y,ℝ))
    (x : X) {a : ℝ} (ha : ∀ y, h (x,y)-g y ≤ a) : compactCostTransform h g x ≤ a := by
  apply csSup_le (range_nonempty _)
  rintro _ ⟨y,rfl⟩
  exact ha y

 theorem compactCostTransform_difference [Nonempty Y] (h : C(X×Y,ℝ)) (g : C(Y,ℝ))
    (x z : X) {a : ℝ} (ha : ∀ y, h (x,y)-h (z,y) ≤ a) :
    compactCostTransform h g x - compactCostTransform h g z ≤ a := by
  suffices hs : compactCostTransform h g x ≤ compactCostTransform h g z+a by linarith
  apply compactCostTransform_le
  intro y
  have hy := le_compactCostTransform h g z y
  linarith [ha y]

 theorem compactCostTransform_lipschitz [Nonempty Y] (h : C(X×Y,ℝ))
    {K : ℝ≥0} (hK : LipschitzWith K h) (g : C(Y,ℝ)) :
    LipschitzWith K (compactCostTransform h g) := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  rw [Real.dist_eq,abs_le]
  have hb (x z : X) : compactCostTransform h g x - compactCostTransform h g z ≤ (K:ℝ)*dist x z := by
    apply compactCostTransform_difference
    intro y
    have hh := hK.dist_le_mul (x,y) (z,y)
    simp only [Prod.dist_eq,dist_self,max_eq_left dist_nonneg,Real.dist_eq] at hh
    exact (le_abs_self _).trans hh
  constructor
  · have hz := hb z x
    rw [dist_comm z x] at hz
    linarith
  · exact hb x z

 theorem compactCostTransform_oscillation [Nonempty Y] (h : C(X×Y,ℝ)) (g : C(Y,ℝ))
    (x z : X) : |compactCostTransform h g x - compactCostTransform h g z| ≤ 2*‖h‖ := by
  have hb (x z : X) : compactCostTransform h g x - compactCostTransform h g z ≤ 2*‖h‖ := by
    apply compactCostTransform_difference
    intro y
    have hx := (abs_le.mp (h.norm_coe_le_norm (x,y))).2
    have hz := (abs_le.mp (h.norm_coe_le_norm (z,y))).1
    linarith
  rw [abs_le]
  constructor
  · linarith [hb z x]
  · exact hb x z

 theorem compactCostTransform_bounded [Nonempty Y]
    (h : C(X×Y,ℝ)) (g : C(Y,ℝ)) {A : ℝ} (hA : ∀ y, |g y| ≤ A) (x : X) :
    |compactCostTransform h g x| ≤ ‖h‖+A := by
  rw [abs_le]
  constructor
  · obtain ⟨y⟩ := ‹Nonempty Y›
    have hh := (abs_le.mp (h.norm_coe_le_norm (x,y))).1
    have hg := (abs_le.mp (hA y)).2
    have hl := le_compactCostTransform h g x y
    linarith
  · apply compactCostTransform_le
    intro y
    have hh := (abs_le.mp (h.norm_coe_le_norm (x,y))).2
    have hg := (abs_le.mp (hA y)).1
    linarith

end

 

 
section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
universe u v
variable {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
  [CompactSpace X] [CompactSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
  [BorelSpace X] [BorelSpace Y]
  (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

def separatedSum (f : C(X,ℝ)) (g : C(Y,ℝ)) : C(X×Y,ℝ) :=
  ⟨fun xy => f xy.1+g xy.2, (f.continuous.comp continuous_fst).add (g.continuous.comp continuous_snd)⟩

 theorem compact_continuous_integrable (f : C(X,ℝ)) : Integrable f μ :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.intro isCompact_univ (by simp))

 theorem separatedSum_integral_mono (f F : C(X,ℝ)) (g G : C(Y,ℝ))
    (h : separatedSum f g ≤ separatedSum F G) :
    (∫ x, f x ∂μ)+(∫ y, g y ∂ν) ≤ (∫ x, F x ∂μ)+(∫ y, G y ∂ν) := by
  have hy (x : X) : f x+(∫ y, g y ∂ν) ≤ F x+(∫ y, G y ∂ν) := by
    have hh := integral_mono ((integrable_const (f x)).add (compact_continuous_integrable ν g))
      ((integrable_const (F x)).add (compact_continuous_integrable ν G)) (fun y => h (x,y))
    simp only [Pi.add_apply] at hh
    simpa only [integral_add (integrable_const _) (compact_continuous_integrable ν _),
      integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using hh
  have hh := integral_mono ((compact_continuous_integrable μ f).add (integrable_const _))
    ((compact_continuous_integrable μ F).add (integrable_const _)) hy
  simp only [Pi.add_apply] at hh
  simpa only [integral_add (compact_continuous_integrable μ _) (integrable_const _),
    integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using hh

noncomputable def transportEnvelopeValues (h : C(X×Y,ℝ)) : Set ℝ :=
  {a | ∃ f : C(X,ℝ), ∃ g : C(Y,ℝ), h ≤ separatedSum f g ∧ a = (∫ x, f x ∂μ)+(∫ y, g y ∂ν)}

noncomputable def transportEnvelope (h : C(X×Y,ℝ)) : ℝ := sInf (transportEnvelopeValues μ ν h)

omit [BorelSpace X] [BorelSpace Y] [IsProbabilityMeasure ν] in
 theorem transportEnvelopeValues_nonempty (h : C(X×Y,ℝ)) :
    (transportEnvelopeValues μ ν h).Nonempty := by
  refine ⟨‖h‖, ContinuousMap.const X ‖h‖, 0, ?_, ?_⟩
  · intro xy
    change h xy ≤ ‖h‖+0
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, add_zero] using h.norm_coe_le_norm xy)
  · simp only [ContinuousMap.const_apply, ContinuousMap.zero_apply, integral_zero, add_zero,
      integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]

 theorem transportEnvelopeValues_bddBelow (h : C(X×Y,ℝ)) :
    BddBelow (transportEnvelopeValues μ ν h) := by
  refine ⟨-‖h‖, ?_⟩
  rintro a ⟨f,g,hfg,rfl⟩
  have hh : separatedSum (ContinuousMap.const X (-‖h‖)) 0 ≤ separatedSum f g := by
    intro xy
    change -‖h‖+0 ≤ f xy.1+g xy.2
    have hl : -‖h‖ ≤ h xy := (abs_le.mp (h.norm_coe_le_norm xy)).1
    simpa only [add_zero, separatedSum, ContinuousMap.coe_mk] using hl.trans (hfg xy)
  simpa only [ContinuousMap.const_apply, ContinuousMap.zero_apply, integral_zero, add_zero,
    integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using
      separatedSum_integral_mono μ ν (ContinuousMap.const X (-‖h‖)) f 0 g hh

 theorem transportEnvelope_le (h : C(X×Y,ℝ)) (f : C(X,ℝ)) (g : C(Y,ℝ))
    (hfg : h ≤ separatedSum f g) : transportEnvelope μ ν h ≤ (∫x, f x ∂μ)+(∫y, g y ∂ν) :=
  csInf_le (transportEnvelopeValues_bddBelow μ ν h) ⟨f,g,hfg,rfl⟩

 theorem transportEnvelope_separatedSum (f : C(X,ℝ)) (g : C(Y,ℝ)) :
    transportEnvelope μ ν (separatedSum f g) = (∫x, f x ∂μ)+(∫y, g y ∂ν) := by
  apply le_antisymm (transportEnvelope_le μ ν _ f g le_rfl)
  apply le_csInf (transportEnvelopeValues_nonempty μ ν _)
  rintro a ⟨F,G,hFG,rfl⟩
  exact separatedSum_integral_mono μ ν f F g G hFG

 theorem transportEnvelope_zero : transportEnvelope μ ν (0 : C(X×Y,ℝ)) = 0 := by
  have h : (0 : C(X×Y,ℝ)) = separatedSum (0:C(X,ℝ)) (0:C(Y,ℝ)) := by ext; simp [separatedSum]
  rw [h, transportEnvelope_separatedSum]
  simp only [ContinuousMap.zero_apply, integral_zero, add_zero]

 theorem transportEnvelope_add (h k : C(X×Y,ℝ)) :
    transportEnvelope μ ν (h+k) ≤ transportEnvelope μ ν h + transportEnvelope μ ν k := by
  have hh : transportEnvelope μ ν (h+k)-transportEnvelope μ ν k ≤ transportEnvelope μ ν h := by
    apply le_csInf (transportEnvelopeValues_nonempty μ ν h)
    rintro a ⟨f,g,hfg,rfl⟩
    have hk : transportEnvelope μ ν (h+k)-((∫x, f x ∂μ)+(∫y, g y ∂ν)) ≤ transportEnvelope μ ν k := by
      apply le_csInf (transportEnvelopeValues_nonempty μ ν k)
      rintro b ⟨F,G,hFG,rfl⟩
      have hu := transportEnvelope_le μ ν (h+k) (f+F) (g+G) (fun xy => by
        change h xy+k xy ≤ (f xy.1+F xy.1)+(g xy.2+G xy.2)
        have hh := add_le_add (hfg xy) (hFG xy)
        change h xy+k xy ≤ (f xy.1+g xy.2)+(F xy.1+G xy.2) at hh
        linarith)
      simp only [ContinuousMap.add_apply, integral_add (compact_continuous_integrable μ f)
        (compact_continuous_integrable μ F), integral_add (compact_continuous_integrable ν g)
        (compact_continuous_integrable ν G)] at hu
      linarith
    linarith
  linarith

 theorem transportEnvelope_smul_le {c : ℝ} (hc : 0 < c) (h : C(X×Y,ℝ)) :
    transportEnvelope μ ν (c • h) ≤ c*transportEnvelope μ ν h := by
  suffices hh : transportEnvelope μ ν (c • h)/c ≤ transportEnvelope μ ν h by
    simpa only [mul_comm] using (div_le_iff₀ hc).mp hh
  apply le_csInf (transportEnvelopeValues_nonempty μ ν h)
  rintro a ⟨f,g,hfg,rfl⟩
  apply (div_le_iff₀ hc).mpr
  have hu := transportEnvelope_le μ ν (c • h) (c • f) (c • g) (fun xy => by
    change c*h xy ≤ c*f xy.1+c*g xy.2
    have hh := mul_le_mul_of_nonneg_left (hfg xy) hc.le
    change c*h xy ≤ c*(f xy.1+g xy.2) at hh
    linarith)
  simp only [ContinuousMap.smul_apply, smul_eq_mul, integral_const_mul] at hu
  linarith

 theorem transportEnvelope_smul {c : ℝ} (hc : 0 < c) (h : C(X×Y,ℝ)) :
    transportEnvelope μ ν (c • h) = c*transportEnvelope μ ν h := by
  apply le_antisymm (transportEnvelope_smul_le μ ν hc h)
  have hh := transportEnvelope_smul_le μ ν (inv_pos.mpr hc) (c • h)
  rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at hh
  have hh' := mul_le_mul_of_nonneg_left hh hc.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] using hh'
end

 
section
open Set Filter MeasureTheory
open scoped NNReal Topology BoundedContinuousFunction
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace X] [CompactSpace Y]

omit [MetricSpace Y] [CompactSpace Y] in
 theorem compact_lipschitz_bounded_cmaps (K : ℝ≥0) (A : ℝ) :
    IsCompact {f : C(X,ℝ) | LipschitzWith K f ∧ ∀ x, |f x| ≤ A} := by
  let B : Set (X →ᵇ ℝ) := {f | LipschitzWith K f ∧ ∀ x, |f x| ≤ A}
  have hclosed : IsClosed B := by
    change IsClosed ({f : X →ᵇ ℝ | LipschitzWith K f} ∩ {f | ∀ x, |f x| ≤ A})
    apply IsClosed.inter
    · change IsClosed ((fun f : X →ᵇ ℝ => (f : X → ℝ)) ⁻¹'
        {f : X → ℝ | LipschitzWith K f})
      exact (isClosed_setOfPred_lipschitzWith (α := X) (β := ℝ) K).preimage
        BoundedContinuousFunction.continuous_coe
    · simp only [ofPred_forall]
      apply isClosed_iInter
      intro x
      exact isClosed_le (((continuous_apply x).comp BoundedContinuousFunction.continuous_coe).abs)
        continuous_const
  have hb : IsCompact B := by
    refine BoundedContinuousFunction.arzela_ascoli₂ (Icc (-A) A) isCompact_Icc B hclosed ?_ ?_
    · intro f x hf
      exact abs_le.mp (hf.2 x)
    · refine Metric.equicontinuous_of_continuity_modulus (fun t => (K:ℝ)*t) ?_ _ ?_
      · simpa using (tendsto_const_nhds.mul tendsto_id :
          Tendsto (fun t : ℝ => (K:ℝ)*t) (𝓝 0) (𝓝 ((K:ℝ)*0)))
      · intro x y f
        exact f.2.1.dist_le_mul x y
  exact (ContinuousMap.isometryEquivBoundedOfCompact X ℝ).toHomeomorph.isCompact_preimage.mpr hb

end

 
section
open Set Filter MeasureTheory
open scoped NNReal Topology
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace X] [CompactSpace Y]

 

 theorem compact_dual_pair_improvement [Nonempty Y] (h : C(X×Y,ℝ))
    {K : ℝ≥0} (hK : LipschitzWith K h) (p : X) (f : C(X,ℝ)) (g : C(Y,ℝ))
    (hfg : h ≤ separatedSum f g) :
    ∃ F : C(X,ℝ), ∃ G : C(Y,ℝ),
      LipschitzWith K F ∧ LipschitzWith K G ∧
      (∀ x, |F x| ≤ 2*‖h‖) ∧ (∀ y, |G y| ≤ 3*‖h‖) ∧
      h ≤ separatedSum F G ∧ separatedSum F G ≤ separatedSum f g := by
  let : Nonempty X := ⟨p⟩
  let c := compactCostTransform h g p
  let F : C(X,ℝ) := ⟨fun x => compactCostTransform h g x-c,
    (compactCostTransform_lipschitz h hK g).continuous.sub continuous_const⟩
  let hs : C(Y×X,ℝ) := ⟨fun yx => h (yx.2,yx.1), h.continuous.comp continuous_swap⟩
  have hsK : LipschitzWith K hs := by
    apply LipschitzWith.of_dist_le_mul
    intro yx wz
    have hh := hK.dist_le_mul (yx.2,yx.1) (wz.2,wz.1)
    simpa only [hs,ContinuousMap.coe_mk,Prod.dist_eq,max_comm] using hh
  let G : C(Y,ℝ) := ⟨compactCostTransform hs F, (compactCostTransform_lipschitz hs hsK F).continuous⟩
  have hF (x : X) : |F x| ≤ 2*‖h‖ := compactCostTransform_oscillation h g x p
  have hhn : ‖hs‖ ≤ ‖h‖ := (ContinuousMap.norm_le hs (norm_nonneg h)).mpr
    (fun yx => h.norm_coe_le_norm (yx.2,yx.1))
  refine ⟨F,G,?_,compactCostTransform_lipschitz hs hsK F,hF,?_,?_,?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x z
    have hh := (compactCostTransform_lipschitz h hK g).dist_le_mul x z
    simpa only [F,ContinuousMap.coe_mk,Real.dist_eq,sub_sub_sub_cancel_right] using hh
  · intro y
    have hh := compactCostTransform_bounded hs F hF y
    exact hh.trans (by linarith)
  · intro xy
    have hh := le_compactCostTransform hs F xy.2 xy.1
    change h xy-F xy.1 ≤ G xy.2 at hh
    change h xy ≤ F xy.1+G xy.2
    linarith
  · intro xy
    have h1 : F xy.1 ≤ f xy.1-c := by
      have hh : compactCostTransform h g xy.1 ≤ f xy.1 := by
        apply compactCostTransform_le
        intro y
        have ht := hfg (xy.1,y)
        change h (xy.1,y) ≤ f xy.1+g y at ht
        linarith
      change compactCostTransform h g xy.1-c ≤ f xy.1-c
      linarith
    have h2 : G xy.2 ≤ g xy.2+c := by
      apply compactCostTransform_le
      intro x
      have hh := le_compactCostTransform h g x xy.2
      change h (x,xy.2)-(compactCostTransform h g x-c) ≤ g xy.2+c
      linarith
    change F xy.1+G xy.2 ≤ f xy.1+g xy.2
    linarith

end

 
open Set Filter MeasureTheory
open scoped NNReal Topology
section Integral
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

 theorem compact_integral_lipschitz :
    LipschitzWith 1 (fun f : C(X,ℝ) => ∫ x, f x ∂μ) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  rw [Real.dist_eq, ←integral_sub (compact_continuous_integrable μ f)
    (compact_continuous_integrable μ g)]
  have hh := norm_integral_le_of_norm_le_const (μ := μ)
    (Filter.Eventually.of_forall (fun x => (f-g).norm_coe_le_norm x))
  simpa only [ContinuousMap.sub_apply,Real.norm_eq_abs,measureReal_def,measure_univ,
    ENNReal.toReal_one,mul_one,NNReal.coe_one,one_mul,dist_eq_norm] using hh
end Integral

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace X] [CompactSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

 

 theorem compact_transport_dual_attainment (h : C(X×Y,ℝ)) {K : ℝ≥0}
    (hK : LipschitzWith K h) :
    ∃ f : C(X,ℝ), ∃ g : C(Y,ℝ), LipschitzWith K f ∧ LipschitzWith K g ∧
      (∀ x, |f x| ≤ 2*‖h‖) ∧ (∀ y, |g y| ≤ 3*‖h‖) ∧
      h ≤ separatedSum f g ∧ transportEnvelope μ ν h = (∫x, f x ∂μ)+(∫y, g y ∂ν) := by
  let : Nonempty X := nonempty_of_isProbabilityMeasure μ
  let : Nonempty Y := nonempty_of_isProbabilityMeasure ν
  classical
  let p : X := Classical.choice ‹Nonempty X›
  let A : Set C(X,ℝ) := {f | LipschitzWith K f ∧ ∀ x, |f x| ≤ 2*‖h‖}
  let B : Set C(Y,ℝ) := {g | LipschitzWith K g ∧ ∀ y, |g y| ≤ 3*‖h‖}
  let S : Set (C(X,ℝ) × C(Y,ℝ)) := (A ×ˢ B) ∩ {fg | h ≤ separatedSum fg.1 fg.2}
  have hclosed : IsClosed {fg : C(X,ℝ) × C(Y,ℝ) | h ≤ separatedSum fg.1 fg.2} := by
    change IsClosed {fg : C(X,ℝ) × C(Y,ℝ) | ∀ xy, h xy ≤ fg.1 xy.1+fg.2 xy.2}
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro xy
    apply isClosed_le continuous_const
    exact ((continuous_eval_const xy.1).comp continuous_fst).add
      ((continuous_eval_const xy.2).comp continuous_snd)
  have hSc : IsCompact S := ((compact_lipschitz_bounded_cmaps K (2*‖h‖)).prod
    (compact_lipschitz_bounded_cmaps K (3*‖h‖))).inter_right hclosed
  have improve (f : C(X,ℝ)) (g : C(Y,ℝ)) (hfg : h ≤ separatedSum f g) :
      ∃ fg ∈ S, separatedSum fg.1 fg.2 ≤ separatedSum f g := by
    obtain ⟨F,G,hF,hG,hFb,hGb,had,himp⟩ := compact_dual_pair_improvement h hK p f g hfg
    exact ⟨(F,G),⟨⟨⟨hF,hFb⟩,⟨hG,hGb⟩⟩,had⟩,himp⟩
  have hSn : S.Nonempty := by
    obtain ⟨fg,hfg,_⟩ := improve (ContinuousMap.const X ‖h‖) 0 (fun xy => by
      change h xy ≤ ‖h‖+0
      simpa only [add_zero] using (le_abs_self _).trans (h.norm_coe_le_norm xy))
    exact ⟨fg,hfg⟩
  let J : C(X,ℝ) × C(Y,ℝ) → ℝ := fun fg => (∫x, fg.1 x ∂μ)+(∫y, fg.2 y ∂ν)
  have hJ : Continuous J := ((compact_integral_lipschitz μ).continuous.comp continuous_fst).add
    ((compact_integral_lipschitz ν).continuous.comp continuous_snd)
  obtain ⟨fg,hfg,hmin⟩ := hSc.exists_isMinOn hSn hJ.continuousOn
  refine ⟨fg.1,fg.2,hfg.1.1.1,hfg.1.2.1,hfg.1.1.2,hfg.1.2.2,hfg.2,?_⟩
  apply le_antisymm (transportEnvelope_le μ ν h fg.1 fg.2 hfg.2)
  apply le_csInf (transportEnvelopeValues_nonempty μ ν h)
  rintro a ⟨f,g,hf,rfl⟩
  obtain ⟨FG,hFG,himp⟩ := improve f g hf
  exact (hmin hFG).trans (separatedSum_integral_mono μ ν FG.1 f FG.2 g himp)

end RegularPointCoordinates

end OAI
