import Mathlib
import OAI.Probability.SLE.BrownianStrongMarkov

namespace OAI

/-! Stopped Measures for chordal SLE. -/

section
open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal

section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section

local instance sourceRealPathMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance sourceComplexPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance sourceRealPathBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance sourceComplexPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

def sourceDriverPath {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (ω : Ω) : C(ℝ≥0, ℝ) :=
  ⟨fun t => B t ω, hc ω⟩

def sourceTracePath {Ω : Type*} (γ : Ω → ℝ≥0 → ℂ)
    (hc : ∀ ω, Continuous (γ ω)) (ω : Ω) : C(ℝ≥0, ℂ) := ⟨γ ω, hc ω⟩

noncomputable def sourceRestartDriverPath {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (τ : Ω → ℝ≥0) (ω : Ω) : C(ℝ≥0, ℝ) :=
  ⟨fun t => brownianRestart B τ t ω,
    ((hc ω).comp (continuous_const.add continuous_id)).sub continuous_const⟩

universe u_source_stopped

 

def SourceStoppedTraceLawTarget : Prop :=
  ∀ {Ω : Type u_source_stopped} [_m : MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ), 0 < κ → κ < 8 →
  ∀ (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
  ∀ (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) (F ω)),
  ∃ Φ : C(ℝ≥0, ℝ) → C(ℝ≥0, ℂ), Measurable Φ ∧
    (∀ ω, Φ (sourceDriverPath B hc ω) = sourceTracePath γ (fun ω => (hw ω).1) ω) ∧
    ∀ (τ : Ω → ℝ≥0)
      (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
        (fun ω => (τ ω : WithTop ℝ≥0))),
      (∀ (A : Set Ω), MeasurableSet[hτ.measurableSpace] A →
        (P.restrict A).map (fun ω => Φ (sourceRestartDriverPath B hc τ ω)) =
          P A • P.map (sourceTracePath γ (fun ω => (hw ω).1))) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Φ (sourceRestartDriverPath B hc τ ω) t ∈ upperHalfPlane →
        γ ω (τ ω + t) = F ω (τ ω)
          (Φ (sourceRestartDriverPath B hc τ ω) t + (Real.sqrt κ * B (τ ω) ω : ℝ)))

end
end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section

lemma source_path_evaluation_embedding {E : Type*} [TopologicalSpace E]
    [PolishSpace E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace C(ℝ≥0, E)] [BorelSpace C(ℝ≥0, E)] [PolishSpace C(ℝ≥0, E)] :
    MeasurableEmbedding (fun f : C(ℝ≥0, E) => fun n => f (denseSeq ℝ≥0 n)) := by
  apply Continuous.measurableEmbedding
  · exact continuous_pi fun n => continuous_eval_const _
  · intro f g h
    apply DFunLike.coe_injective
    exact (denseRange_denseSeq ℝ≥0).equalizer f.continuous g.continuous h

lemma source_path_measurable {Ω E : Type*} [MeasurableSpace Ω]
    [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace C(ℝ≥0, E)] [BorelSpace C(ℝ≥0, E)] [PolishSpace C(ℝ≥0, E)]
    (f : Ω → C(ℝ≥0, E)) (hf : ∀ t, Measurable (fun ω => f ω t)) : Measurable f := by
  apply source_path_evaluation_embedding.measurable_comp_iff.mp
  exact Measurable.of_eval (fun _ => hf _)

local instance stoppedTraceFactorRealPathMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance stoppedTraceFactorComplexPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance stoppedTraceFactorRealPathBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance stoppedTraceFactorComplexPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

lemma source_trace_factor {Ω : Type*} [m : MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω))
    (γ : Ω → C(ℝ≥0, ℂ))
    (ha : Adapted (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun t ω => γ ω t)) :
    ∃ Φ : C(ℝ≥0, ℝ) → C(ℝ≥0, ℂ), Measurable Φ ∧
      γ = Φ ∘ (fun ω => (⟨fun t => B t ω, hc ω⟩ : C(ℝ≥0, ℝ))) := by
  let bp : Ω → C(ℝ≥0, ℝ) := fun ω => ⟨fun t => B t ω, hc ω⟩
  have hb (t : ℝ≥0) : @Measurable Ω ℝ (MeasurableSpace.comap bp (borel _)) (borel ℝ)
      (B t) := by
    exact (continuous_eval_const t).measurable.comp (Measurable.of_comap_le le_rfl)
  have hle (t : ℝ≥0) :
      (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) t ≤
        MeasurableSpace.comap bp (borel _) := by
    change (⨆ s ≤ t, MeasurableSpace.comap (B s) (borel ℝ)) ≤ _
    exact iSup_le fun s => iSup_le fun _ => measurable_iff_comap_le.mp (hb s)
  have hγ : @Measurable Ω C(ℝ≥0,ℂ)
      (MeasurableSpace.comap bp (borel _)) (borel _) γ := by
    let : MeasurableSpace Ω := MeasurableSpace.comap bp (borel _)
    exact source_path_measurable γ (fun t => (ha t).mono (hle t) le_rfl)
  exact hγ.exists_eq_measurable_comp
end
end SLEExactGauge

open Set Filter MeasureTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma source_reverseField_sub_real (a u v : ℝ) (z : ℂ) :
    reverseField a (u - v) (z - (v : ℂ)) = reverseField a u z := by
  unfold reverseField
  congr 2
  apply Complex.ext <;> simp [reverseCenter]

 

lemma IsCapacityTwoWitness.source_shifted_reverse_identifies
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T t : ℝ≥0) (w : ℂ) {a : ℝ}
    (ha : 0 < a) (haw : a ≤ w.im) (Q : ℝ → ℂ) (hQ0 : Q 0 = w)
    (hQd : ∀ s ∈ Icc 0 (t : ℝ), HasDerivWithinAt Q
      (reverseField a (U (T + ((t : ℝ) - s).toNNReal) - U T) (Q s))
        (Icc 0 (t : ℝ)) s) :
    F (T + t) (w + (U T : ℂ)) = F T (Q t + (U T : ℂ)) := by
  have hzH : w + (U T : ℂ) ∈ upperHalfPlane := by
    change 0 < (w + (U T : ℂ)).im
    simpa using ha.trans_le haw
  let z := F (T + t) (w + (U T : ℂ))
  have hz : z ∈ survivingDomain γ (T + t) := h.2.2.2.2.2.2.1 _ hzH
  have hzt : z ∈ survivingDomain γ T :=
    survivingDomain_antitone γ (le_add_of_nonneg_right (show 0 ≤ t from bot_le)) hz
  have ht (s : ℝ) (hs : s ∈ Icc 0 (t : ℝ)) :
      (((T + t : ℝ≥0) : ℝ) - s).toNNReal = T + ((t : ℝ) - s).toNNReal := by
    apply NNReal.coe_injective
    rw [Real.coe_toNNReal _ (by simp only [NNReal.coe_add]; linarith [T.coe_nonneg, hs.2])]
    simp only [NNReal.coe_add]
    rw [Real.coe_toNNReal _ (sub_nonneg.mpr hs.2)]
    ring
  let R (s : ℝ) := G (((T + t : ℝ≥0) : ℝ) - s).toNNReal z - (U T : ℂ)
  have hRd (s : ℝ) (hs : s ∈ Icc 0 (t : ℝ)) : HasDerivWithinAt R
      (reverseField a (U (T + ((t : ℝ) - s).toNNReal) - U T) (R s))
      (Icc 0 (t : ℝ)) s := by
    have hs' : s ∈ Icc 0 ((T + t : ℝ≥0) : ℝ) :=
      ⟨hs.1, by simp only [NNReal.coe_add]; linarith [T.coe_nonneg, hs.2]⟩
    have hd := ((h.reverse_path_derivative (T+t) (w + (U T : ℂ)) ha
      (by simpa using haw) s hs').sub_const (U T : ℂ)).mono
      (show Icc (0 : ℝ) t ⊆ Icc 0 ((T+t : ℝ≥0) : ℝ) from
        Icc_subset_Icc le_rfl (by simp only [NNReal.coe_add]; linarith [T.coe_nonneg]))
    change HasDerivWithinAt R _ _ _ at hd
    simpa only [R, ht s hs, source_reverseField_sub_real] using hd
  have he : EqOn Q R (Icc 0 (t : ℝ)) := by
    apply ODE_solution_unique
      (fun s => reverseField_lipschitz ha (U (T + ((t : ℝ) - s).toNNReal) - U T))
      (fun s hs => (hQd s hs).continuousWithinAt)
      (fun s hs => hasDerivWithinAt_Ici_of_Icc hs (hQd s ⟨hs.1, hs.2.le⟩))
      (fun s hs => (hRd s hs).continuousWithinAt)
      (fun s hs => hasDerivWithinAt_Ici_of_Icc hs (hRd s ⟨hs.1, hs.2.le⟩))
    simpa only [R, sub_zero, Real.toNNReal_coe, z,
      h.2.2.2.2.2.2.2.2.1 (T+t) _ hzH, add_sub_cancel_right] using hQ0
  have heT := he ⟨t.coe_nonneg, le_rfl⟩
  have htime : (((T + t : ℝ≥0) : ℝ) - (t : ℝ)).toNNReal = T := by
    simp only [NNReal.coe_add, add_sub_cancel_right, Real.toNNReal_coe]
  have hQ : Q t + (U T : ℂ) = G T z := by
    simpa only [R, htime, sub_add_cancel] using congrArg (fun v : ℂ => v + (U T : ℂ)) heT
  rw [hQ, h.2.2.2.2.2.2.2.1 T z hzt]

end SLEExactGauge

open Set Filter MeasureTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance stoppedReverseFlowRealPathMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance stoppedReverseFlowRealPathBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩

lemma source_canonical_reverse_flow (κ : ℝ) (T : ℝ≥0) {a : ℝ} (ha : 0 < a) :
    ∃ Q : ℝ → C(ℝ≥0, ℝ) → ℂ,
      (∀ s, Measurable (Q s)) ∧
      (∀ p, Q 0 p = (Real.sqrt κ * p T : ℝ) + (a : ℂ) * I) ∧
      ∀ p s, 0 ≤ s → HasDerivWithinAt (fun r => Q r p)
        (reverseField a (Real.sqrt κ * p ((T : ℝ) - s).toNNReal) (Q s p)) (Ici 0) s := by
  let V (s : ℝ) (p : C(ℝ≥0, ℝ)) := Real.sqrt κ * p ((T : ℝ) - s).toNNReal
  have hV : Continuous (fun q : ℝ × C(ℝ≥0, ℝ) => V q.1 q.2) := by
    apply continuous_const.mul
    exact continuous_eval.comp (continuous_snd.prodMk
      (continuous_real_toNNReal.comp (continuous_const.sub continuous_fst)))
  have hw : Measurable (fun p : C(ℝ≥0, ℝ) =>
      (Real.sqrt κ * p T : ℝ) + (a : ℂ) * I) :=
    (Complex.continuous_ofReal.comp (continuous_const.mul (continuous_eval_const T))).measurable.add_const _
  obtain ⟨Q, hQm, hQ0, hQd⟩ := exists_measurable_reverse_flow V hV.measurable
    (fun p => hV.comp (continuous_id.prodMk continuous_const)) _ hw ha
  exact ⟨Q, fun s => hQm.comp (measurable_prodMk_left (x := s)), hQ0, hQd⟩

end
end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance stoppedRestartLawRealPathMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance stoppedRestartLawComplexPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance stoppedRestartLawRealPathBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance stoppedRestartLawComplexPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

lemma source_restart_continuous_driver_law
    {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) :
    (P.restrict A).map (sourceRestartDriverPath B hc τ) =
      P A • P.map (sourceDriverPath B hc) := by
  have hbm : Measurable (sourceDriverPath B hc) := source_path_measurable _ hm
  have hrm : Measurable (sourceRestartDriverPath B hc τ) :=
    source_path_measurable _ (fun t => (measurable_pi_apply t).comp
      (brownianRestart_measurable hm hc (stopping_time_measurable_nnreal hτ)))
  apply source_path_evaluation_embedding.map_injective
  have he := congrArg (Measure.map (fun p : ℝ≥0 → ℝ => fun n => p (denseSeq ℝ≥0 n)))
    (brownian_restart_path_law hB hm hc hτ hA)
  have hem : Measurable (fun p : ℝ≥0 → ℝ => fun n => p (denseSeq ℝ≥0 n)) :=
    Measurable.of_eval (fun _ => measurable_pi_apply _)
  rw [Measure.map_map source_path_evaluation_embedding.measurable hrm,
    Measure.map_smul _ source_path_evaluation_embedding.measurable.aemeasurable,
    Measure.map_map source_path_evaluation_embedding.measurable hbm]
  rw [Measure.map_map hem (brownianRestart_measurable hm hc
    (stopping_time_measurable_nnreal hτ)), Measure.map_smul _ hem.aemeasurable,
    Measure.map_map hem (Measurable.of_eval hm)] at he
  exact he

end
end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance stoppedTraceLawRealPathMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance stoppedTraceLawComplexPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance stoppedTraceLawRealPathBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance stoppedTraceLawComplexPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

theorem sourceStoppedTraceLaw : SourceStoppedTraceLawTarget := by
  intro Ω m P κ hκ hκ8 B hB hm hc γ G F hw
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let bp := sourceDriverPath B hc
  let gp := sourceTracePath γ (fun ω => (hw ω).1)
  have hbm : Measurable bp := source_path_measurable bp hm
  have hγa : Adapted (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun t ω => gp ω t) := by
    apply capacity_trace_adapted _ (fun t ω => Real.sqrt κ * B t ω)
      ?_ (fun ω => continuous_const.mul (hc ω)) γ G F hw
    intro t
    exact measurable_const.mul
      ((Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable)) t).measurable
  obtain ⟨Φ, hΦm, hΦ⟩ := source_trace_factor B hm hc gp hγa
  have hΦe (ω : Ω) : Φ (bp ω) = gp ω := (congrFun hΦ ω).symm
  have hgm : Measurable gp := hΦ ▸ hΦm.comp hbm
  refine ⟨Φ, hΦm, hΦe, ?_⟩
  intro τ hτ
  let rp := sourceRestartDriverPath B hc τ
  have hrm : Measurable rp := source_path_measurable rp (fun t =>
    (measurable_pi_apply t).comp (brownianRestart_measurable hm hc
      (stopping_time_measurable_nnreal hτ)))
  have hlaw (A : Set Ω) (hA : MeasurableSet[hτ.measurableSpace] A) :
      (P.restrict A).map rp = P A • P.map bp :=
    source_restart_continuous_driver_law hB hm hc τ hτ hA
  have hlaw0 : P.map rp = P.map bp := by
    simpa only [Measure.restrict_univ, measure_univ, one_smul] using hlaw univ MeasurableSet.univ
  constructor
  · intro A hA
    have he := congrArg (Measure.map Φ) (hlaw A hA)
    rw [Measure.map_map hΦm hrm, Measure.map_smul _ hΦm.aemeasurable,
      Measure.map_map hΦm hbm] at he
    have hcomp : Φ ∘ bp = gp := hΦ.symm
    simpa only [hcomp, rp, gp, Function.comp_def] using he
  · choose Q hQm hQ0 hQd using fun (t : ℝ≥0) (n : ℕ) =>
      source_canonical_reverse_flow κ t (a := 1 / ((n : ℝ) + 1)) (by positivity)
    let a (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
    have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
    have hy : Tendsto a atTop (𝓝[>] (0 : ℝ)) :=
      tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall ha⟩
    have hQorig (ω : Ω) (t : ℝ≥0) (n : ℕ) :
        Q t n t (bp ω) = F ω t ((Real.sqrt κ * B t ω : ℝ) + (a n : ℂ) * I) := by
      apply (hw ω).reverse_flow_identifies t
        ((Real.sqrt κ * B t ω : ℝ) + (a n : ℂ) * I) (ha n) (by simp)
        (fun s => Q t n s (bp ω)) (hQ0 t n (bp ω))
      intro s hs
      exact (hQd t n (bp ω) s hs.1).mono Icc_subset_Ici_self
    have hQlimit (ω : Ω) (t : ℝ≥0) :
        Tendsto (fun n => Q t n t (bp ω)) atTop (𝓝 (Φ (bp ω) t)) := by
      have ht := ((hw ω).2.2.2.2.2.2.2.2.2.2.2.2 t).comp hy
      simpa only [hQorig, hΦe, gp, sourceTracePath, ContinuousMap.coe_mk, Function.comp_def] using ht
    have hset (t : ℝ≥0) : MeasurableSet
        {p : C(ℝ≥0,ℝ) | Tendsto (fun n => Q t n t p - Φ p t) atTop (𝓝 0)} :=
      measurableSet_tendsto (𝓝 (0 : ℂ)) (fun n => (hQm t n t).sub
        ((continuous_eval_const t).measurable.comp hΦm))
    have hQR (t : ℝ≥0) : ∀ᵐ ω ∂P,
        Tendsto (fun n => Q t n t (rp ω)) atTop (𝓝 (Φ (rp ω) t)) := by
      have ho : ∀ᵐ p ∂P.map bp,
          Tendsto (fun n => Q t n t p - Φ p t) atTop (𝓝 0) := by
        apply (ae_map_iff hbm.aemeasurable (hset t)).2
        exact Eventually.of_forall (fun ω => tendsto_sub_nhds_zero_iff.mpr (hQlimit ω t))
      rw [← hlaw0] at ho
      filter_upwards [(ae_map_iff hrm.aemeasurable (hset t)).1 ho] with ω hω
      exact tendsto_sub_nhds_zero_iff.mp hω
    have hQRall : ∀ᵐ ω ∂P, ∀ j : ℕ,
        Tendsto (fun n => Q (denseSeq ℝ≥0 j) n (denseSeq ℝ≥0 j) (rp ω)) atTop
          (𝓝 (Φ (rp ω) (denseSeq ℝ≥0 j))) := ae_all_iff.mpr (fun j => hQR _)
    filter_upwards [hQRall] with ω hω
    have hcoc (t : ℝ≥0) (n : ℕ) :
        F ω (τ ω + t) ((Real.sqrt κ * B (τ ω + t) ω : ℝ) + (a n : ℂ) * I) =
        F ω (τ ω) (Q t n t (rp ω) + (Real.sqrt κ * B (τ ω) ω : ℝ)) := by
      have he := (hw ω).source_shifted_reverse_identifies (τ ω) t
        ((Real.sqrt κ * (rp ω) t : ℝ) + (a n : ℂ) * I) (ha n) (by simp)
        (fun s => Q t n s (rp ω)) (hQ0 t n (rp ω))
        (fun s hs => by
          have hh := (hQd t n (rp ω) s hs.1).mono
            (show Icc (0 : ℝ) t ⊆ Ici 0 from Icc_subset_Ici_self)
          simpa only [rp, sourceRestartDriverPath, brownianRestart, ContinuousMap.coe_mk,
            mul_sub] using hh)
      convert he using 2
      simp only [rp, sourceRestartDriverPath, brownianRestart, ContinuousMap.coe_mk]
      push_cast
      ring
    have hdense (j : ℕ) (hj : Φ (rp ω) (denseSeq ℝ≥0 j) ∈ upperHalfPlane) :
        γ ω (τ ω + denseSeq ℝ≥0 j) = F ω (τ ω)
          (Φ (rp ω) (denseSeq ℝ≥0 j) + (Real.sqrt κ * B (τ ω) ω : ℝ)) := by
      let t := denseSeq ℝ≥0 j
      have hz : Φ (rp ω) t + (Real.sqrt κ * B (τ ω) ω : ℝ) ∈ upperHalfPlane := by
        simpa only [upperHalfPlane, mem_ofPred_eq, add_im, ofReal_im, add_zero] using hj
      have hFt : ContinuousAt (F ω (τ ω))
          (Φ (rp ω) t + (Real.sqrt κ * B (τ ω) ω : ℝ)) :=
        ((hw ω).2.2.2.2.1 (τ ω)).continuousOn.continuousAt
          (isOpen_upperHalfPlane.mem_nhds hz)
      have hlimF := hFt.tendsto.comp ((hω j).add_const ((Real.sqrt κ * B (τ ω) ω : ℝ) : ℂ))
      have hlimγ := ((hw ω).2.2.2.2.2.2.2.2.2.2.2.2 (τ ω + t)).comp hy
      simp only [Function.comp_def, hcoc] at hlimγ
      exact tendsto_nhds_unique hlimγ hlimF
    let S : Set ℝ≥0 := {t | Φ (rp ω) t ∈ upperHalfPlane}
    have hSo : IsOpen S := isOpen_upperHalfPlane.preimage (Φ (rp ω)).continuous
    have hleft : ContinuousOn (fun t => γ ω (τ ω + t)) S :=
      ((hw ω).1.comp (continuous_const.add continuous_id)).continuousOn
    have hright : ContinuousOn (fun t => F ω (τ ω)
        (Φ (rp ω) t + (Real.sqrt κ * B (τ ω) ω : ℝ))) S := by
      apply ((hw ω).2.2.2.2.1 (τ ω)).continuousOn.comp
        ((Φ (rp ω)).continuous.add_const _).continuousOn
      intro t ht
      simpa only [S, upperHalfPlane, mem_ofPred_eq, add_im, ofReal_im, add_zero] using ht
    have hEq : EqOn (fun t => γ ω (τ ω + t))
        (fun t => F ω (τ ω) (Φ (rp ω) t + (Real.sqrt κ * B (τ ω) ω : ℝ)))
        (S ∩ range (denseSeq ℝ≥0)) := by
      rintro t ⟨ht, j, rfl⟩
      exact hdense j ht
    exact hEq.of_subset_closure hleft hright inter_subset_left
      ((denseRange_denseSeq ℝ≥0).open_subset_closure_inter hSo)
end
end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance stoppedForwardLawRealPathMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance stoppedForwardLawComplexPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance stoppedForwardLawRealPathBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance stoppedForwardLawComplexPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩
lemma IsCapacityTwoWitness.source_shifted_forward_approximation
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T t : ℝ≥0) (w : ℂ) {a : ℝ}
    (ha : 0 < a) (haw : a ≤ w.im) (Q : ℝ → ℂ) (hQ0 : Q 0 = w)
    (hQd : ∀ s ∈ Icc 0 (t : ℝ), HasDerivWithinAt Q
      (reverseField a (U (T + ((t : ℝ) - s).toNNReal) - U T) (Q s))
        (Icc 0 (t : ℝ)) s) :
    Q t = G T (F (T + t) (w + (U T : ℂ))) - (U T : ℂ) := by
  have hzH : w + (U T : ℂ) ∈ upperHalfPlane := by
    change 0 < (w + (U T : ℂ)).im
    simpa using ha.trans_le haw
  let z := F (T + t) (w + (U T : ℂ))
  have hz : z ∈ survivingDomain γ (T + t) := h.2.2.2.2.2.2.1 _ hzH
  have hzt : z ∈ survivingDomain γ T :=
    survivingDomain_antitone γ (le_add_of_nonneg_right (show 0 ≤ t from bot_le)) hz
  have ht (s : ℝ) (hs : s ∈ Icc 0 (t : ℝ)) :
      (((T + t : ℝ≥0) : ℝ) - s).toNNReal = T + ((t : ℝ) - s).toNNReal := by
    apply NNReal.coe_injective
    rw [Real.coe_toNNReal _ (by simp only [NNReal.coe_add]; linarith [T.coe_nonneg, hs.2])]
    simp only [NNReal.coe_add]
    rw [Real.coe_toNNReal _ (sub_nonneg.mpr hs.2)]
    ring
  let R (s : ℝ) := G (((T + t : ℝ≥0) : ℝ) - s).toNNReal z - (U T : ℂ)
  have hRd (s : ℝ) (hs : s ∈ Icc 0 (t : ℝ)) : HasDerivWithinAt R
      (reverseField a (U (T + ((t : ℝ) - s).toNNReal) - U T) (R s))
      (Icc 0 (t : ℝ)) s := by
    have hs' : s ∈ Icc 0 ((T + t : ℝ≥0) : ℝ) :=
      ⟨hs.1, by simp only [NNReal.coe_add]; linarith [T.coe_nonneg, hs.2]⟩
    have hd := ((h.reverse_path_derivative (T+t) (w + (U T : ℂ)) ha
      (by simpa using haw) s hs').sub_const (U T : ℂ)).mono
      (show Icc (0 : ℝ) t ⊆ Icc 0 ((T+t : ℝ≥0) : ℝ) from
        Icc_subset_Icc le_rfl (by simp only [NNReal.coe_add]; linarith [T.coe_nonneg]))
    change HasDerivWithinAt R _ _ _ at hd
    simpa only [R, ht s hs, source_reverseField_sub_real] using hd
  have he : EqOn Q R (Icc 0 (t : ℝ)) := by
    apply ODE_solution_unique
      (fun s => reverseField_lipschitz ha (U (T + ((t : ℝ) - s).toNNReal) - U T))
      (fun s hs => (hQd s hs).continuousWithinAt)
      (fun s hs => hasDerivWithinAt_Ici_of_Icc hs (hQd s ⟨hs.1, hs.2.le⟩))
      (fun s hs => (hRd s hs).continuousWithinAt)
      (fun s hs => hasDerivWithinAt_Ici_of_Icc hs (hRd s ⟨hs.1, hs.2.le⟩))
    simpa only [R, sub_zero, Real.toNNReal_coe, z,
      h.2.2.2.2.2.2.2.2.1 (T+t) _ hzH, add_sub_cancel_right] using hQ0
  have heT := he ⟨t.coe_nonneg, le_rfl⟩
  have htime : (((T + t : ℝ≥0) : ℝ) - (t : ℝ)).toNNReal = T := by
    simp only [NNReal.coe_add, add_sub_cancel_right, Real.toNNReal_coe]
  have hQ : Q t + (U T : ℂ) = G T z := by
    simpa only [R, htime, sub_add_cancel] using congrArg (fun v : ℂ => v + (U T : ℂ)) heT
  exact eq_sub_iff_add_eq.mpr hQ

universe u_source_stopped

theorem sourceStoppedTraceLaw_forward :
  ∀ {Ω : Type u_source_stopped} [_m : MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ), 0 < κ → κ < 8 →
  ∀ (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
  ∀ (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) (F ω)),
  ∃ Φ : C(ℝ≥0, ℝ) → C(ℝ≥0, ℂ), Measurable Φ ∧
    (∀ ω, Φ (sourceDriverPath B hc ω) = sourceTracePath γ (fun ω => (hw ω).1) ω) ∧
    ∀ (τ : Ω → ℝ≥0)
      (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
        (fun ω => (τ ω : WithTop ℝ≥0))),
      (∀ (A : Set Ω), MeasurableSet[hτ.measurableSpace] A →
        (P.restrict A).map (fun ω => Φ (sourceRestartDriverPath B hc τ ω)) =
          P A • P.map (sourceTracePath γ (fun ω => (hw ω).1))) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        γ ω (τ ω + t) ∈ survivingDomain (γ ω) (τ ω) →
        Φ (sourceRestartDriverPath B hc τ ω) t =
          G ω (τ ω) (γ ω (τ ω + t)) - (Real.sqrt κ * B (τ ω) ω : ℝ)) := by
  intro Ω m P κ hκ hκ8 B hB hm hc γ G F hw
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let bp := sourceDriverPath B hc
  let gp := sourceTracePath γ (fun ω => (hw ω).1)
  have hbm : Measurable bp := source_path_measurable bp hm
  have hγa : Adapted (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun t ω => gp ω t) := by
    apply capacity_trace_adapted _ (fun t ω => Real.sqrt κ * B t ω)
      ?_ (fun ω => continuous_const.mul (hc ω)) γ G F hw
    intro t
    exact measurable_const.mul
      ((Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable)) t).measurable
  obtain ⟨Φ, hΦm, hΦ⟩ := source_trace_factor B hm hc gp hγa
  have hΦe (ω : Ω) : Φ (bp ω) = gp ω := (congrFun hΦ ω).symm
  have hgm : Measurable gp := hΦ ▸ hΦm.comp hbm
  refine ⟨Φ, hΦm, hΦe, ?_⟩
  intro τ hτ
  let rp := sourceRestartDriverPath B hc τ
  have hrm : Measurable rp := source_path_measurable rp (fun t =>
    (measurable_pi_apply t).comp (brownianRestart_measurable hm hc
      (stopping_time_measurable_nnreal hτ)))
  have hlaw (A : Set Ω) (hA : MeasurableSet[hτ.measurableSpace] A) :
      (P.restrict A).map rp = P A • P.map bp :=
    source_restart_continuous_driver_law hB hm hc τ hτ hA
  have hlaw0 : P.map rp = P.map bp := by
    simpa only [Measure.restrict_univ, measure_univ, one_smul] using hlaw univ MeasurableSet.univ
  constructor
  · intro A hA
    have he := congrArg (Measure.map Φ) (hlaw A hA)
    rw [Measure.map_map hΦm hrm, Measure.map_smul _ hΦm.aemeasurable,
      Measure.map_map hΦm hbm] at he
    have hcomp : Φ ∘ bp = gp := hΦ.symm
    simpa only [hcomp, rp, gp, Function.comp_def] using he
  · choose Q hQm hQ0 hQd using fun (t : ℝ≥0) (n : ℕ) =>
      source_canonical_reverse_flow κ t (a := 1 / ((n : ℝ) + 1)) (by positivity)
    let a (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
    have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
    have hy : Tendsto a atTop (𝓝[>] (0 : ℝ)) :=
      tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall ha⟩
    have hQorig (ω : Ω) (t : ℝ≥0) (n : ℕ) :
        Q t n t (bp ω) = F ω t ((Real.sqrt κ * B t ω : ℝ) + (a n : ℂ) * I) := by
      apply (hw ω).reverse_flow_identifies t
        ((Real.sqrt κ * B t ω : ℝ) + (a n : ℂ) * I) (ha n) (by simp)
        (fun s => Q t n s (bp ω)) (hQ0 t n (bp ω))
      intro s hs
      exact (hQd t n (bp ω) s hs.1).mono Icc_subset_Ici_self
    have hQlimit (ω : Ω) (t : ℝ≥0) :
        Tendsto (fun n => Q t n t (bp ω)) atTop (𝓝 (Φ (bp ω) t)) := by
      have ht := ((hw ω).2.2.2.2.2.2.2.2.2.2.2.2 t).comp hy
      simpa only [hQorig, hΦe, gp, sourceTracePath, ContinuousMap.coe_mk, Function.comp_def] using ht
    have hset (t : ℝ≥0) : MeasurableSet
        {p : C(ℝ≥0,ℝ) | Tendsto (fun n => Q t n t p - Φ p t) atTop (𝓝 0)} :=
      measurableSet_tendsto (𝓝 (0 : ℂ)) (fun n => (hQm t n t).sub
        ((continuous_eval_const t).measurable.comp hΦm))
    have hQR (t : ℝ≥0) : ∀ᵐ ω ∂P,
        Tendsto (fun n => Q t n t (rp ω)) atTop (𝓝 (Φ (rp ω) t)) := by
      have ho : ∀ᵐ p ∂P.map bp,
          Tendsto (fun n => Q t n t p - Φ p t) atTop (𝓝 0) := by
        apply (ae_map_iff hbm.aemeasurable (hset t)).2
        exact Eventually.of_forall (fun ω => tendsto_sub_nhds_zero_iff.mpr (hQlimit ω t))
      rw [← hlaw0] at ho
      filter_upwards [(ae_map_iff hrm.aemeasurable (hset t)).1 ho] with ω hω
      exact tendsto_sub_nhds_zero_iff.mp hω
    have hQRall : ∀ᵐ ω ∂P, ∀ j : ℕ,
        Tendsto (fun n => Q (denseSeq ℝ≥0 j) n (denseSeq ℝ≥0 j) (rp ω)) atTop
          (𝓝 (Φ (rp ω) (denseSeq ℝ≥0 j))) := ae_all_iff.mpr (fun j => hQR _)
    filter_upwards [hQRall] with ω hω
    have hcoc (t : ℝ≥0) (n : ℕ) :
        Q t n t (rp ω) = G ω (τ ω)
          (F ω (τ ω + t) ((Real.sqrt κ * B (τ ω + t) ω : ℝ) + (a n : ℂ) * I)) -
            (Real.sqrt κ * B (τ ω) ω : ℝ) := by
      have he := (hw ω).source_shifted_forward_approximation (τ ω) t
        ((Real.sqrt κ * (rp ω) t : ℝ) + (a n : ℂ) * I) (ha n) (by simp)
        (fun s => Q t n s (rp ω)) (hQ0 t n (rp ω))
        (fun s hs => by
          have hh := (hQd t n (rp ω) s hs.1).mono
            (show Icc (0 : ℝ) t ⊆ Ici 0 from Icc_subset_Ici_self)
          simpa only [rp, sourceRestartDriverPath, brownianRestart, ContinuousMap.coe_mk,
            mul_sub] using hh)
      convert he using 2
      simp only [rp, sourceRestartDriverPath, brownianRestart, ContinuousMap.coe_mk]
      push_cast
      ring_nf
    have hdense (j : ℕ)
        (hj : γ ω (τ ω + denseSeq ℝ≥0 j) ∈ survivingDomain (γ ω) (τ ω)) :
        Φ (rp ω) (denseSeq ℝ≥0 j) =
          G ω (τ ω) (γ ω (τ ω + denseSeq ℝ≥0 j)) - (Real.sqrt κ * B (τ ω) ω : ℝ) := by
      let t := denseSeq ℝ≥0 j
      have hGc : ContinuousAt (G ω (τ ω)) (γ ω (τ ω + t)) :=
        ((hw ω).2.2.2.1 (τ ω)).continuousOn.continuousAt
          ((isOpen_survivingDomain (hw ω).1 (τ ω)).mem_nhds hj)
      have hlimγ := ((hw ω).2.2.2.2.2.2.2.2.2.2.2.2 (τ ω + t)).comp hy
      have hlimG := (hGc.tendsto.comp hlimγ).sub_const ((Real.sqrt κ * B (τ ω) ω : ℝ) : ℂ)
      apply tendsto_nhds_unique (hω j)
      simpa only [hcoc, Function.comp_def] using hlimG
    let S : Set ℝ≥0 := {t | γ ω (τ ω + t) ∈ survivingDomain (γ ω) (τ ω)}
    have hγc : Continuous (fun t : ℝ≥0 => γ ω (τ ω + t)) :=
      (hw ω).1.comp (continuous_const.add continuous_id)
    have hSo : IsOpen S := (isOpen_survivingDomain (hw ω).1 (τ ω)).preimage hγc
    have hleft : ContinuousOn (fun t : ℝ≥0 => Φ (rp ω) t) S :=
      (Φ (rp ω)).continuous.continuousOn
    have hright : ContinuousOn (fun t : ℝ≥0 =>
        G ω (τ ω) (γ ω (τ ω + t)) - (Real.sqrt κ * B (τ ω) ω : ℝ)) S :=
      (((hw ω).2.2.2.1 (τ ω)).continuousOn.comp hγc.continuousOn
        (fun _ ht => ht)).sub continuousOn_const
    have hEq : EqOn (fun t : ℝ≥0 => Φ (rp ω) t)
        (fun t : ℝ≥0 => G ω (τ ω) (γ ω (τ ω + t)) - (Real.sqrt κ * B (τ ω) ω : ℝ))
        (S ∩ range (denseSeq ℝ≥0)) := by
      rintro t ⟨ht, j, rfl⟩
      exact hdense j ht
    exact hEq.of_subset_closure hleft hright inter_subset_left
      ((denseRange_denseSeq ℝ≥0).open_subset_closure_inter hSo)

end
end SLEExactGauge

end

section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped ENNReal
namespace SLEExactGauge

 

lemma source_parameter_joint_law
    {Ω Z E : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [MeasurableSpace Z] [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [IsProbabilityMeasure ν]
    (hm : m ≤ mΩ)
    {X : Ω → E} (hX : Measurable X) {Y : Ω → Z} (hY : Measurable[m] Y)
    (hlaw : ∀ A : Set Ω, MeasurableSet[m] A → (P.restrict A).map X = P A • ν)
    (A : Set Ω) (hA : MeasurableSet[m] A) :
    (P.restrict A).map (fun ω => (Y ω, X ω)) = ((P.restrict A).map Y).prod ν := by
  have hYa : Measurable Y := hY.mono hm le_rfl
  apply Measure.ext_prod
  intro S T hS hT
  have he := congrArg (fun μ : Measure E => μ T)
    (hlaw (A ∩ Y ⁻¹' S) (hA.inter (hY hS)))
  rw [Measure.map_apply hX hT, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply (hX hT)] at he
  rw [Measure.map_apply (hYa.prodMk hX) (hS.prod hT),
    Measure.restrict_apply ((hYa.prodMk hX) (hS.prod hT)),
    Measure.prod_prod, Measure.map_apply hYa hS, Measure.restrict_apply (hYa hS)]
  change P ((Y ⁻¹' S ∩ X ⁻¹' T) ∩ A) = P (Y ⁻¹' S ∩ A) * ν T
  simpa only [inter_assoc, inter_left_comm, inter_comm] using he

lemma source_parameter_condExp
    {Ω Z E : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [MeasurableSpace Z] [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [IsProbabilityMeasure ν]
    (hm : m ≤ mΩ)
    {X : Ω → E} (hX : Measurable X) {Y : Ω → Z} (hY : Measurable[m] Y)
    (hlaw : ∀ A : Set Ω, MeasurableSet[m] A → (P.restrict A).map X = P A • ν)
    (H : Z × E → ℝ) (hH : Measurable H) (hb : ∀ p, ‖H p‖ ≤ 1) :
    P[(fun ω => H (Y ω, X ω)) | m] =ᵐ[P] (fun ω => ∫ e, H (Y ω, e) ∂ν) := by
  have hYa : Measurable Y := hY.mono hm le_rfl
  have hK : StronglyMeasurable (fun y => ∫ e, H (y, e) ∂ν) :=
    hH.stronglyMeasurable.integral_prod_right'
  have hKb (y : Z) : ‖∫ e, H (y, e) ∂ν‖ ≤ 1 := by
    simpa using norm_integral_le_of_norm_le_const (μ := ν) (Eventually.of_forall (fun e => hb (y,e)))
  have hint : Integrable (fun ω => H (Y ω, X ω)) P :=
    (integrable_const (1 : ℝ)).mono' (hH.comp (hYa.prodMk hX)).aestronglyMeasurable
      (Eventually.of_forall (fun ω => hb (Y ω, X ω)))
  have hKint : Integrable (fun ω => ∫ e, H (Y ω, e) ∂ν) P :=
    (integrable_const (1 : ℝ)).mono' (hK.comp_measurable hYa).aestronglyMeasurable
      (Eventually.of_forall (fun ω => hKb (Y ω)))
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm hint
    (fun _ _ _ => hKint.integrableOn) _ (hK.comp_measurable hY).aestronglyMeasurable
  intro A hA _
  have hprodint : Integrable H (((P.restrict A).map Y).prod ν) :=
    (integrable_const (1 : ℝ)).mono' hH.aestronglyMeasurable (Eventually.of_forall hb)
  calc
    (∫ ω in A, ∫ e, H (Y ω, e) ∂ν ∂P) =
        ∫ y, ∫ e, H (y, e) ∂ν ∂(P.restrict A).map Y :=
      (integral_map hYa.aemeasurable hK.aestronglyMeasurable).symm
    _ = ∫ p, H p ∂(((P.restrict A).map Y).prod ν) := (integral_prod H hprodint).symm
    _ = ∫ p, H p ∂(P.restrict A).map (fun ω => (Y ω, X ω)) := by
      rw [source_parameter_joint_law hm hX hY hlaw A hA]
    _ = ∫ ω in A, H (Y ω, X ω) ∂P :=
      integral_map (hYa.prodMk hX).aemeasurable hH.aestronglyMeasurable

end SLEExactGauge

end

section
open Set Filter MeasureTheory ProbabilityTheory Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section

 

theorem source_killedChart_progressive
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) (F ω)) (z : ℂ) :
    IsStronglyProgressive (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun t ω => if z ∈ survivingDomain (γ ω) t then G ω t z else 0) := by
  classical
  let f := Filtration.natural B (fun t => (hm t).stronglyMeasurable)
  have hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2) :=
    measurable_uncurry_of_continuous_of_measurable hc hm
  have hnn (n : ℕ) : -(n : ℝ) ≤ n := by linarith [Nat.cast_nonneg (α := ℝ) n]
  let c (n : ℕ) := (exists_clippedLogSolution B hm hBm hc κ (-(n : ℝ)) n (hnn n)
    (initialLogCoordinates z)).some
  let v (n : ℕ) (t : ℝ≥0) (ω : Ω) : Prop :=
    0 < z.im ∧ Real.log z.im ≤ (n : ℝ) ∧ -(n : ℝ) ≤ ((c n).Q t ω).1.im
  let A (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℂ :=
    if v n t ω then
      (((c n).Q t ω).1.re : ℂ) + (Real.exp ((c n).Q t ω).1.im : ℂ) * I
    else 0
  have hQp (n : ℕ) : IsStronglyProgressive f (fun t : ℝ≥0 => (c n).Q t) :=
    (show StronglyAdapted f (fun t : ℝ≥0 => (c n).Q t) from
      fun t => ((c n).adapted t).stronglyMeasurable).isStronglyProgressive_of_continuous
      (fun ω => ((c n).lipschitz ω).continuous.comp NNReal.continuous_coe)
  have hAp (n : ℕ) : IsStronglyProgressive f (A n) := by
    intro T
    have hQ := (hQp n T).measurable
    let : MeasurableSpace Ω := f T
    have hv : MeasurableSet {p : Iic T × Ω | v n p.1 p.2} :=
      (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
        (measurableSet_le measurable_const (Complex.measurable_im.comp hQ.fst)))
    exact (Measurable.ite hv
      ((Complex.measurable_ofReal.comp (Complex.measurable_re.comp hQ.fst)).add
        ((Complex.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
          (Complex.measurable_im.comp hQ.fst))).mul_const I)) measurable_const).stronglyMeasurable
  have hlim (t : ℝ≥0) (ω : Ω) : Tendsto (fun n => A n t ω) atTop
      (𝓝 (if z ∈ survivingDomain (γ ω) t then G ω t z else 0)) := by
    apply tendsto_nhds_of_eventually_eq
    have hU : Continuous (fun s => Real.sqrt κ * B s ω) := (hc ω).const_mul _
    have hd (n : ℕ) (s : ℝ) (hs : s ∈ Icc 0 (t : ℝ)) :=
      ((c n).derivative ω s hs.1).mono (show Icc (0 : ℝ) (t : ℝ) ⊆ Ici 0 from Icc_subset_Ici_self)
    by_cases hz : z ∈ survivingDomain (γ ω) t
    · obtain ⟨N, hN⟩ := exists_nat_ge (max (-Real.log (G ω t z).im) (Real.log z.im))
      filter_upwards [eventually_ge_atTop N] with n hn
      have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
      have hlo : -(n : ℝ) ≤ Real.log (G ω t z).im := by
        have hh := (le_max_left (-Real.log (G ω t z).im) (Real.log z.im)).trans (hN.trans hNn)
        linarith
      have hhi : Real.log z.im ≤ (n : ℝ) := (le_max_right _ _).trans (hN.trans hNn)
      have he : (c n).Q t ω = logLoewnerCoordinates (G ω) z t :=
        clipped_log_loewner_agrees hU (hw ω) t z hz _ _ _ hlo hhi
          (fun s => (c n).Q s ω) ((c n).initial ω) (hd n) ⟨t.coe_nonneg, le_rfl⟩
      have hv : v n t ω := ⟨hz.1.1, hhi, by simpa only [he, logCoordinates_im] using hlo⟩
      simp only [A, ite_eq_left hz, ite_eq_left hv, he, logCoordinates_re, logCoordinates_im,
        Real.exp_log ((hw ω).imag_positive t z hz)]
      exact Complex.re_add_im _
    · filter_upwards [] with n
      have hv : ¬ v n t ω := by
        intro hv
        exact hz (clipped_log_identification_of_endpoint hU (hw ω) t z hv.1 _ _ _
          (fun s => (c n).Q s ω) ((c n).initial ω) (hd n) hv.2.2 hv.2.1).1
      simp only [A, ite_eq_right hv, ite_eq_right hz]
  exact isStronglyProgressive_of_tendsto hAp
    (tendsto_pi_nhds.mpr (fun t => tendsto_pi_nhds.mpr (hlim t)))

end
end SLEExactGauge
end
end

end OAI
