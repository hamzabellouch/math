import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.JAction
import OAI.Geometry.TamingCompatibility.DifferentialForms.MetricCoords
import OAI.Geometry.TamingCompatibility.Functional.ContinuousBundleNorm

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
namespace TamingCompatibility

section CompactFunctions

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]

def positiveFunctions : Set C(K, ℝ) := {f | ∀ x, 0 < f x}

omit [Nonempty K] in
lemma convex_positiveFunctions : Convex ℝ (positiveFunctions (K := K)) := by
  intro f hf g hg a b ha hb hab x
  change 0 < a * f x + b * g x
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simpa [ha0, hb1] using hg x
  · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne ha (Ne.symm ha0)) (hf x))
      (mul_nonneg hb (hg x).le)

lemma isOpen_positiveFunctions : IsOpen (positiveFunctions (K := K)) := by
  rw [Metric.isOpen_iff]
  intro f hf
  obtain ⟨x₀, _, hmin⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty) f.continuous.continuousOn
  refine ⟨f x₀, hf x₀, ?_⟩
  intro g hg x
  have hdist := ContinuousMap.dist_apply_le_dist (f := g) (g := f) x
  have hball : dist g f < f x₀ := hg
  have hlo : f x₀ ≤ f x := hmin (Set.mem_univ x)
  rw [Real.dist_eq] at hdist
  have hl := (abs_le.mp hdist).1
  linarith

theorem exists_normalized_positive_annihilator
    (L : Submodule ℝ C(K, ℝ))
    (hL : Disjoint (positiveFunctions (K := K)) (L : Set C(K, ℝ))) :
    ∃ Λ : C(K, ℝ) →L[ℝ] ℝ, Λ 1 = 1 ∧
      (∀ f, (∀ x, 0 ≤ f x) → 0 ≤ Λ f) ∧ ∀ f ∈ L, Λ f = 0 := by
  obtain ⟨φ, u, hp, hl⟩ := geometric_hahn_banach_open
    convex_positiveFunctions isOpen_positiveFunctions L.convex hL
  have hu : u ≤ 0 := by simpa using hl 0 L.zero_mem
  have hφ1 : φ 1 < 0 := (hp 1 (fun _ => zero_lt_one)).trans_le hu
  have hz (f : C(K, ℝ)) (hf : f ∈ L) : φ f = 0 := by
    by_contra hne
    have h := hl (((u - 1) / φ f) • f) (L.smul_mem _ hf)
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at h
    linarith
  have hn (f : C(K, ℝ)) (hf : ∀ x, 0 ≤ f x) : φ f ≤ 0 := by
    by_contra! hpos
    let c : ℝ := -φ 1 / φ f + 1
    have hc : 0 < c := by
      dsimp [c]
      exact add_pos (div_pos (neg_pos.mpr hφ1) hpos) zero_lt_one
    have hp' : c • f + 1 ∈ positiveFunctions (K := K) := by
      intro x
      change 0 < c * f x + 1
      exact add_pos_of_nonneg_of_pos (mul_nonneg hc.le (hf x)) zero_lt_one
    have h := (hp _ hp').trans_le hu
    rw [map_add, map_smul, smul_eq_mul] at h
    dsimp [c] at h
    rw [add_mul, div_mul_cancel₀ _ hpos.ne'] at h
    linarith
  refine ⟨(φ 1)⁻¹ • φ, ?_, ?_, ?_⟩
  · change (φ 1)⁻¹ * φ 1 = 1
    exact inv_mul_cancel₀ hφ1.ne
  · intro f hf
    change 0 ≤ (φ 1)⁻¹ * φ f
    exact mul_nonneg_of_nonpos_of_nonpos (inv_nonpos.mpr hφ1.le) (hn f hf)
  · intro f hf
    change (φ 1)⁻¹ * φ f = 0
    rw [hz f hf, mul_zero]

variable [T2Space K] [MeasurableSpace K] [BorelSpace K]

theorem exists_probability_annihilating_subspace
    (L : Submodule ℝ C(K, ℝ))
    (hL : Disjoint (positiveFunctions (K := K)) (L : Set C(K, ℝ))) :
    ∃ μ : Measure K, IsProbabilityMeasure μ ∧ μ.Regular ∧
      ∀ f ∈ L, ∫ x, f x ∂μ = 0 := by
  obtain ⟨Λ, hΛ1, hΛpos, hΛL⟩ := exists_normalized_positive_annihilator L hL
  let Ψ : C_c(K, ℝ) →ₚ[ℝ] ℝ :=
    { toFun := fun f => Λ f.toContinuousMap
      map_add' := fun f g => by change Λ (f.toContinuousMap + g.toContinuousMap) = _; exact map_add Λ _ _
      map_smul' := fun c f => by change Λ (c • f.toContinuousMap) = _; exact map_smul Λ _ _
      monotone' := by
        intro f g hfg
        have h := hΛpos (g.toContinuousMap - f.toContinuousMap) (fun x => sub_nonneg.mpr (hfg x))
        rw [map_sub] at h
        exact sub_nonneg.mp h }
  let μ := RealRMK.rieszMeasure Ψ
  have hrepr (f : C(K, ℝ)) : ∫ x, f x ∂μ = Λ f := by
    let fc : C_c(K, ℝ) := ⟨f, HasCompactSupport.of_compactSpace f⟩
    exact RealRMK.integral_rieszMeasure Ψ fc
  have hmass : μ Set.univ = 1 := by
    have h := hrepr 1
    simp only [ContinuousMap.one_apply, integral_const, smul_eq_mul, mul_one, hΛ1] at h
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) ENNReal.one_ne_top).mp
    simpa only [Measure.real, ENNReal.toReal_one] using h
  exact ⟨μ, ⟨hmass⟩, inferInstance, fun f hf => (hrepr f).trans (hΛL f hf)⟩

end CompactFunctions

open Bundle Set MeasureTheory
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

lemma IsSmooth.continuous_tangentEval {α : TwoForm X} (hα : IsSmooth α)
    (J : AlmostComplexStructure X) :
    Continuous (fun p : TangentBundle Model X => eval α p.proj p.2 (J.endomorphism p.proj p.2)) := by
  have hm := (hα.associatedBilinear J).comp (contMDiff_proj (IB := Model) (n := ∞) (F := Space) (TangentSpace Model : X → Type))
  have he := hm.clm_bundle_apply₂ (F₁ := Space) (F₂ := Space) (F₃ := ℝ)
    (E₁ := TangentSpace Model) (E₂ := TangentSpace Model) (E₃ := Bundle.Trivial X ℝ)
    (IB := Model) (IM := Model.tangent) contMDiff_id contMDiff_id
  have hcont := he.continuous
  have hs := ((Bundle.Trivial.homeomorphProd X ℝ).continuous.comp hcont).snd
  change Continuous (fun p : TangentBundle Model X =>
    TamingCompatibility.associatedBilinear J α p.proj p.2 p.2) at hs
  simpa only [associatedBilinear_apply] using hs

abbrev MetricUnit (g : ContMDiffRiemannianMetric Model ∞ Space
    (TangentSpace Model : X → Type)) :=
  {p : TangentBundle Model X // g.inner p.proj p.2 p.2 = 1}

lemma isCompact_metricUnit [CompactSpace X] [T2Space X]
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type)) :
    IsCompact {p : TangentBundle Model X | g.inner p.proj p.2 p.2 = 1} := by
  let : RiemannianBundle (TangentSpace Model : X → Type) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle Space (TangentSpace Model : X → Type) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  have heq : {p : TangentBundle Model X | g.inner p.proj p.2 p.2 = 1} =
      {p : TangentBundle Model X | ‖p.2‖ = 1} := by
    ext p
    change inner ℝ p.2 p.2 = 1 ↔ ‖p.2‖ = 1
    rw [real_inner_self_eq_norm_sq]
    constructor
    · intro h
      nlinarith [norm_nonneg p.2]
    · intro h
      rw [h]
      norm_num
  rw [heq]
  exact isCompact_bundle_unitSphere

instance [CompactSpace X] [T2Space X]
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type)) :
    CompactSpace (MetricUnit g) :=
  isCompact_iff_compactSpace.mp (isCompact_metricUnit g)

def unitEvaluation (J : AlmostComplexStructure X) (g : ContMDiffRiemannianMetric Model ∞ Space
    (TangentSpace Model : X → Type)) (α : TwoForm X) (hα : IsSmooth α) :
    C(MetricUnit g, ℝ) :=
  ⟨fun p => eval α p.val.proj p.val.2 (J.endomorphism p.val.proj p.val.2),
    (hα.continuous_tangentEval J).comp continuous_subtype_val⟩

end TamingCompatibility

end

end OAI
