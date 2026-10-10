import OAI.Analysis.CircleDomains.Probability.CodeLocalBandTagNull
import OAI.Analysis.CircleDomains.Probability.CircleNullImage
import OAI.Analysis.CircleDomains.Modulus.CodeFreeIncidence

namespace OAI

/-! Local real trace estimates remove circle-level incidences. Their
assembly uses outer measure only, so the free set need not be Borel. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

namespace CircleDomainRigidity

theorem local_level_incidence_null_of_real_trace
    {X : Type*} [TopologicalSpace X]
    (D Free V : Set X) (H : Set (UnitAddCircle × X))
    (f trace : X → ℝ) (γ : C(PathTime, X)) (T : Set PathTime)
    (hlevel : ∀ x ∈ V, ∀ θ, (x, θ) ∈ circleBandGraph D f ↔ (θ, x) ∈ H)
    (htrace : ∀ x ∈ Free ∩ V, ∀ a,
      (x, a) ∈ intervalFiberHull (clusterGraph D f) ↔ a = trace x)
    (hnull : volume ((trace ∘ γ) '' (γ ⁻¹' Free ∩ (T ∩ γ ⁻¹' V))) = 0) :
    volume {θ | ∃ t ∈ T, γ t ∈ Free ∩ V ∧ (θ, γ t) ∈ H} = 0 := by
  apply measure_mono_null (t := ((↑) : ℝ → UnitAddCircle) ''
    ((trace ∘ γ) '' (γ ⁻¹' Free ∩ (T ∩ γ ⁻¹' V)))) _
    (volume_addCircle_image_eq_zero hnull)
  rintro θ ⟨t, ht, hx, hθ⟩
  obtain ⟨⟨x, a⟩, ha, he⟩ := (hlevel (γ t) hx.2 θ).mpr hθ
  change (x, (a : UnitAddCircle)) = (γ t, θ) at he
  have hxEq : x = γ t := congrArg Prod.fst he
  subst x
  have haEq : a = trace (γ t) := (htrace (γ t) hx a).mp ha
  refine ⟨trace (γ t), ⟨t, ⟨hx.1, ht, hx.2⟩, rfl⟩, ?_⟩
  simpa only [haEq] using congrArg Prod.snd he

theorem level_incidence_null_of_countable_cover
    {X I : Type*} [TopologicalSpace X] [Countable I]
    (Free : Set X) (H : Set (UnitAddCircle × X))
    (V : I → Set X) (γ : C(PathTime, X)) (T : Set PathTime)
    (hcover : ∀ x ∈ Free, ∀ θ, (θ, x) ∈ H → ∃ i, x ∈ V i)
    (hnull : ∀ i, volume {θ | ∃ t ∈ T, γ t ∈ Free ∩ V i ∧ (θ, γ t) ∈ H} = 0) :
    volume {θ | ∃ t ∈ T, γ t ∈ Free ∧ (θ, γ t) ∈ H} = 0 := by
  apply measure_mono_null (t := ⋃ i : I,
    {θ | ∃ t ∈ T, γ t ∈ Free ∩ V i ∧ (θ, γ t) ∈ H}) _ (measure_iUnion_null hnull)
  rintro θ ⟨t, ht, hx, hθ⟩
  obtain ⟨i, hi⟩ := hcover (γ t) hx θ hθ
  exact mem_iUnion.mpr ⟨i, t, ht, ⟨hx, hi⟩, hθ⟩

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

theorem ae_code_free_incidence_null_of_local_real_traces
    [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]
    (d : PathCodeData Sphere Sphere) (P : ProbabilityMeasure (BasePathCode d)) (i : ℕ)
    (Free : Set Sphere) (hFree : Free ⊆ d.dust)
    (hm : (support (d.levelWeights i)).Countable)
    (hweight : countingSquareNorm (fun x : support (d.levelWeights i) =>
      d.levelWeights i x.val) < ∞)
    (hvisits : countingSquareNorm (fun x : support (d.levelWeights i) =>
      meanVisitCount (codePathLaw d P) x.val) < ∞)
    (hdeleteCover : ∀ x ∈ support (d.levelWeights i), ∀ᶠ n in atTop, x ∈ d.flagDeletions n)
    (hdelete : ∀ n, Disjoint Free (d.flagDeletions n : Set Sphere))
    {I : Type*} [Countable I] (V : I → Set Sphere) (f trace : I → Sphere → ℝ)
    (hcover : ∀ x ∈ Free, ∀ θ, (θ, x) ∈ d.levels i → ∃ j, x ∈ V j)
    (hlevel : ∀ j x, x ∈ V j → ∀ θ,
      (x, θ) ∈ circleBandGraph d.quotientDomain (f j) ↔ (θ, x) ∈ d.levels i)
    (htrace : ∀ j x, x ∈ Free ∩ V j → ∀ a,
      (x, a) ∈ intervalFiberHull (clusterGraph d.quotientDomain (f j)) ↔ a = trace j x)
    (hnull : ∀ j, ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ∀ k,
      volume ((trace j ∘ Γ.val.1) '' (Γ.val.1 ⁻¹' Free ∩
        (Ioo (tagLeft (Γ.val.2 k)) (tagRight (Γ.val.2 k)) ∩ Γ.val.1 ⁻¹' V j))) = 0) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)),
      volume {θ | ∃ x ∈ range Γ.val.1 ∩ Free, (θ, x) ∈ d.levels i} = 0 := by
  apply ae_code_free_level_incidence_null_of_tags d P i Free hFree hm hweight hvisits hdeleteCover hdelete
  filter_upwards [ae_all_iff.mpr hnull] with Γ hΓ
  intro k
  apply level_incidence_null_of_countable_cover Free (d.levels i) V Γ.val.1
    (Ioo (tagLeft (Γ.val.2 k)) (tagRight (Γ.val.2 k))) hcover
  intro j
  exact local_level_incidence_null_of_real_trace d.quotientDomain Free (V j)
    (d.levels i) (f j) (trace j) Γ.val.1 _ (hlevel j) (htrace j) (hΓ j k)

end CircleDomainRigidity

end OAI
