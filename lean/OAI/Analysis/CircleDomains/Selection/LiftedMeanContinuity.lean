import OAI.Analysis.CircleDomains.Selection.MeanGeometricIndex
import OAI.Analysis.CircleDomains.Probability.PathHitLaws

namespace OAI

/-! Continuous local representatives of the geometric mean index.
Point avoidance is transported through the actual injective Jordan map. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 def liftedMeanGeometricIndex (hsch : PlanarSchoenflies)
    (K : Set C(PathTime, ℂ)) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (Ψ : ℂ → ℂ) (z : ℂ) : ℝ :=
  if h : 0 ≤ (Ψ z).im then meanGeometricIndex hsch K hKS η ⟨Ψ z, h⟩ else 0

 theorem liftedMeanGeometricIndex_eq (hsch : PlanarSchoenflies)
    (K : Set C(PathTime, ℂ)) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (Ψ : ℂ → ℂ) (z : ℂ) (hz : 0 ≤ (Ψ z).im) :
    liftedMeanGeometricIndex hsch K hKS η Ψ z =
      meanGeometricIndex hsch K hKS η ⟨Ψ z, hz⟩ := dite_eq_left hz

 theorem continuousOn_liftedMeanGeometricIndex
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) {S : Set ℂ}
    (Ψ : ℂ → ℂ) (hΨ : ContinuousOn Ψ S)
    (hpos : ∀ z ∈ S, 0 ≤ (Ψ z).im)
    (hmiss : ∀ z ∈ S, ∀ᵐ γ : K ∂(η : Measure K),
      diskRayProjection (Ψ z) ∉ range γ.val) :
    ContinuousOn (liftedMeanGeometricIndex hsch K hKS η Ψ) S := by
  let L : S → ClosedUpperHalfPlane := fun z => ⟨Ψ z.val, hpos z.val z.property⟩
  have hL : Continuous L := (continuousOn_iff_continuous_domRestrict.mp hΨ).subtype_mk _
  have hm : Continuous (fun z : S => meanGeometricIndex hsch K hKS η (L z)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (continuousAt_meanGeometricIndex hsch hsep K hK hKS η (L z)
      (hmiss z.val z.property)).comp hL.continuousAt
  apply continuousOn_iff_continuous_domRestrict.mpr
  apply hm.congr
  intro z
  exact (liftedMeanGeometricIndex_eq hsch K hKS η Ψ z.val (hpos z.val z.property)).symm

 theorem bounded_liftedMeanGeometricIndex_on_compact
    (hsch : PlanarSchoenflies) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure K)
    {S : Set ℂ} (hS : IsCompact S) (Ψ : ℂ → ℂ) (hΨ : ContinuousOn Ψ S)
    (hpos : ∀ z ∈ S, 0 ≤ (Ψ z).im) :
    ∃ M : ℝ, ∀ z ∈ S, ‖liftedMeanGeometricIndex hsch K hKS η Ψ z‖ ≤ M := by
  obtain ⟨R, hR⟩ := hS.exists_bound_of_continuousOn hΨ
  let T := max R 0
  have hT : 0 ≤ T := le_max_right _ _
  obtain ⟨M, hM⟩ := compact_geometricRayIndex_bound hsch K hK hKS T T hT hT
  refine ⟨M, ?_⟩
  intro z hz
  rw [liftedMeanGeometricIndex_eq hsch K hKS η Ψ z (hpos z hz)]
  have hb : ‖Ψ z‖ ≤ T := (hR z hz).trans (le_max_left _ _)
  have hx : |(Ψ z).re| ≤ T := (Complex.abs_re_le_norm _).trans hb
  have hy : (Ψ z).im ≤ T := (Complex.im_le_norm _).trans hb
  have hi : ∀ᵐ γ : K ∂(η : Measure K),
      ‖(geometricRayIndex hsch γ.val (hKS γ.property) (Ψ z) : ℝ)‖ ≤ M := by
    apply Eventually.of_forall
    intro γ
    simpa only [Complex.re_add_im, Real.norm_eq_abs] using
      hM γ (Ψ z).re (Ψ z).im hx (hpos z hz) hy
  simpa only [meanGeometricIndex, measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using
    norm_integral_le_of_norm_le_const hi

variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)]

 theorem ae_mapped_arc_avoids
    (A : Set C(PathTime, X)) (K : Set C(PathTime, ℂ)) (η : ProbabilityMeasure A)
    (F : C(X, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (x : X) (hx : ∀ᵐ γ : A ∂(η : Measure A), x ∉ range γ.val)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ {x})) :
    ∀ᵐ γ : K ∂((η.map f : ProbabilityMeasure K) : Measure K), F x ∉ range γ.val := by
  rw [ProbabilityMeasure.toMeasure_map]
  apply (ae_map_iff hf.aemeasurable ?_).mpr
  · filter_upwards [hx] with γ hγ
    rw [hmap γ]
    rintro ⟨t, ht⟩
    exact hγ ⟨t, hF γ (Or.inl (mem_range_self t)) (Or.inr (mem_singleton x)) ht⟩
  · exact ((isClosed_pathHitSet.preimage
      (continuous_subtype_val.prodMk continuous_const)).isOpen_compl.measurableSet)

end CircleDomainRigidity

end

end OAI
