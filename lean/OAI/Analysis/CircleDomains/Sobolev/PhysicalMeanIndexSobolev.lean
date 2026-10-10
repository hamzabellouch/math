import OAI.Analysis.CircleDomains.Selection.PhysicalMeanIndexHorizontal
import OAI.Analysis.CircleDomains.Selection.PhysicalMeanIndexVertical
import OAI.Analysis.CircleDomains.Selection.LiftedMeanContinuity
import OAI.Analysis.CircleDomains.Probability.RectangleMeasurability
import OAI.Analysis.CircleDomains.Sobolev.PlanarSobolevTransport
import OAI.Analysis.CircleDomains.Sobolev.DensityL2

namespace OAI

/-! The locally lifted geometric mean has actual L² weak derivatives.
Both ACL directions follow from physical occupation and published coarea;
boundedness follows from the compact family of lifted terminal rays. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

omit [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)] in
 theorem sliceChartDensity_memLp_rectangle
    (B : ℝ≥0) (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞) (a b c d : ℝ) :
    MemLp (fun p : ℝ × ℝ => (sliceChartDensity B g ⟨p.1, p.2⟩).toReal) 2
      (volume.restrict (Icc a b ×ˢ Icc c d)) := by
  have hL := memLp_two_toReal_of_lintegral_sq_ne_top volume
    (measurable_sliceChartDensity B hg) (sliceChartDensity_sq_integral_finite B g hg henergy).ne
  have hP := hL.comp_measurePreserving
    (Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd)
  exact hP.restrict (Icc a b ×ˢ Icc c d)

 theorem physicalMeanIndex_rectangle_weak_gradient
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcoarea : PlanarLipschitzFiberCoarea)
    {G U : Set Sphere} (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    (A : Set C(PathTime, Sphere)) (hA : ∀ γ ∈ A, Injective γ)
    (η : ProbabilityMeasure A) (hfinite : ∀ γ ∈ A, physicalDomainLength e y₀ γ < ∞)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hocc : meanPhysicalOccupation e y₀ (η.map Subtype.val) = sphericalArea.withDensity g)
    (henergy : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    {a₀ a b b₀ c₀ c d d₀ : ℝ}
    (ha : a₀ < a) (hab : a < b) (hb : b < b₀)
    (hc : c₀ < c) (hcd : c < d) (hd : d < d₀)
    (hAG : MapsTo ((↑) : ℂ → Sphere) (planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀)) G)
    (B : ℝ≥0) (hB : LipschitzOnWith B finiteCoord
      (((↑) : ℂ → Sphere) '' planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀)))
    (Ψ : ℂ → ℂ) (hΨ : ContinuousOn Ψ (planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀)))
    (hpos : ∀ z ∈ planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀), 0 ≤ (Ψ z).im)
    (hproj : ∀ z ∈ planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀),
      diskRayProjection (Ψ z) = F (π (z : Sphere)))
    (hF : ∀ γ : A, InjOn F (range γ.val ∪
      (fun z : ℂ => π (z : Sphere)) '' planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀)))
    (hinj : InjOn (fun z : ℂ => F (π (z : Sphere)))
      (planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀))) :
    let v := liftedMeanGeometricIndex hsch K hKS (η.map f) Ψ
    let v₂ : ℝ × ℝ → ℝ := fun p => v ⟨p.1, p.2⟩
    MemLp v₂ 2 (volume.restrict (Icc a b ×ˢ Icc c d)) ∧
    ∃ Gx Gy : ℝ × ℝ → ℝ, Measurable Gx ∧ Measurable Gy ∧
      MemLp Gx 2 (volume.restrict (Icc a b ×ˢ Icc c d)) ∧
      MemLp Gy 2 (volume.restrict (Icc a b ×ˢ Icc c d)) ∧
      (∀ᵐ p ∂volume.restrict (Icc a b ×ˢ Icc c d),
        |Gx p| ≤ (sliceChartDensity B g ⟨p.1, p.2⟩).toReal ∧
        |Gy p| ≤ (sliceChartDensity B g ⟨p.1, p.2⟩).toReal) ∧
      ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ioo c d →
        (∫p in Icc a b ×ˢ Icc c d, v₂ p * (fderiv ℝ φ p) (1, 0)) =
          -(∫p in Icc a b ×ˢ Icc c d, Gx p * φ p) ∧
        (∫p in Icc a b ×ˢ Icc c d, v₂ p * (fderiv ℝ φ p) (0, 1)) =
          -(∫p in Icc a b ×ˢ Icc c d, Gy p * φ p) := by
  let v := liftedMeanGeometricIndex hsch K hKS (η.map f) Ψ
  let v₂ : ℝ × ℝ → ℝ := fun p => v ⟨p.1, p.2⟩
  let ρ : ℝ × ℝ → ℝ := fun p => (sliceChartDensity B g ⟨p.1, p.2⟩).toReal
  have hsx : planarSliceBox (Icc a₀ b₀) (Icc c d) ⊆
      planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀) :=
    planarSliceBox_mono Subset.rfl (Icc_subset_Icc hc.le hd.le)
  have hsy : planarSliceBox (Icc a b) (Icc c₀ d₀) ⊆
      planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀) :=
    planarSliceBox_mono (Icc_subset_Icc ha.le hb.le) Subset.rfl
  have hs : planarSliceBox (Icc a b) (Icc c d) ⊆
      planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀) :=
    planarSliceBox_mono (Icc_subset_Icc ha.le hb.le) (Icc_subset_Icc hc.le hd.le)
  have hx := physicalMeanIndex_horizontal_ACL_derivative hsch hsep hcoarea e hU y₀ π hπ he
    A hA η hfinite g hg hocc henergy K hK hKS F f hf hmap (Icc c d) isCompact_Icc
    ha hab.le hb (hAG.mono_left hsx) B (hB.mono (image_mono hsx)) Ψ (hΨ.mono hsx)
    (fun z hz => hpos z (hsx hz)) (fun z hz => hproj z (hsx hz)) v
    (fun z hz => liftedMeanGeometricIndex_eq hsch K hKS (η.map f) Ψ z (hpos z (hsx hz)))
    (fun γ => (hF γ).mono (union_subset_union Subset.rfl (image_mono hsx))) (hinj.mono hsx)
  have hy := physicalMeanIndex_vertical_ACL_derivative hsch hsep hcoarea e hU y₀ π hπ he
    A hA η hfinite g hg hocc henergy K hK hKS F f hf hmap (Icc a b) isCompact_Icc
    hc hcd.le hd (hAG.mono_left hsy) B (hB.mono (image_mono hsy)) Ψ (hΨ.mono hsy)
    (fun z hz => hpos z (hsy hz)) (fun z hz => hproj z (hsy hz)) v
    (fun z hz => liftedMeanGeometricIndex_eq hsch K hKS (η.map f) Ψ z (hpos z (hsy hz)))
    (fun γ => (hF γ).mono (union_subset_union Subset.rfl (image_mono hsy))) (hinj.mono hsy)
  have hacx := hx.mono fun _ h => h.1
  have hacy := hy.mono fun _ h => h.1
  have hbx := hx.mono fun _ h => h.2
  have hby := hy.mono fun _ h => h.2
  have hvmeas : AEStronglyMeasurable v₂ (volume.restrict (Icc a b ×ˢ Icc c d)) := by
    rw [← rectangle_restrict_Ioo_eq_Icc]
    exact aestronglyMeasurable_on_rectangle_of_ACL v₂ hab hcd hacx hacy
  obtain ⟨M, hM⟩ := bounded_liftedMeanGeometricIndex_on_compact hsch K hK hKS (η.map f)
    (isCompact_planarSliceBox isCompact_Icc isCompact_Icc) Ψ hΨ hpos
  let : IsFiniteMeasure ((volume : Measure (ℝ × ℝ)).restrict (Icc a b ×ˢ Icc c d)) :=
    isFiniteMeasure_restrict.mpr (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
  have hv₂ : MemLp v₂ 2 (volume.restrict (Icc a b ×ˢ Icc c d)) := by
    apply MemLp.of_bound hvmeas M
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
    exact hM ⟨p.1, p.2⟩ (hs ⟨hp.1, hp.2⟩)
  have hρ : Measurable ρ := (measurable_sliceChartDensity B hg).ennreal_toReal.comp
    Complex.measurableEquivRealProd.symm.measurable
  exact ⟨hv₂, exists_rectangle_weak_gradient hab.le hcd.le hv₂ hρ
    (sliceChartDensity_memLp_rectangle B g hg henergy a b c d) hacx hacy hbx hby⟩

end CircleDomainRigidity

end

end OAI
