import OAI.Analysis.CircleDomains.Selection.MappedMeanBands

namespace OAI

/-! Dust-band estimates for the same local representative used in the
Sobolev construction. The lift only needs nonnegative height on the domain. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 def upperHalfPlaneClamp (z : ℂ) : ClosedUpperHalfPlane :=
  ⟨⟨z.re, max z.im 0⟩, le_max_right _ _⟩

 theorem continuous_upperHalfPlaneClamp : Continuous upperHalfPlaneClamp :=
  (Complex.equivRealProdCLM.symm.continuous.comp
    (Complex.continuous_re.prodMk (Complex.continuous_im.max continuous_const))).subtype_mk _

 theorem upperHalfPlaneClamp_val {z : ℂ} (hz : 0 ≤ z.im) :
    (upperHalfPlaneClamp z).val = z :=
  Complex.ext rfl (max_eq_left hz)

 theorem liftedMeanGeometricIndex_eq_clamp
    (hsch : PlanarSchoenflies) (K : Set C(PathTime, ℂ)) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (Ψ : ℂ → ℂ) {z : ℂ} (hz : 0 ≤ (Ψ z).im) :
    liftedMeanGeometricIndex hsch K hKS η Ψ z =
      meanGeometricIndex hsch K hKS η (upperHalfPlaneClamp (Ψ z)) := by
  rw [liftedMeanGeometricIndex_eq hsch K hKS η Ψ z hz]
  congr 1
  exact Subtype.ext (upperHalfPlaneClamp_val hz).symm

 theorem liftedMeanGeometricIndex_band_width
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (S : Set ℂ) (s : ℂ) (hs : s ∈ closure S)
    (Ψ : ℂ → ℂ) (hΨ : ContinuousWithinAt Ψ S s)
    (hpos : ∀ z ∈ S, 0 ≤ (Ψ z).im) (hz : 0 < (Ψ s).im) :
    limsup (liftedMeanGeometricIndex hsch K hKS η Ψ) (𝓝[S] s) -
      liminf (liftedMeanGeometricIndex hsch K hKS η Ψ) (𝓝[S] s) ≤
        (η : Measure K).real {γ | diskRayProjection (Ψ s) ∈ range γ.val} := by
  let L := upperHalfPlaneClamp ∘ Ψ
  have hL : ContinuousWithinAt L S s :=
    continuous_upperHalfPlaneClamp.continuousAt.comp_continuousWithinAt hΨ
  have hh : (L s).val.im > 0 := by
    change (upperHalfPlaneClamp (Ψ s)).val.im > 0
    rw [upperHalfPlaneClamp_val hz.le]
    exact hz
  have hb := meanGeometricIndex_band_width hsch hsep K hK hKS η S s hs L hL hh
  have he : liftedMeanGeometricIndex hsch K hKS η Ψ =ᶠ[𝓝[S] s]
      fun z => meanGeometricIndex hsch K hKS η (L z) := by
    filter_upwards [self_mem_nhdsWithin] with z hzS
    exact liftedMeanGeometricIndex_eq_clamp hsch K hKS η Ψ (hpos z hzS)
  rw [limsup_congr he, liminf_congr he]
  simpa only [L, Function.comp_apply, upperHalfPlaneClamp_val hz.le] using hb

end CircleDomainRigidity

end

end OAI
