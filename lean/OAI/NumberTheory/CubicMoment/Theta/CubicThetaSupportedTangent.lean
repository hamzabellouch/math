import OAI.NumberTheory.CubicMoment.Theta.CubicThetaTangentVolume
import RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Rellich

namespace OAI

/-! Compactly supported complex chart sections give actual supported
real Sobolev vectors. The Euclidean Rellich theorem applies to these
vectors, with the concrete transported compact support. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment.LocalSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

local instance tangent_borel : MeasurableSpace CubicThetaTangent := borel CubicThetaTangent
local instance tangent_borelSpace : BorelSpace CubicThetaTangent := ⟨rfl⟩

private lemma supported_test (g : C1c (E:=CubicThetaTangent))
    {S : Set CubicThetaTangent} (hS : MeasurableSet S) (hg : tsupport (g: CubicThetaTangent → ℝ)⊆S) :
    (⟨graph (μ:=tangentBorelVolume) g,Submodule.le_topologicalClosure _ ⟨g,rfl⟩⟩ :
      h1 (μ:=tangentBorelVolume))∈h1On S hS := by
  change toL2 (μ:=tangentBorelVolume) g∈LinearMap.range (Lp.extendByZeroₗᵢ hS).toLinearMap
  have hmem := memLp_of_mem_C1c (μ:=tangentBorelVolume) g.property
  let r := (hmem.restrict S).toLp (g:CubicThetaTangent → ℝ)
  refine ⟨r,?_⟩
  apply Lp.ext
  have hlocal : ∀ᵐ x ∂tangentBorelVolume, x∈S → r x=(g:CubicThetaTangent → ℝ) x :=
    (ae_restrict_iff' hS).mp (hmem.restrict S).coeFn_toLp
  filter_upwards [Lp.extendByZeroₗᵢ_ae_eq hS r,hmem.coeFn_toLp,hlocal] with x hxt hval hloc
  change (Lp.extendByZeroₗᵢ hS r) x=((hmem.toLp _) x)
  rw [hxt,hval]
  by_cases hx : x∈S
  · rw [Set.indicator_of_mem hx,hloc hx]
  · rw [Set.indicator_of_notMem hx]
    exact (image_eq_zero_of_notMem_tsupport (fun ht => hx (hg ht))).symm

lemma realTest_support {K : Set (ℂ × ℝ)} (f : ℂ × ℝ → ℂ)
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (hK : tsupport f⊆K) :
    tsupport (realTest f hf hc : CubicThetaTangent → ℝ)⊆cubicThetaTangentCoordinates ⁻¹' K := by
  change tsupport (Complex.re ∘ (f ∘ cubicThetaTangentCoordinates))⊆_
  exact (tsupport_comp_subset (g:=Complex.re) (by simp) _).trans
    ((tsupport_comp_subset_preimage f cubicThetaTangentCoordinates.continuous).trans (preimage_mono hK))

lemma imagTest_support {K : Set (ℂ × ℝ)} (f : ℂ × ℝ → ℂ)
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (hK : tsupport f⊆K) :
    tsupport (imagTest f hf hc : CubicThetaTangent → ℝ)⊆cubicThetaTangentCoordinates ⁻¹' K := by
  change tsupport (Complex.im ∘ (f ∘ cubicThetaTangentCoordinates))⊆_
  exact (tsupport_comp_subset (g:=Complex.im) (by simp) _).trans
    ((tsupport_comp_subset_preimage f cubicThetaTangentCoordinates.continuous).trans (preimage_mono hK))

def realSupported {K : Set (ℂ × ℝ)} (hK : IsCompact K)
    (f : ℂ × ℝ → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (hs : tsupport f⊆K) :
    h1On (cubicThetaTangentCoordinates ⁻¹' K)
      (hK.isClosed.measurableSet.preimage cubicThetaTangentCoordinates.continuous.measurable) :=
  ⟨realH1 f hf hc,supported_test (realTest f hf hc) _ (realTest_support f hf hc hs)⟩

def imagSupported {K : Set (ℂ × ℝ)} (hK : IsCompact K)
    (f : ℂ × ℝ → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (hs : tsupport f⊆K) :
    h1On (cubicThetaTangentCoordinates ⁻¹' K)
      (hK.isClosed.measurableSet.preimage cubicThetaTangentCoordinates.continuous.measurable) :=
  ⟨imagH1 f hf hc,supported_test (imagTest f hf hc) _ (imagTest_support f hf hc hs)⟩

lemma supported_inclusion_compact {K : Set (ℂ × ℝ)} (hK : IsCompact K) :
    IsCompactOperator (h1OnToL2 (cubicThetaTangentCoordinates ⁻¹' K)
      (hK.isClosed.measurableSet.preimage cubicThetaTangentCoordinates.continuous.measurable)) :=
  isCompactOperator_h1OnToL2
    (cubicThetaTangentCoordinates.toHomeomorph.isCompact_preimage.mpr hK) _

end CubicFirstMoment.LocalSobolev

end

end OAI
