import OAI.Analysis.LipschitzHilbert.Trees.SourceCoordinateSpectrum
import OAI.Analysis.LipschitzHilbert.Estimates.PlanarFixedScaleEnergy

namespace OAI

/-! Finite sums of the original scalar planar packets are actual vector
Schwartz maps, and their coordinate cutoffs follow from those of the
nonzero summands. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped BigOperators FourierTransform
namespace LipschitzHilbert
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The Schwartz-map representative of the manuscript's fixed synthesis. -/
def planarSynthesisSchwartz (c : ι → EuclideanSpace ℂ κ)
    (f : ι → κ → SchwartzMap (ℝ×ℝ) ℂ) : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ) :=
  vectorSchwartz (fun k => ∑ i, c i k • f i k)

@[simp] theorem planarSynthesisSchwartz_apply (c : ι → EuclideanSpace ℂ κ)
    (f : ι → κ → SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    planarSynthesisSchwartz c f z=planarFixedSynthesis c f z := by
  ext k
  simp only [planarSynthesisSchwartz,vectorSchwartz_apply,sum_apply,smul_apply,
    smul_eq_mul,planarFixedSynthesis,WithLp.ofLp_toLp]

theorem planarSynthesisSchwartz_horizontal (c : ι → EuclideanSpace ℂ κ)
    (f : ι → κ → SchwartzMap (ℝ×ℝ) ℂ) (y : ℝ) (k : κ) :
    (vectorHorizontalSlice (planarSynthesisSchwartz c f) y).postcompCLM (vectorCoordinate k)=
      packetSynthesis (fun i => c i k) (fun i => planarSchwartzSlice (f i k) y 0) := by
  ext x
  simp only [SchwartzMap.postcompCLM_apply,vectorCoordinate_apply,vectorHorizontalSlice_apply,
    planarSynthesisSchwartz,vectorSchwartz_apply,sum_apply,smul_apply,smul_eq_mul,
    packetSynthesis_apply,planarSchwartzSlice_apply,zero_mul,add_zero]

theorem planarSynthesisSchwartz_vertical (c : ι → EuclideanSpace ℂ κ)
    (f : ι → κ → SchwartzMap (ℝ×ℝ) ℂ) (x : ℝ) (k : κ) :
    (vectorVerticalSlice (planarSynthesisSchwartz c f) x).postcompCLM (vectorCoordinate k)=
      packetSynthesis (fun i => c i k) (fun i => planarVerticalSlice (f i k) x) := by
  ext y
  simp only [SchwartzMap.postcompCLM_apply,vectorCoordinate_apply,vectorVerticalSlice_apply,
    planarSynthesisSchwartz,vectorSchwartz_apply,sum_apply,smul_apply,smul_eq_mul,
    packetSynthesis_apply,planarVerticalSlice_apply]

theorem planarSynthesisSchwartz_coordinate_bands (c : ι → EuclideanSpace ℂ κ)
    (f : ι → κ → SchwartzMap (ℝ×ℝ) ℂ) (Rx Ry : ℝ)
    (hfx : ∀ i k, c i k≠0 → ∀ y ξ, 𝓕 (planarSchwartzSlice (f i k) y 0) ξ≠0 → |ξ|≤Rx)
    (hfy : ∀ i k, c i k≠0 → ∀ x η, 𝓕 (planarVerticalSlice (f i k) x) η≠0 → |η|≤Ry) :
    (∀ y ξ, 𝓕 (vectorHorizontalSlice (planarSynthesisSchwartz c f) y) ξ≠0 → |ξ|≤Rx) ∧
    (∀ x η, 𝓕 (vectorVerticalSlice (planarSynthesisSchwartz c f) x) η≠0 → |η|≤Ry) := by
  constructor
  · intro y ξ hne
    by_contra hn
    apply hne
    ext k
    rw [vector_fourier_coordinate,planarSynthesisSchwartz_horizontal,packetSynthesis_fourier]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hc : c i k=0
    · rw [hc,zero_mul]
    · have hz : 𝓕 (planarSchwartzSlice (f i k) y 0) ξ=0 := by
        by_contra h
        exact hn (hfx i k hc y ξ h)
      rw [hz,mul_zero]
  · intro x η hne
    by_contra hn
    apply hne
    ext k
    rw [vector_fourier_coordinate,planarSynthesisSchwartz_vertical,packetSynthesis_fourier]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hc : c i k=0
    · rw [hc,zero_mul]
    · have hz : 𝓕 (planarVerticalSlice (f i k) x) η=0 := by
        by_contra h
        exact hn (hfy i k hc x η h)
      rw [hz,mul_zero]

end LipschitzHilbert

end

end OAI
