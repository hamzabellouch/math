import OAI.MeasureTheory.Falconer.Slicing.SliceTripleStability
import OAI.MeasureTheory.Falconer.Slicing.GaussianRowDimension

namespace OAI

/-! # Quantitative transversality of the actual three-dimensional Gaussian slice -/

namespace Falconer
open NormedSpace
variable {h : ℕ}

theorem gaussian_three_dimensional_transverse_slice
    (B : Space h →ₗᵢ[ℝ] Space (h+3)) (A : Fin h → Space (h+3))
    (w : Fin 3 → Sphere (h+3)) {ε δ Δ : ℝ}
    (hA : ∀ i, ‖A i-B (EuclideanSpace.basisFun (Fin h) ℝ i)‖ ≤ ε)
    (hstable : (h:ℝ)*ε ≤ 1/2)
    (hsmall : 2*(h:ℝ)*δ < 1)
    (hband : ∀ i, w i ∈ gaussianDirectionBand A δ)
    (hΔ : 0 ≤ Δ)
    (hgram : 2*Δ ≤ Real.sqrt ((Matrix.gram ℝ (fun i => (w i : Space (h+3)))).det))
    (herror : 144*(h:ℝ)*δ ≤ 3*Δ^2) :
    ∃ e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space 3,
      (∀ i, ‖normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w i : Space (h+3))))‖ = 1) ∧
      Δ ≤ Real.sqrt ((Matrix.gram ℝ (fun i =>
        normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w i : Space (h+3)))))).det) := by
  have hdim : Module.finrank ℝ (gaussianRowMap A).ker = 3 := by
    simpa only [Nat.add_sub_cancel_left] using row_kernel_finrank A B hA hstable
  let e := sliceCoordinates (gaussianRowMap A).ker hdim
  have hb (i : Fin 3) : w i ∈ directionSliceBand (gaussianRowMap A).ker (2*(h:ℝ)*δ) := by
    have hh := gaussian_direction_band_kernel_distance A (by norm_num)
      (row_kernel_projection_bound A B hA hstable) (hband i)
    change ‖(gaussianRowMap A).kerᗮ.starProjection (w i : Space (h+3))‖ ≤ 2*(h:ℝ)*δ
    convert hh using 1
    ring
  refine ⟨e,?_,slice_triple_gram_lower _ e w hsmall hb hΔ hgram (by nlinarith)⟩
  intro i
  have hp : (gaussianRowMap A).ker.orthogonalProjectionOnto (w i : Space (h+3)) ≠ 0 := by
    intro hz
    have hh := directionSliceBand_projection_lower (gaussianRowMap A).ker (hb i)
    have he := congrArg Subtype.val hz
    change (gaussianRowMap A).ker.starProjection (w i : Space (h+3)) = 0 at he
    rw [he,norm_zero] at hh
    linarith
  exact norm_normalize (fun hz => hp (e.injective (by simpa only [map_zero] using hz)))

end Falconer

end OAI
