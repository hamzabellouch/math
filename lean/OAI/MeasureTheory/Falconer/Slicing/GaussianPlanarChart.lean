import OAI.MeasureTheory.Falconer.Slicing.OrientedSlice
import OAI.MeasureTheory.Falconer.Slicing.GaussianRowDimension
import OAI.MeasureTheory.Falconer.Slicing.GaussianKernelCoordinates

namespace OAI

/-! # Every selected codimension-h slice in dimension h+2 has a controlled planar chart -/

namespace Falconer
open NormedSpace
variable {h : ℕ}

theorem gaussian_two_dimensional_slice_chart
    (B : Space h →ₗᵢ[ℝ] Space (h+2)) (A : Fin h → Space (h+2)) (w₀ : Sphere (h+2))
    {ε δ ρ : ℝ} (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ)
    (hB : ∀ i, inner ℝ (w₀:Space (h+2)) (B (EuclideanSpace.basisFun (Fin h) ℝ i)) = 0)
    (hA : ∀ i, ‖A i-B (EuclideanSpace.basisFun (Fin h) ℝ i)‖ ≤ ε)
    (hstable : (h:ℝ)*ε ≤ 1/2)
    (hchart : 4*(h:ℝ)*δ+ρ+4*(h:ℝ)*ε ≤ 1/4) :
    ∃ e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space 2,
      normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w₀:Space (h+2)))) =
        EuclideanSpace.basisFun (Fin 2) ℝ 0 ∧
      ∀ w : Sphere (h+2), w ∈ gaussianDirectionBand A δ → dist w w₀ ≤ ρ →
        ‖normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space (h+2))))‖ = 1 ∧
        dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space (h+2)))))
          (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4 := by
  have hpδ : 0 ≤ (h:ℝ)*δ := by positivity
  have hpε : 0 ≤ (h:ℝ)*ε := by positivity
  have hsδ : 2*((h:ℝ)*δ) < 1 := by nlinarith
  have hsε : 2*((h:ℝ)*ε) < 1 := by nlinarith
  have hbound := row_kernel_projection_bound A B hA hstable
  have hw₀ : w₀ ∈ gaussianDirectionBand A ε := by
    intro i
    have he : inner ℝ (w₀:Space (h+2)) (A i) =
        inner ℝ (w₀:Space (h+2)) (A i-B (EuclideanSpace.basisFun (Fin h) ℝ i)) := by
      rw [inner_sub_right,hB i,sub_zero]
    rw [he]
    exact (abs_real_inner_le_norm _ _).trans (by simpa only [sphere_norm,one_mul] using hA i)
  have hdim : Module.finrank ℝ (gaussianRowMap A).ker = 2 := by
    simpa only [Nat.add_sub_cancel_left] using row_kernel_finrank A B hA hstable
  obtain ⟨e,he⟩ := exists_oriented_slice_coordinates (gaussianRowMap A).ker hdim (by norm_num)
    (w₀:Space (h+2)) (gaussian_direction_kernel_nonzero A (by norm_num) hbound hsε hw₀)
  refine ⟨e,he,?_⟩
  intro w hw hclose
  have hn := gaussian_direction_kernel_nonzero A (by norm_num) hbound hsδ hw
  have hv : (gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space (h+2)) ≠ 0 :=
    fun hz => hn (congrArg Subtype.val hz)
  have hev : e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space (h+2))) ≠ 0 :=
    fun hz => hv (e.injective (by simpa only [map_zero] using hz))
  refine ⟨norm_normalize hev,?_⟩
  have hd := oriented_slice_direction_distance (gaussianRowMap A).ker e hsδ hsε
    (gaussian_direction_band_kernel_distance A (by norm_num) hbound hw)
    (gaussian_direction_band_kernel_distance A (by norm_num) hbound hw₀) hclose
  rw [he] at hd
  exact hd.trans (by nlinarith)

end Falconer

end OAI
