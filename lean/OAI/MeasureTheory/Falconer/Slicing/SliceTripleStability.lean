import OAI.MeasureTheory.Falconer.Estimates.TripleGramStability
import OAI.MeasureTheory.Falconer.Slicing.OrientedSlice

namespace OAI

/-! # Original transverse triples remain transverse in the selected slice -/

namespace Falconer
open NormedSpace
variable {d m : ℕ}

theorem gram_slice_isometry (V : Submodule ℝ (Space d))
    (e : V ≃ₗᵢ[ℝ] Space m) (u : Fin 3 → V) :
    (Matrix.gram ℝ (fun i => (u i : Space d))).det =
      (Matrix.gram ℝ (fun i => e (u i))).det := by
  congr 1
  ext i j
  exact (e.inner_map_map (u i) (u j)).symm

theorem slice_triple_gram_stability (V : Submodule ℝ (Space d))
    (e : V ≃ₗᵢ[ℝ] Space m) (w : Fin 3 → Sphere d) {δ : ℝ}
    (hδ : δ < 1) (hw : ∀ i, w i ∈ directionSliceBand V δ) :
    |(Matrix.gram ℝ (fun i => (w i : Space d))).det -
      (Matrix.gram ℝ (fun i => normalize (e (V.orthogonalProjectionOnto (w i : Space d))))).det|
      ≤ 72*δ := by
  let u : Fin 3 → V := fun i => normalize (V.orthogonalProjectionOnto (w i : Space d))
  have hp (i : Fin 3) : V.orthogonalProjectionOnto (w i : Space d) ≠ 0 := by
    intro hz
    have hlo := directionSliceBand_projection_lower V (hw i)
    have he : V.starProjection (w i : Space d) = 0 := congrArg Subtype.val hz
    rw [he,norm_zero] at hlo
    linarith
  have hn (i : Fin 3) : ‖(u i : Space d)‖ ≤ 1 := by
    change ‖normalize (V.orthogonalProjectionOnto (w i : Space d))‖ ≤ 1
    rw [norm_normalize (hp i)]
  have hc (i : Fin 3) : ‖(w i : Space d)-(u i : Space d)‖ ≤ 2*δ := by
    rw [norm_sub_rev]
    exact directionSliceBand_normalize_error V hδ (hw i)
  have hh := gram_three_stability (fun i => (w i : Space d)) (fun i => (u i : Space d))
    (fun i => (sphere_norm (w i)).le) hn hc
  rw [gram_slice_isometry V e u] at hh
  have he : (fun i => e (u i)) =
      (fun i => normalize (e (V.orthogonalProjectionOnto (w i : Space d)))) := by
    funext i
    exact slice_isometry_normalize V e _
  rw [he] at hh
  linarith

theorem slice_triple_gram_lower (V : Submodule ℝ (Space d))
    (e : V ≃ₗᵢ[ℝ] Space 3) (w : Fin 3 → Sphere d) {δ Δ : ℝ}
    (hδ : δ < 1) (hw : ∀ i, w i ∈ directionSliceBand V δ)
    (hΔ : 0 ≤ Δ)
    (hgram : 2*Δ ≤ Real.sqrt ((Matrix.gram ℝ (fun i => (w i : Space d))).det))
    (hsmall : 72*δ ≤ 3*Δ^2) :
    Δ ≤ Real.sqrt ((Matrix.gram ℝ (fun i =>
      normalize (e (V.orthogonalProjectionOnto (w i : Space d))))).det) := by
  have hg0 : 0 ≤ (Matrix.gram ℝ (fun i => (w i : Space d))).det :=
    (Matrix.posSemidef_gram ℝ _).det_nonneg
  have hs0 : 0 ≤ (Matrix.gram ℝ (fun i =>
      normalize (e (V.orthogonalProjectionOnto (w i : Space d))))).det :=
    (Matrix.posSemidef_gram ℝ _).det_nonneg
  have hs := slice_triple_gram_stability V e w hδ hw
  have hsq := Real.sq_sqrt hg0
  have hsq' := Real.sq_sqrt hs0
  have hlow := (abs_le.mp hs).2
  have hroot := Real.sqrt_nonneg ((Matrix.gram ℝ (fun i =>
      normalize (e (V.orthogonalProjectionOnto (w i : Space d))))).det)
  nlinarith [Real.sqrt_nonneg ((Matrix.gram ℝ (fun i => (w i : Space d))).det)]

end Falconer

end OAI
