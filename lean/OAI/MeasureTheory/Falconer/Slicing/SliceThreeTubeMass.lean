import OAI.MeasureTheory.Falconer.Estimates.ThreeTubePullback
import OAI.MeasureTheory.Falconer.Slicing.SliceTripleStability

namespace OAI

/-! # The endpoint tube obstruction expressed on the original point law -/

namespace Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem slice_three_tube_mass_sq (μ : Measure (Space d))
    (V : Submodule ℝ (Space d)) (e : V ≃ₗᵢ[ℝ] Space 3)
    (w : Fin 3 → Sphere d) {η Δ : ℝ} (hη : η < 1)
    (hband : ∀ i, w i ∈ directionSliceBand V η)
    (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (hgram : 2*Δ ≤ Real.sqrt ((Matrix.gram ℝ (fun i => (w i : Space d))).det))
    (herror : 72*η ≤ 3*Δ^2)
    (E : Set (Space d)) (A : Fin 3 → Finset (Space d)) (R : ℝ)
    (hE : ∀ x ∈ E, ‖x‖ ≤ R) {δ C H s : ℝ} (hδ : 0 < δ)
    (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hball : ∀ p : Space 3, μ {x | dist (e (V.orthogonalProjectionOnto x)) p < 6*δ} ≤
      ENNReal.ofReal (H*(6*δ)^s))
    (hcover : ∀ i : Fin 3, ∀ x ∈ E, ∃ a ∈ A i,
      ‖perpendicularPart (w i : Space d) (x-a)‖ ≤ C*δ) :
    (μ E).toReal^2 ≤ ((A 0).card:ℝ)*((A 1).card:ℝ)*((A 2).card:ℝ)*
      ((6*C+35)/Δ)^6*(H*(6*δ)^s)^2 := by
  let f : Space d → Space 3 := fun x => e (V.orthogonalProjectionOnto x)
  let v : Fin 3 → Space 3 := fun i => normalize (f (w i))
  have hv (i : Fin 3) : ‖v i‖ = 1 := by
    have hp : V.orthogonalProjectionOnto (w i : Space d) ≠ 0 := by
      intro hz
      have hh := directionSliceBand_projection_lower V (hband i)
      have he : V.starProjection (w i : Space d) = 0 := congrArg Subtype.val hz
      rw [he,norm_zero] at hh
      linarith
    exact norm_normalize (fun hz => hp (e.injective (by simpa only [map_zero] using hz)))
  have hg : Δ ≤ Real.sqrt (tripleGram (v 0) (v 1) (v 2)) := by
    have hh := slice_triple_gram_lower V e w hη hband hΔ.le hgram herror
    have he : ![v 0,v 1,v 2] = v := by ext i; fin_cases i <;> rfl
    change Δ ≤ Real.sqrt (Matrix.gram ℝ ![v 0,v 1,v 2]).det
    rw [he]
    exact hh
  have hnE : ∀ x ∈ E, ‖f x‖ ≤ R := by
    intro x hx
    exact ((e.norm_map _).le.trans (V.norm_orthogonalProjectionOnto_apply_le x)).trans (hE x hx)
  apply three_tube_pullback_mass_sq μ f v hv hΔ hΔ1 hg E A R hnE hδ hC hH hball
  intro i x hx
  obtain ⟨a,ha,ht⟩ := hcover i x hx
  exact ⟨a,ha,(oriented_slice_tube_width V e hη (hband i) x a).trans ht⟩

end Falconer

end OAI
