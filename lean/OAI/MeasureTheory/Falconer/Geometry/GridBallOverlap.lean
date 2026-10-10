import OAI.MeasureTheory.Falconer.Geometry.GeneralGridRounding
import OAI.MeasureTheory.Falconer.Estimates.FiniteOverlap

namespace OAI

/-! # Uniform overlap of fixed-width lattice cells -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {n : ℕ}
attribute [local instance] Classical.propDecidable

theorem grid_ball_overlap (S : Finset (Fin (n+1) → ℤ)) {δ C : ℝ}
    (hδ : 0 < δ) (L : ℕ) (hL : C+1/2 ≤ (L:ℝ)) (x : Space (n+1)) :
    (S.filter (fun z => ‖x-euclideanIntegerGrid δ z‖ ≤ C*δ)).card ≤ (2*L+1)^(n+1) := by
  apply integer_box_card _ (fun j => x j/δ) C L hL
  intro z hz j
  have hb := (PiLp.norm_apply_le (x-euclideanIntegerGrid δ z) j).trans (Finset.mem_filter.mp hz).2
  change |x j-δ*(z j:ℝ)| ≤ C*δ at hb
  have hd : |(x j-δ*(z j:ℝ))/δ| ≤ C := by
    rw [abs_div,abs_of_pos hδ]
    exact (div_le_iff₀ hδ).mpr hb
  have he : (x j-δ*(z j:ℝ))/δ = x j/δ-(z j:ℝ) := by field_simp
  rw [he,abs_sub_comm] at hd
  exact hd

theorem grid_ball_heavy_card (μ : Measure (Space (n+1)))
    (f : Space (n+1) → Space (n+1)) (hf : Measurable f)
    (S : Finset (Fin (n+1) → ℤ)) {δ C : ℝ} (hδ : 0 < δ)
    (L : ℕ) (hL : C+1/2 ≤ (L:ℝ)) (F : ℝ≥0∞)
    (hheavy : ∀ z ∈ S, F ≤ μ {x | ‖f x-euclideanIntegerGrid δ z‖ ≤ C*δ}) :
    (S.card:ℝ≥0∞)*F ≤ ((2*L+1)^(n+1):ℕ)*μ univ := by
  apply heavy_family_card_bound μ S
    (fun z => {x | ‖f x-euclideanIntegerGrid δ z‖ ≤ C*δ})
    (fun z _ => measurableSet_le (by fun_prop) measurable_const)
    ((2*L+1)^(n+1)) (fun x => grid_ball_overlap S hδ L hL (f x)) F hheavy

end Falconer

end OAI
