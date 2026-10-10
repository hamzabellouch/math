import OAI.MeasureTheory.Falconer.Estimates.TwoProjectedLaws
import OAI.MeasureTheory.Falconer.Geometry.TwoProjectionPieces

namespace OAI

/-! # Choose the normalized pair geometry in the noncharging odd-dimensional case -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d n : ℕ}

theorem choose_odd_projected_pieces (hn : 2 ≤ n) (μ : ProbabilityMeasure (Space d))
    {s C ε : ℝ} (hs : (n:ℝ)-1/2 < s)
    (hfrost : FrostmanBallBound (μ : Measure (Space d)) s C)
    (hnull : ∀ p : Space d, ∀ V : Submodule ℝ (Space d), Module.finrank ℝ V ≤ n →
      (μ : Measure (Space d)) {x | x-p ∈ V} = 0) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1/2 ∧
      ∃ ν : ProbabilityMeasure (Space d), IsCompact (ν : Measure (Space d)).support ∧
        (ν : Measure (Space d)) ≪ (μ : Measure (Space d)) ∧
        ∃ f : TwoProjectionFrame ν (n+1) n ((n:ℝ)-1/2+δ),
          Nonempty (TwoProjectionPieces f ε) := by
  let δ := min (s-((n:ℝ)-1/2)) (1/2) / 3
  have hδ : 0 < δ := div_pos (lt_min (sub_pos.mpr hs) (by norm_num)) (by norm_num)
  have hδbound : δ ≤ (1/2:ℝ)/3 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hδs : 3*δ ≤ s-((n:ℝ)-1/2) := by
    dsimp [δ]
    linarith only [min_le_left (s-((n:ℝ)-1/2)) (1/2)]
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  let u := (n:ℝ)-1/2+δ
  let v := (n:ℝ)-1/2+2*δ
  have hu : 0 < u := by dsimp [u]; linarith
  have huv : u < v := by dsimp [u,v]; linarith
  have hvs : v < s := by dsimp [v]; linarith
  have hv : v < (n+1:ℕ) := by dsimp [v]; push_cast; linarith
  have hun : u < (n:ℝ) := by dsimp [u]; linarith
  obtain ⟨P,Q,ν,hK,hdom,hzero,D,hD,hν,hP,hQ⟩ :=
    choose_two_projected_laws μ hu huv hvs hv hun hfrost hnull
  obtain ⟨f⟩ := normalize_two_projected_laws ν hK P Q hD hν hP hQ hzero
  refine ⟨δ,hδ,by linarith,ν,hK,hdom,f,?_⟩
  exact exists_two_projection_pieces hK f hu hε

end Falconer

end OAI
