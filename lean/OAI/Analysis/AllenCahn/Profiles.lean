import OAI.Analysis.AllenCahn.ZeroDefect

namespace OAI

noncomputable section
namespace DeGiorgi
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform
open Filter Topology
open scoped ContDiff
open scoped ENNReal
open MeasureTheory Filter Topology

lemma planar_profile_coordinate_derivative {n : ℕ}
    (e : Space n) (c : ℝ) (j : Fin n) (x : Space n) :
    fderiv ℝ (fun y : Space n => profile (inner ℝ e y - c)) x
      (EuclideanSpace.single j 1) =
      (profileWeight (inner ℝ e x - c) / Real.sqrt 2) * e j := by
  have hi : HasFDerivAt (fun y : Space n => inner ℝ e y - c) (innerSL ℝ e) x :=
    (innerSL ℝ e).hasFDerivAt.sub_const c
  have hp := (profile_hasDerivAt (inner ℝ e x - c)).comp_hasFDerivAt x hi
  simp only [Function.comp_def] at hp
  rw [hp.fderiv]
  simp [EuclideanSpace.inner_single_right]

lemma oriented_profile_of_classified {n : ℕ} {u : Space n → ℝ} (j : Fin n)
    (hi : ∀ x, u x ∈ Set.Ioo (-1 : ℝ) 1)
    (hmon : ∀ x, 0 < fderiv ℝ u x (EuclideanSpace.single j 1))
    (hc : Classified u) :
    ∃ (e : Space n) (c : ℝ), ‖e‖ = 1 ∧ 0 < e j ∧
      ∀ x, u x = profile (inner ℝ e x - c) := by
  rcases hc with h | h | ⟨e, c, he, h⟩
  · have hx := (hi 0).2
    rw [h 0] at hx
    exact (lt_irrefl 1 hx).elim
  · have hx := (hi 0).1
    rw [h 0] at hx
    exact (lt_irrefl (-1 : ℝ) hx).elim
  · refine ⟨e, c, he, ?_, h⟩
    have hp := hmon 0
    rw [funext h, planar_profile_coordinate_derivative] at hp
    exact (mul_pos_iff_of_pos_left
      (div_pos (profileWeight_pos _) (Real.sqrt_pos.mpr (by norm_num)))).mp hp

lemma monotone_profile_of_defect_zero {u : Space 8 → ℝ}
    (hu : ContDiff ℝ 2 u) (hi : ∀ x, u x ∈ Set.Ioo (-1 : ℝ) 1)
    (hAC : AllenCahn u)
    (hmon : ∀ x, 0 < fderiv ℝ u x (EuclideanSpace.single (7 : Fin 8) 1))
    {z : Space 8} (hz : diffuseDefect u z = 0) :
    ∃ (e : Space 8) (c : ℝ), ‖e‖ = 1 ∧ 0 < e 7 ∧
      ∀ x, u x = profile (inner ℝ e x - c) := by
  exact oriented_profile_of_classified 7 hi hmon
    (classified_of_defect_zero_at hu hi hAC hz)

theorem monotone_profile_or_positive_defect {u : Space 8 → ℝ}
    (hu : ContDiff ℝ 2 u) (hi : ∀ x, u x ∈ Set.Ioo (-1 : ℝ) 1)
    (hAC : AllenCahn u)
    (hmon : ∀ x, 0 < fderiv ℝ u x (EuclideanSpace.single (7 : Fin 8) 1)) :
    (∃ (e : Space 8) (c : ℝ), ‖e‖ = 1 ∧ 0 < e 7 ∧
      ∀ x, u x = profile (inner ℝ e x - c)) ∨
    (∀ x, 0 < diffuseDefect u x) := by
  rcases classified_or_positive_defect hu (fun x => ⟨(hi x).1.le, (hi x).2.le⟩)
    hAC with hc | hp
  · exact Or.inl (oriented_profile_of_classified 7 hi hmon hc)
  · exact Or.inr hp.2

lemma strictMono_on_coordinate_lines {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ 2 u) (j : Fin n)
    (hmon : ∀ x, 0 < fderiv ℝ u x (EuclideanSpace.single j 1))
    (x : Space n) :
    StrictMono (fun t : ℝ => u (x + t • EuclideanSpace.single j 1)) := by
  apply strictMono_of_deriv_pos
  intro t
  rw [deriv_line (hu.differentiable (by norm_num))]
  exact hmon _

theorem monotone_line_end_limits {u : Space 8 → ℝ}
    (hu : ContDiff ℝ 2 u) (hi : ∀ x, u x ∈ Set.Ioo (-1 : ℝ) 1)
    (hmon : ∀ x, 0 < fderiv ℝ u x (EuclideanSpace.single (7 : Fin 8) 1))
    (x : Space 8) :
    ∃ a ∈ Set.Icc (-1 : ℝ) 1, ∃ b ∈ Set.Icc (-1 : ℝ) 1,
      Tendsto (fun t : ℝ => u (x + t • EuclideanSpace.single (7 : Fin 8) 1))
        atBot (𝓝 a) ∧
      Tendsto (fun t : ℝ => u (x + t • EuclideanSpace.single (7 : Fin 8) 1))
        atTop (𝓝 b) ∧
      ∀ t : ℝ, a < u (x + t • EuclideanSpace.single (7 : Fin 8) 1) ∧
        u (x + t • EuclideanSpace.single (7 : Fin 8) 1) < b := by
  let f : ℝ → ℝ := fun t => u (x + t • EuclideanSpace.single (7 : Fin 8) 1)
  have hm : StrictMono f := strictMono_on_coordinate_lines hu 7 hmon x
  have hb : BddBelow (Set.range f) := ⟨-1, by
    rintro _ ⟨t, rfl⟩
    exact (hi _).1.le⟩
  have ha : BddAbove (Set.range f) := ⟨1, by
    rintro _ ⟨t, rfl⟩
    exact (hi _).2.le⟩
  refine ⟨⨅ t, f t, ⟨le_ciInf (fun t => (hi _).1.le), ?_⟩,
    ⨆ t, f t, ⟨?_, ciSup_le (fun t => (hi _).2.le)⟩,
    tendsto_atBot_ciInf hm.monotone hb, tendsto_atTop_ciSup hm.monotone ha, ?_⟩
  · exact (ciInf_le hb (0 : ℝ)).trans (hi _).2.le
  · exact (hi _).1.le.trans (le_ciSup ha (0 : ℝ))
  · intro t
    exact ⟨(ciInf_le hb (t - 1)).trans_lt (hm (by linarith)),
      (hm (show t < t + 1 by linarith)).trans_le (le_ciSup ha (t + 1))⟩

end DeGiorgi
end

end OAI
