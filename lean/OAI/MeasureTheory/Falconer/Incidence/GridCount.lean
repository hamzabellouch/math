import OAI.MeasureTheory.Falconer.Graphs.AllDimensionalGraphGeometry
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Interval

namespace OAI

/-!
# Candidate grid counts in any ambient dimension

The remaining unknown cell in a retained graph edge is confined to a small
ball. Its integer coordinate labels therefore lie in a product of short
integer intervals. This gives the dimension-dependent degree factor.
-/

namespace Falconer

/-- Grid centers with mesh `s⁻¹`. A common fixed translation cancels in all
pair differences and so does not enter the counting argument. -/
noncomputable def scaledGridPoint {d : ℕ} (s : ℝ) (z : Fin d → ℤ) : Space d :=
  WithLp.toLp 2 (fun i => (z i : ℝ) / s)

@[simp] theorem scaledGridPoint_apply {d : ℕ} (s : ℝ) (z : Fin d → ℤ) (i : Fin d) :
    scaledGridPoint s z i = (z i : ℝ) / s := rfl

/-- Euclidean distance bounds every integer coordinate difference. -/
theorem grid_coordinate_bound {d L : ℕ} {s r : ℝ} (hs : 0 < s)
    (hL : r * s ≤ L) {z w : Fin d → ℤ}
    (hz : ‖scaledGridPoint s z - scaledGridPoint s w‖ ≤ r) (i : Fin d) :
    |z i - w i| ≤ (L : ℤ) := by
  have hi := (PiLp.norm_apply_le (scaledGridPoint s z - scaledGridPoint s w) i).trans hz
  change |(z i : ℝ) / s - (w i : ℝ) / s| ≤ r at hi
  rw [← sub_div, abs_div, abs_of_pos hs] at hi
  have hb : |(z i : ℝ) - (w i : ℝ)| ≤ (L : ℝ) :=
    ((div_le_iff₀ hs).mp hi).trans hL
  exact_mod_cast hb

/-- A finite family in a coordinate box has at most `(2L+1)^d` labels. -/
theorem grid_box_card {d L : ℕ} (S : Finset (Fin d → ℤ)) (w : Fin d → ℤ)
    (hS : ∀ z ∈ S, ∀ i, |z i - w i| ≤ (L : ℤ)) :
    S.card ≤ (2 * L + 1)^d := by
  classical
  let shift : (Fin d → ℤ) → (Fin d → ℤ) := fun z i => z i - w i
  have hi : Function.Injective shift := by
    intro u v huv
    funext i
    have hi := congrFun huv i
    dsimp [shift] at hi
    omega
  have hsub : S.image shift ⊆
      Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(L : ℤ)) (L : ℤ)) := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
    apply Fintype.mem_piFinset.mpr
    intro i
    exact Finset.mem_Icc.mpr (abs_le.mp (hS u hu i))
  have hcard : (Finset.Icc (-(L : ℤ)) (L : ℤ)).card = 2 * L + 1 := by
    rw [Int.card_Icc]
    omega
  calc
    S.card = (S.image shift).card := (Finset.card_image_of_injective S hi).symm
    _ ≤ (Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(L : ℤ)) (L : ℤ))).card :=
      Finset.card_le_card hsub
    _ = (2 * L + 1)^d := by simp [Fintype.card_piFinset, hcard]

/-- Ball count at a chosen grid center, with explicit integer radius. -/
theorem grid_ball_card {d L : ℕ} {s r : ℝ} (hs : 0 < s) (hL : r * s ≤ L)
    (S : Finset (Fin d → ℤ)) (w : Fin d → ℤ)
    (hS : ∀ z ∈ S, ‖scaledGridPoint s z - scaledGridPoint s w‖ ≤ r) :
    S.card ≤ (2 * L + 1)^d :=
  grid_box_card S w (fun z hz i => grid_coordinate_bound hs hL (hS z hz) i)

/-- In the retained graph, the scalar and perpendicular tests give exactly
this grid count. No transversality condition between cap directions is used. -/
theorem retained_grid_card {d L : ℕ} {s τ c : ℝ} (hs : 0 < s) (hL : 4 * τ * s ≤ L)
    (S : Finset (Fin d → ℤ)) (w : Space d) (hw : ‖w‖ = 1)
    (hlong : ∀ z ∈ S, |inner ℝ w (scaledGridPoint s z) - c| ≤ τ)
    (hperp : ∀ z ∈ S, ‖perpendicularPart w (scaledGridPoint s z)‖ ≤ τ) :
    S.card ≤ (2 * L + 1)^d := by
  classical
  by_cases hne : S.Nonempty
  · obtain ⟨z₀, hz₀⟩ := hne
    apply grid_ball_card hs hL S z₀
    intro z hz
    exact retained_candidates_diameter hw (hlong z hz) (hlong z₀ hz₀)
      (hperp z hz) (hperp z₀ hz₀)
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
    exact Nat.zero_le _

/-- The same count with an arbitrary common origin for the displacement
tests. The grid itself need not be centered at the origin of the tube. -/
theorem retained_grid_card_translated {d L : ℕ} {s τ c : ℝ}
    (hs : 0 < s) (hL : 4 * τ * s ≤ L)
    (S : Finset (Fin d → ℤ)) (w u : Space d) (hw : ‖w‖ = 1)
    (hlong : ∀ z ∈ S, |inner ℝ w (scaledGridPoint s z - u) - c| ≤ τ)
    (hperp : ∀ z ∈ S, ‖perpendicularPart w (scaledGridPoint s z - u)‖ ≤ τ) :
    S.card ≤ (2 * L + 1)^d := by
  classical
  by_cases hne : S.Nonempty
  · obtain ⟨z₀, hz₀⟩ := hne
    apply grid_ball_card hs hL S z₀
    intro z hz
    have hh := retained_candidates_diameter hw (hlong z hz) (hlong z₀ hz₀)
      (hperp z hz) (hperp z₀ hz₀)
    simpa only [sub_sub_sub_cancel_right] using hh
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
    exact Nat.zero_le _

end Falconer

end OAI
