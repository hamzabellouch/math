import OAI.Geometry.IsometricImmersion.Calculus.CoordinateJetBounds

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry.CoordinateBound

theorem congr_on {f h : Coord → ℝ} {U : Set Coord} {n : ℕ} {M : ℝ}
    (hU : IsOpen U) (hf : CoordinateBound f U n M) (he : EqOn h f U) :
    CoordinateBound h U n M := by
  intro ds hds p hp
  have hlocal : h =ᶠ[𝓝 p] f := by
    filter_upwards [hU.mem_nhds hp] with x hx
    exact he hx
  rw [(iteratedCoordPartial_eventuallyEq hlocal ds).self_of_nhds]
  exact hf ds hds p hp

theorem mul_through_one {f h : Coord → ℝ} {U : Set Coord} {A B : ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hh : ContDiffOn ℝ ∞ h U) (hU : IsOpen U)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfB : CoordinateBound f U 1 A) (hhB : CoordinateBound h U 1 B) :
    CoordinateBound (fun x => f x * h x) U 1 (2 * A * B) := by
  intro ds hds p hp
  have hab (vs ws : List (Fin 2)) (hv : vs.length ≤ 1) (hw : ws.length ≤ 1) :
      |iteratedCoordPartial vs f p * iteratedCoordPartial ws h p| ≤ A * B := by
    rw [abs_mul]
    exact mul_le_mul (hfB vs hv p hp) (hhB ws hw p hp) (abs_nonneg _) hA
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  cases ds with
  | nil => exact (hab [] [] (by norm_num) (by norm_num)).trans (by nlinarith)
  | cons i ds =>
    cases ds with
    | nil =>
      rw [LowQuotient.product_one hf hh hU hp i]
      exact ((abs_add_le _ _).trans
        (add_le_add (hab [i] [] (by norm_num) (by norm_num))
          (hab [] [i] (by norm_num) (by norm_num)))).trans (le_of_eq (by ring))
    | cons j ds => simp only [List.length_cons] at hds; omega

theorem div_through_one {f h : Coord → ℝ} {U : Set Coord} {A B c : ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hh : ContDiffOn ℝ ∞ h U) (hU : IsOpen U)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 0 < c)
    (hfB : CoordinateBound f U 1 A) (hhB : CoordinateBound h U 1 B)
    (hden : ∀ p ∈ U, c ≤ |h p|) :
    CoordinateBound (fun x => f x / h x) U 1 (A / c + (A + B * (A / c)) / c) := by
  have hne := LowQuotient.denominator_ne_zero hc hden
  have hval (p : Coord) (hp : p ∈ U) : |f p / h p| ≤ A / c :=
    LowQuotient.abs_div_bound hA (hfB [] (by norm_num) p hp) hc (hden p hp)
  have h0 : 0 ≤ A / c := by positivity
  have h1 : 0 ≤ (A + B * (A / c)) / c := by positivity
  intro ds hds p hp
  cases ds with
  | nil => exact (hval p hp).trans (by linarith)
  | cons i ds =>
    cases ds with
    | nil =>
      rw [LowQuotient.quotient_one hf hh hU hp hne i]
      have hprod : |coordPartial i h p * (f p / h p)| ≤ B * (A / c) := by
        rw [abs_mul]
        exact mul_le_mul (hhB [i] (by norm_num) p hp) (hval p hp) (abs_nonneg _) hB
      have hnum := (abs_sub (coordPartial i f p) (coordPartial i h p * (f p / h p))).trans
        (add_le_add (hfB [i] (by norm_num) p hp) hprod)
      exact (LowQuotient.abs_div_bound (by positivity) hnum hc (hden p hp)).trans (by linarith)
    | cons j ds => simp only [List.length_cons] at hds; omega

end SmoothLocal.Geometry.CoordinateBound

end

end OAI
