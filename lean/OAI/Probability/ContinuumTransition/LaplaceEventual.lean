import OAI.Probability.ContinuumTransition.CoerciveCanonical

namespace OAI

section
open scoped Topology BigOperators
open Filter Set
namespace ContinuumTemperature

theorem laplace_principle_eventual {w : ℝ → ℕ → ℝ} {F : ℝ → ℝ} {b : ℕ → ℝ} {D : ℝ}
    (hw : ∀ L > 0, ∀ n, 0 < w L n) (hsum : ∀ᶠ L in atTop, Summable (w L))
    (hb : Summable b) (hb0 : ∀ n, 0 ≤ b n) (hD : 0 < D) (hF0 : F 0 = 0)
    (hbdd : BddAbove (F '' Ici 0))
    (hlim : ∀ d, 0 ≤ d → Tendsto (fun p : ℝ × ℕ => Real.log (w p.1 p.2)/p.1^3)
      (densityFilter d) (𝓝 (F d)))
    (htail : ∀ᶠ L in atTop, ∀ n : ℕ, D ≤ (n : ℝ)/L^3 → w L n ≤ b n) :
    Tendsto (fun L => Real.log (∑' n, w L n)/L^3) atTop (𝓝 (sSup (F '' Ici 0))) := by
  classical
  let v (L : ℝ) (n : ℕ) := if Summable (w L) then w L n else (Real.exp (-1))^n
  have hvs (L : ℝ) (_ : 0 < L) : Summable (v L) := by
    by_cases hh : Summable (w L)
    · simpa only [v, ite_eq_left hh] using hh
    · simp only [v, ite_eq_right hh]
      exact summable_geometric_of_lt_one (Real.exp_pos _).le (by simp)
  have hv (L : ℝ) (hL : 0 < L) (n : ℕ) : 0 < v L n := by
    dsimp only [v]
    split_ifs
    · exact hw L hL n
    · exact pow_pos (Real.exp_pos _) n
  have hve : ∀ᶠ L in atTop, v L = w L := by
    filter_upwards [hsum] with L hL
    funext n
    exact ite_eq_left hL
  have hvl (d : ℝ) (hd : 0 ≤ d) := (hlim d hd).congr' (by
    filter_upwards [(densityFilter_length d).eventually hve] with p hp
    rw [hp] : (fun p : ℝ × ℕ => Real.log (w p.1 p.2)/p.1^3) =ᶠ[densityFilter d]
      (fun p : ℝ × ℕ => Real.log (v p.1 p.2)/p.1^3))
  have ht : ∀ᶠ L in atTop, ∀ n : ℕ, D ≤ (n : ℝ)/L^3 → v L n ≤ b n := by
    filter_upwards [hve, htail] with L he hh
    simpa only [he] using hh
  have hh := laplace_principle hv hvs hb hb0 hD hF0 hbdd hvl ht
  apply hh.congr'
  filter_upwards [hve] with L hL
  rw [hL]

end ContinuumTemperature
end

end OAI
