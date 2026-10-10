import OAI.MeasureTheory.Falconer.Shells.ActualHighShellInverse

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
namespace PositiveDistanceData

theorem uniform_weighted_high_shell_inverse {sig T : ℝ} (hsig : 0 < sig) :
    ∃ n N₀ : ℕ, ∀ d : PositiveDistanceData, N₀ ≤ d.N → d.sig = sig →
    0 < d.Q.side → d.StronglySeparated → 0 < d.q →
    d.sig*d.N ≤ (d.q:ℝ) → d.a+100*d.q < d.t → d.t ≤ d.N →
    ∀ v r : ℝ, (d.t:ℝ)-d.sig*d.N ≤ v → (2:ℝ)^(v-1) ≤ r →
    ∀ x ∈ (d.Q.descendant d.X).carrier, ∀ y ∈ (d.Q.descendant d.Y).carrier,
    ‖(d.spatialWeight (x,y):ℂ)*Complex.exp (Complex.I*((r*dist x y:ℝ):ℂ)) -
      (((dist x y/(2:ℝ)^(-(d.a:ℝ)))^(-(1/2:ℝ)):ℝ):ℂ) *
      sourceInverseCircleIntegral n r (x-y)
        (sourceConeCircle (sourceParentAxis (d.Q.descendant d.X) (d.Q.descendant d.Y)))
        (d.pairMaskSymbol (x,y))‖ ≤ ((2:ℝ)^d.N)^(-T) := by
  obtain ⟨n,N₀,h₀⟩ := uniform_actual_high_shell_inverse (T := T) hsig
  refine ⟨n,N₀,?_⟩
  intro d hN hd hQ hs hq hqs hw ht v r hv hr x hx y hy
  have hb := h₀ d hN hd hQ hs hq hqs hw ht v r hv hr x hx y hy
  have hratio := d.separated_distance_ratio hQ hs (z := (x,y)) hx hy
  let w := (dist x y/(2:ℝ)^(-(d.a:ℝ)))^(-(1/2:ℝ))
  have hw0 : 0 ≤ w := Real.rpow_nonneg (by positivity) _
  have hw1 : w ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith :
    1 ≤ dist x y/(2:ℝ)^(-(d.a:ℝ))) (by norm_num)
  have he : (d.spatialWeight (x,y):ℂ)*Complex.exp (Complex.I*((r*dist x y:ℝ):ℂ)) -
      (w:ℂ)*sourceInverseCircleIntegral n r (x-y)
        (sourceConeCircle (sourceParentAxis (d.Q.descendant d.X) (d.Q.descendant d.Y)))
        (d.pairMaskSymbol (x,y)) =
      (w:ℂ)*(Complex.exp (Complex.I*((r*dist x y:ℝ):ℂ))*(d.minimalMask (x,y):ℂ) -
        sourceInverseCircleIntegral n r (x-y)
          (sourceConeCircle (sourceParentAxis (d.Q.descendant d.X) (d.Q.descendant d.Y)))
          (d.pairMaskSymbol (x,y))) := by
    simp only [spatialWeight,Complex.ofReal_mul]
    dsimp [w]
    ring
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hw0]
  exact (mul_le_mul_of_nonneg_left hb hw0).trans
    (by simpa using mul_le_mul_of_nonneg_right hw1 (by positivity : 0 ≤ ((2:ℝ)^d.N)^(-T)))

end PositiveDistanceData

end PlanarFalconer

end OAI
