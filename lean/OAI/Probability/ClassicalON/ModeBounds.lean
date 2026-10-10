import OAI.Probability.ClassicalON.DyadicSums

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace ClassicalON
namespace LatticeGraph
variable {k : ℕ}

def modeBlockConstant (C : ℝ) : ℝ := Real.sqrt (512*(C^2+C^2*(Real.pi/4)^2))

theorem scaledModes_direction_bound (G : LatticeGraph) (hG : G.WithinDyadicBox k)
    (C : ℝ)
    (hval : ∀ m s z, |squareProfile m s z| ≤ C)
    (hLip : ∀ m s z w, |squareProfile m s w-squareProfile m s z| ≤ C*‖w-z‖)
    (m s j : Bool) :
    SquareBound (fun (e : G.DirectionalEdges j) (p : DyadicFreq k) => G.scaledModeGradient m s p e.val)
      (modeBlockConstant C) := by
  classical
  have hN : (2:ℝ)^k ≠ 0 := by positivity
  have hd (e : G.DirectionalEdges j) :
      ‖(squareProfile m s (scaledSite k e.val.val.2.val):ℂ)-
        (squareProfile m s (scaledSite k e.val.val.1.val):ℂ)‖ ≤ C/(2:ℝ)^k := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    simpa only [G.scaled_edge_distance, div_eq_mul_inv, one_mul] using
      hLip m s (scaledSite k e.val.val.1.val) (scaledSite k e.val.val.2.val)
  have hv (e : G.DirectionalEdges j) :
      ‖(squareProfile m s (scaledSite k e.val.val.2.val):ℂ)‖ ≤ C := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hval m s (scaledSite k e.val.val.2.val)
  have ha (p : DyadicFreq k) : ‖((1/(dyadicRadius p:ℝ)):ℂ)‖ ≤ 1 := by
    have hp : (1:ℝ) ≤ dyadicRadius p := by exact_mod_cast dyadicRadius_pos p
    simp only [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ dyadicRadius p)]
    exact (div_le_one (by positivity)).mpr hp
  have hh := edge_cutoff_squareBound (groupedTorusPoint m s) (groupedTorusPoint_injective m s)
    (fun e : G.DirectionalEdges j => latticeTorus (16*2^k) e.val.val.1.val)
    (G.directional_torus_injective k hG j) (latticeTorus (16*2^k) (latticeAxis j))
    (fun e => (squareProfile m s (scaledSite k e.val.val.1.val):ℂ))
    (fun e => (squareProfile m s (scaledSite k e.val.val.2.val):ℂ))
    (fun p => ((1/(dyadicRadius p:ℝ)):ℂ)) (C/(2:ℝ)^k) C 1 (Real.pi/(4*(2:ℝ)^k))
    hd hv ha (groupedWave_multiplier_bound m s j)
  have hc : Real.sqrt (2*((16*2^k:ℕ):ℝ)^2*((C/(2:ℝ)^k)^2*1^2+C^2*(Real.pi/(4*(2:ℝ)^k))^2)) = modeBlockConstant C := by
    congr 1
    push_cast
    field_simp [hN]
    ring
  rw [hc] at hh
  have hdir (e : G.DirectionalEdges j) : G.edgeDirection e.val=j := e.property
  exact fun v => by simpa only [G.scaledModeGradient_formula, hdir] using hh v

theorem scaledModes_squareBound (G : LatticeGraph) (hG : G.WithinDyadicBox k)
    (C : ℝ)
    (hval : ∀ m s z, |squareProfile m s z| ≤ C)
    (hLip : ∀ m s z w, |squareProfile m s w-squareProfile m s z| ≤ C*‖w-z‖)
    (m s : Bool) :
    SquareBound (fun e (p : DyadicFreq k) => G.scaledModeGradient m s p e) (2*modeBlockConstant C) := by
  apply SquareBound.combine_directions _ G.edgeDirection
  exact fun j => G.scaledModes_direction_bound hG C hval hLip m s j

end LatticeGraph
end ClassicalON

end

end OAI
