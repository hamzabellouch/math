import OAI.Probability.ClassicalON.SquareEstimates

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace ClassicalON

variable {k : ℕ}

def latticeMode (m s : Bool) (p : DyadicFreq k) (x : Site) : ℂ :=
  (dyadicWeight p:ℂ) * (squareProfile m s (scaledSite k x):ℂ) *
    torusWave (groupedTorusPoint m s p) (latticeTorus (16*2^k) x)

theorem groupedPoint_abs_bound (m s : Bool) (p : DyadicFreq k) :
    |(groupedPoint m s p).1| ≤ 2*(dyadicRadius p:ℤ) ∧
    |(groupedPoint m s p).2| ≤ 2*(dyadicRadius p:ℤ) := by
  have hp := dyadicPoint_bounds p
  have hr : (0:ℤ)<dyadicRadius p := by exact_mod_cast dyadicRadius_pos p
  have h1 : |(dyadicPoint p).1| ≤ 2*(dyadicRadius p:ℤ) := abs_le.mpr (by constructor <;> omega)
  have h2 : |(dyadicPoint p).2| ≤ 2*(dyadicRadius p:ℤ) := abs_le.mpr (by constructor <;> omega)
  cases m <;> cases s
  · simpa [groupedPoint] using And.intro h1 h2
  · simpa [groupedPoint] using And.intro h1 h2
  · simpa [groupedPoint] using And.intro h2 h1
  · simpa [groupedPoint] using And.intro h2 h1

theorem groupedWave_axis (m s j : Bool) (p : DyadicFreq k) :
    torusWave (groupedTorusPoint m s p) (latticeTorus (16*2^k) (latticeAxis j)) =
      ZMod.stdAddChar ((if j then (groupedPoint m s p).2 else (groupedPoint m s p).1):ZMod (16*2^k)) := by
  cases j <;> simp [torusWave, groupedTorusPoint, latticeTorus, latticeAxis]

theorem groupedWave_axis_sine (m s j : Bool) (p : DyadicFreq k) :
    torusWave (groupedTorusPoint m s p) (latticeTorus (16*2^k) (latticeAxis j)) =
      Complex.exp (Complex.I*((dyadicAngle k ((if j then (groupedPoint m s p).2 else (groupedPoint m s p).1):ℤ):ℝ):ℂ)) := by
  rw [groupedWave_axis]
  cases j <;> simp only [Bool.false_eq_true, ↓reduceIte]
  all_goals
    rw [ZMod.stdAddChar_coe]
    congr 1
    unfold dyadicAngle
    push_cast
    ring

theorem groupedWave_multiplier_bound (m s j : Bool) (p : DyadicFreq k) :
    ‖((1/(dyadicRadius p:ℝ)):ℂ) *
      (torusWave (groupedTorusPoint m s p) (latticeTorus (16*2^k) (latticeAxis j))-1)‖ ≤
        Real.pi/(4*(2:ℝ)^k) := by
  have hr : (0:ℝ)<dyadicRadius p := by exact_mod_cast dyadicRadius_pos p
  have hp : |((if j then (groupedPoint m s p).2 else (groupedPoint m s p).1):ℤ)| ≤
      2*(dyadicRadius p:ℤ) := by
    cases j
    · exact (groupedPoint_abs_bound m s p).1
    · exact (groupedPoint_abs_bound m s p).2
  have hp' : |(((if j then (groupedPoint m s p).2 else (groupedPoint m s p).1):ℤ):ℝ)| ≤ 2*(dyadicRadius p:ℝ) := by exact_mod_cast hp
  simp only [norm_mul, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  rw [groupedWave_axis]
  have hchar : ‖ZMod.stdAddChar (if j then ((groupedPoint m s p).2:ZMod (16*2^k)) else ((groupedPoint m s p).1:ZMod (16*2^k)))-1‖ ≤
      (2*Real.pi/(16*2^k:ℕ))*|(((if j then (groupedPoint m s p).2 else (groupedPoint m s p).1):ℤ):ℝ)| := by
    cases j <;> exact norm_stdAddChar_intCast_sub_one (L := 16*2^k) _
  calc _ ≤ (1/(dyadicRadius p:ℝ))*((2*Real.pi/(16*2^k:ℕ))*|(((if j then (groupedPoint m s p).2 else (groupedPoint m s p).1):ℤ):ℝ)|) :=
          mul_le_mul_of_nonneg_left hchar (by positivity)
       _ ≤ (1/(dyadicRadius p:ℝ))*((2*Real.pi/(16*2^k:ℕ))*(2*(dyadicRadius p:ℝ))) := by gcongr
       _ = Real.pi/(4*(2:ℝ)^k) := by push_cast; field_simp [ne_of_gt hr]; ring

theorem latticeMode_norm_bound (m s : Bool) (p : DyadicFreq k) (x : Site) (C : ℝ)
    (hC : |squareProfile m s (scaledSite k x)| ≤ C) : ‖latticeMode m s p x‖ ≤ dyadicWeight p*C := by
  simp only [latticeMode, norm_mul, torusWave_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos (dyadicWeight_pos p)]
  exact mul_le_mul_of_nonneg_left hC (dyadicWeight_pos p).le

namespace LatticeGraph

def modeGradient (G : LatticeGraph) (m s : Bool) (p : DyadicFreq k) (e : G.edges) : ℂ :=
  latticeMode m s p e.val.2.val-latticeMode m s p e.val.1.val

def scaledModeGradient (G : LatticeGraph) (m s : Bool) (p : DyadicFreq k) (e : G.edges) : ℂ :=
  (Real.sqrt (dyadicRadius p:ℝ):ℂ)*G.modeGradient m s p e

theorem scaledModeGradient_formula (G : LatticeGraph) (m s : Bool) (p : DyadicFreq k) (e : G.edges) :
    G.scaledModeGradient m s p e =
      ((1/(dyadicRadius p:ℝ)):ℂ) *
      ((squareProfile m s (scaledSite k e.val.2.val):ℂ)*torusWave (groupedTorusPoint m s p)
        (latticeTorus (16*2^k) e.val.1.val+latticeTorus (16*2^k) (latticeAxis (G.edgeDirection e))) -
       (squareProfile m s (scaledSite k e.val.1.val):ℂ)*torusWave (groupedTorusPoint m s p)
        (latticeTorus (16*2^k) e.val.1.val)) := by
  have h := congrArg Complex.ofReal (dyadicWeight_mul_sqrt p)
  push_cast at h
  simp only [scaledModeGradient, modeGradient, latticeMode]
  rw [G.edge_step e, latticeTorus_add]
  linear_combination ( ((squareProfile m s (scaledSite k (e.val.1.val+latticeAxis (G.edgeDirection e))):ℂ)*
    torusWave (groupedTorusPoint m s p) (latticeTorus (16*2^k) e.val.1.val+latticeTorus (16*2^k) (latticeAxis (G.edgeDirection e)))) -
    ((squareProfile m s (scaledSite k e.val.1.val):ℂ)*torusWave (groupedTorusPoint m s p) (latticeTorus (16*2^k) e.val.1.val)) ) * h

end LatticeGraph
end ClassicalON

end

end OAI
