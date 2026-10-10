import OAI.Probability.ClassicalON.ModeCosts

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace ClassicalON
variable {k : ℕ}

theorem dyadic_sine_main_sum (k : ℕ) :
    (∑ p : DyadicFreq k, (dyadicWeight p)^2*Real.sin (dyadicAngle k (dyadicPoint p).1)) =
      dyadicLambda k/(2:ℝ)^k := by
  simp only [dyadicWeight_sq, dyadicLambda]
  rw [mul_div_cancel_left₀ _ (by positivity : (2:ℝ)^k ≠ 0)]

theorem grouped_sine_sum (m s j : Bool) :
    (∑ p : DyadicFreq k, (dyadicWeight p)^2*
      Real.sin (dyadicAngle k (if j then (groupedPoint m s p).2 else (groupedPoint m s p).1))) =
      if m=j then (if s then -(dyadicLambda k/(2:ℝ)^k) else dyadicLambda k/(2:ℝ)^k) else 0 := by
  have h1 := dyadic_sine_main_sum k
  have h2 := dyadic_sin_cancel k
  cases m <;> cases s <;> cases j <;>
    simp_all [groupedPoint]

namespace LatticeGraph

def modeCommutator (G : LatticeGraph) (m s : Bool) (p : DyadicFreq k) (e : G.edges) : ℂ :=
  (latticeMode m s p e.val.1.val*conj (latticeMode m s p e.val.2.val)-
    conj (latticeMode m s p e.val.1.val)*latticeMode m s p e.val.2.val)/2

def profileEdge (G : LatticeGraph) (k : ℕ) (e : G.edges) : ℝ :=
  (1/(2:ℝ)^k)*(squareProfile (G.edgeDirection e) false (scaledSite k e.val.1.val)*
    squareProfile (G.edgeDirection e) false (scaledSite k e.val.2.val)-
    squareProfile (G.edgeDirection e) true (scaledSite k e.val.1.val)*
    squareProfile (G.edgeDirection e) true (scaledSite k e.val.2.val))

def thetaEdge (G : LatticeGraph) (k : ℕ) (e : G.edges) : ℝ :=
  squareTheta (scaledSite k e.val.2.val)-squareTheta (scaledSite k e.val.1.val)

theorem modeCommutator_formula (G : LatticeGraph) (m s : Bool) (p : DyadicFreq k) (e : G.edges) :
    G.modeCommutator m s p e = -Complex.I *
      ((squareProfile m s (scaledSite k e.val.1.val)*squareProfile m s (scaledSite k e.val.2.val)*
        ((dyadicWeight p)^2*Real.sin (dyadicAngle k
          (if G.edgeDirection e then (groupedPoint m s p).2 else (groupedPoint m s p).1))):ℝ):ℂ) := by
  have hy : latticeMode m s p e.val.2.val =
      (((dyadicWeight p*squareProfile m s (scaledSite k e.val.2.val)):ℝ):ℂ)*
        torusWave (groupedTorusPoint m s p) (latticeTorus (16*2^k) e.val.1.val)*
        Complex.exp (Complex.I*((dyadicAngle k
          (if G.edgeDirection e then (groupedPoint m s p).2 else (groupedPoint m s p).1):ℝ):ℂ)) := by
    unfold latticeMode
    rw [show latticeTorus (16*2^k) e.val.2.val = latticeTorus (16*2^k) e.val.1.val+
      latticeTorus (16*2^k) (latticeAxis (G.edgeDirection e)) by rw [G.edge_step e,latticeTorus_add],
      torusWave_add, groupedWave_axis_sine]
    push_cast
    ring
  have hh := wave_commutator (dyadicWeight p)
    (squareProfile m s (scaledSite k e.val.1.val)) (squareProfile m s (scaledSite k e.val.2.val))
    (dyadicAngle k (if G.edgeDirection e then (groupedPoint m s p).2 else (groupedPoint m s p).1))
    (torusWave (groupedTorusPoint m s p) (latticeTorus (16*2^k) e.val.1.val))
    (torusWave_norm _ _)
  unfold modeCommutator
  rw [hy]
  simp only [latticeMode, Complex.ofReal_mul] at hh ⊢
  linear_combination hh

theorem mode_group_commutator (G : LatticeGraph) (m s : Bool) (e : G.edges) :
    (∑ p : DyadicFreq k, G.modeCommutator m s p e) = -Complex.I*
      ((squareProfile m s (scaledSite k e.val.1.val)*squareProfile m s (scaledSite k e.val.2.val)*
        (if m=G.edgeDirection e then (if s then -(dyadicLambda k/(2:ℝ)^k) else dyadicLambda k/(2:ℝ)^k) else 0):ℝ):ℂ) := by
  simp only [G.modeCommutator_formula, ← Finset.mul_sum, ← Complex.ofReal_sum]
  rw [grouped_sine_sum]

theorem modes_commutator (G : LatticeGraph) (e : G.edges) :
    (∑ i : ModeIndex k, G.modeCommutator i.1.1 i.1.2 i.2 e) =
      -Complex.I*((dyadicLambda k*G.profileEdge k e:ℝ):ℂ) := by
  simp only [Fintype.sum_prod_type, G.mode_group_commutator, Fintype.sum_bool]
  cases h : G.edgeDirection e <;>
    simp [profileEdge, h]
  all_goals ring

end LatticeGraph
end ClassicalON

end

end OAI
