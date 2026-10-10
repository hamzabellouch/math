import OAI.NumberTheory.DukePrimeDegree.Geometry.SeparatedQuotientNet
import OAI.NumberTheory.DukePrimeDegree.Geometry.DyadicBoundaryCuts

namespace OAI

/-! # Separated quotient observations with controlled distance boundaries

Each logarithmic ball admits finitely many distance cuts that cover it,
have small relative lifts, and satisfy a common dyadic boundary estimate.
Both the number of cuts and their boundary constants are explicit.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_separated_controlled_distance_cuts {n : ℕ} (hn : 0 < n)
    (μ : Measure (X n)) [IsProbabilityMeasure μ]
    (R r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    let τ := Real.log (1+r)
    ∃ (N : ℕ) (z : Fin N → X n) (c : Fin N → ℝ),
      (N:ℝ) ≤ quotientNetBound n R (τ/8) ∧
      (∀ i j, i ≠ j → τ/8 < quotientLogDistance (z i) (z j)) ∧
      (∀ i, τ/3 < c i ∧ c i < τ/2 ∧
        μ {x | quotientLogDistance (z i) x=c i}=0 ∧
        ∀ k : ℕ, μ (realBoundaryStrip (quotientLogDistance (z i)) (c i) ((1/4:ℝ)^k)) ≤
          ENNReal.ofReal (48/τ*(1/2:ℝ)^k)) ∧
      (∀ x, quotientLogDistance (Quotient.mk _ (1 : G n)) x ≤ R →
        ∃ i, quotientLogDistance (z i) x < c i) ∧
      ∀ i, ∀ x, quotientLogDistance (z i) x < c i →
        ∀ y, quotientLogDistance (z i) y < c i →
        ∃ g ∈ matrixBall n r, rightAction x g=y := by
  classical
  let τ := Real.log (1+r)
  have hτ : 0 < τ := Real.log_pos (by linarith)
  have hτr : τ ≤ r := by
    have H := Real.log_le_sub_one_of_pos (show 0 < 1+r by linarith)
    dsimp [τ]
    linarith
  obtain ⟨N,z,hN,hsep,hcover⟩ := exists_separated_quantitative_distance_net hn R (τ/4)
    (by positivity) (by linarith)
  have hex (i : Fin N) := exists_dyadic_boundary_cut μ
    (continuous_quotientLogDistance n (z i)).measurable
    (show τ/3 < τ/2 by linarith)
  choose c hc hnull hboundary using hex
  have hN' : (N:ℝ) ≤ quotientNetBound n R (τ/8) := by
    have he : τ/4/2=τ/8 := by ring
    simpa only [he] using hN
  have hsep' : ∀ i j, i ≠ j → τ/8 < quotientLogDistance (z i) (z j) := by
    intro i j hij
    have he : τ/4/2=τ/8 := by ring
    simpa only [he] using hsep i j hij
  refine ⟨N,z,c,hN',hsep',?_,?_,?_⟩
  · intro i
    refine ⟨(hc i).1,(hc i).2,hnull i,?_⟩
    intro k
    convert hboundary i k using 1
    congr 1
    change 48/τ*(1/2:ℝ)^k = 8/(τ/2-τ/3)*(1/2:ℝ)^k
    have hne := hτ.ne'
    field_simp [hne]
    ring
  · intro x hx
    obtain ⟨i,hi⟩ := hcover x hx
    exact ⟨i,hi.trans (by linarith [(hc i).1])⟩
  · intro i x hx y hy
    apply exists_matrix_lift_of_logDistance_lt hr
    have H := quotientLogDistance_triangle x (z i) y
    rw [quotientLogDistance_symm x (z i)] at H
    change quotientLogDistance x y < τ
    linarith [(hc i).2]

end DukePrimeDegree

end

end OAI
