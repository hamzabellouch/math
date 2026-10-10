import OAI.NumberTheory.DukePrimeDegree.Entropy.NeutralFutureCoordinates
import OAI.NumberTheory.DukePrimeDegree.Geometry.RadialLocalInjectivity

namespace OAI

/-! # Identify small future lifts inside a neutral graph patch -/

noncomputable section
open Matrix Set
namespace DukePrimeDegree
open PrimeDegreePackets

theorem neutral_graph_quotient_lift {n : ℕ} (g₀ : G n)
    (E : Set (NeutralCoordinateBase n))
    (hE : ∀ x ∈ E, ∀ y ∈ E, x.1=y.1 → x.2=y.2)
    (z w : NeutralCoordinateBase n × transverseNeutralSpace n)
    (hz : z.1 ∈ E) (hw : w.1 ∈ E) (r : ℝ)
    (hinj : LocalInjectivityAt r
      (Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (g₀*neutralProductParam n z)))
    (hchart : (neutralProductParam n z)⁻¹*neutralProductParam n w ∈ matrixBall n r)
    (g : G n) (hg : g ∈ matrixBall n r)
    (htri : g.val.IsUpperTriangular) (hpos : ∀ i, 0 < g.val i i)
    (hlift : rightAction
      (Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (g₀*neutralProductParam n z)) g =
      Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (g₀*neutralProductParam n w)) :
    ∃ v : transverseNeutralSpace n, g=diagonalOneParameter v.val v.prop 1 := by
  have haction : rightAction
      (Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (g₀*neutralProductParam n z))
      ((neutralProductParam n z)⁻¹*neutralProductParam n w) =
      Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (g₀*neutralProductParam n w) := by
    change Quotient.mk _ ((g₀*neutralProductParam n z)*
      ((neutralProductParam n z)⁻¹*neutralProductParam n w)) = _
    congr 1
    group
  have he : g=(neutralProductParam n z)⁻¹*neutralProductParam n w :=
    hinj.injOn hg hchart (hlift.trans haction.symm)
  apply neutral_graph_upper_displacement n E hE z w hz hw g htri hpos
  rw [he]
  group

theorem neutral_graph_small_future_lift {n : ℕ}
    (ell : Fin n → ℝ) (hord : StrictMono ell) (g₀ : G n)
    (E : Set (NeutralCoordinateBase n))
    (hE : ∀ x ∈ E, ∀ y ∈ E, x.1=y.1 → x.2=y.2)
    (z w : NeutralCoordinateBase n × transverseNeutralSpace n)
    (hz : z.1 ∈ E) (hw : w.1 ∈ E) (r : ℝ) (hr : r ≤ 1)
    (hinj : LocalInjectivityAt r
      (Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (g₀*neutralProductParam n z)))
    (hchart : (neutralProductParam n z)⁻¹*neutralProductParam n w ∈ matrixBall n r)
    (g : G n) (hg : g ∈ matrixBall n r)
    (hzero : ∀ i j, ell j < ell i → g.val i j=0)
    (hlift : rightAction
      (Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (g₀*neutralProductParam n z)) g =
      Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (g₀*neutralProductParam n w)) :
    ∃ v : transverseNeutralSpace n, g=diagonalOneParameter v.val v.prop 1 := by
  apply neutral_graph_quotient_lift g₀ E hE z w hz hw r hinj hchart g hg
    (fun i j hji => hzero i j (hord hji)) _ hlift
  intro i
  have h := matrixBall_mono hr hg i i
  rw [Matrix.one_apply_eq] at h
  have hh := (abs_lt.mp h).1
  linarith

end DukePrimeDegree

end

end OAI
