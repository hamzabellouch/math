import OAI.NumberTheory.DukePrimeDegree.Geometry.QuantitativeQuotientCover
import OAI.NumberTheory.DukePrimeDegree.Geometry.SmallMatrixLength

namespace OAI

/-! # Quantitative distance nets on logarithmic quotient balls

Finite matrix grids give nets for the intrinsic quotient distance. In
the other direction a small quotient distance gives a small actual
right lift, which is what the future-fiber construction needs.
-/

noncomputable section
open Set
open scoped Topology Matrix.Norms.Operator
namespace DukePrimeDegree
open PrimeDegreePackets

def quotientNetBound (n : ℕ) (R s : ℝ) : ℝ :=
  (2*Real.exp (R+1)+2)^(n*n) /
    (min 1 ((s/(12*(n:ℝ)))/(4*(n:ℝ)*Real.exp (R+1))))^(n*n)

theorem exists_quantitative_distance_net {n : ℕ} (hn : 0 < n)
    (R s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) :
    ∃ (N : ℕ) (z : Fin N → X n), (N:ℝ) ≤ quotientNetBound n R s ∧
      ∀ x, quotientLogDistance (Quotient.mk _ (1 : G n)) x ≤ R →
        ∃ i, quotientLogDistance (z i) x < s := by
  classical
  let r := s/(12*(n:ℝ))
  have hnp : 0 < (n:ℝ) := by exact_mod_cast hn
  have hr : 0 < r := by dsimp [r]; positivity
  have hnr : (n:ℝ)*r=s/12 := by dsimp [r]; field_simp
  have h3nr : 3*(n:ℝ)*r=s/4 := by nlinarith [hnr]
  have hsmall : (n:ℝ)*r ≤ 1/2 := by rw [hnr]; linarith
  obtain ⟨N,V,hN,hopen,hcover,hrel⟩ := exists_quantitative_quotient_cover hn R r hr
  let z (i : Fin N) : X n :=
    if h : (V i).Nonempty then h.choose else Quotient.mk _ (1 : G n)
  refine ⟨N,z,?_,?_⟩
  · exact hN
  · intro x hx
    obtain ⟨i,hxi⟩ := mem_iUnion.mp (hcover hx)
    have hne : (V i).Nonempty := ⟨x,hxi⟩
    have hzi : z i ∈ V i := by
      simp only [z,dite_eq_left hne]
      exact hne.choose_spec
    obtain ⟨g,hg,hgx⟩ := hrel i (z i) hzi x hxi
    refine ⟨i,?_⟩
    have H := (quotientLogDistance_le_length (z i) x g hgx).trans
      (matrixLogLength_le_three_card_radius hn hr.le hsmall hg)
    rw [h3nr] at H
    linarith

theorem exists_matrix_lift_of_logDistance_lt {n : ℕ}
    {r : ℝ} (hr : 0 < r) {x y : X n}
    (hxy : quotientLogDistance x y < Real.log (1+r)) :
    ∃ g ∈ matrixBall n r, rightAction x g=y := by
  obtain ⟨g,hg,hlen⟩ := exists_rightAction_length_lt x y (sub_pos.mpr hxy)
  have hnorm : ‖g.val-1‖ < r := norm_sub_one_lt_of_matrixLogLength_lt g hr (by linarith)
  refine ⟨g,?_,hg⟩
  intro i j
  exact (matrix_entry_abs_le_operator_norm (g.val-1) i j).trans_lt hnorm

end DukePrimeDegree

end

end OAI
