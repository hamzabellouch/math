import OAI.Probability.InvariantIsing.Fields.FieldHeightFinalOrder
import OAI.Probability.InvariantIsing.Fields.FieldHeightRadialHessian
import OAI.Probability.InvariantIsing.Fields.FieldFiniteSupport

namespace OAI

/-! Actual mixed-coordinate and quadratic-form signs of the finite
scalar Ising height Hessian. The mixed and radial derivative estimates imply the Hessian sign. -/

noncomputable section
open IsingPerceptron Set
open scoped BigOperators Topology

namespace InvariantIsing

lemma fieldHeight_hessian_nonneg_of_coordinate_order (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (hI : IsOpen I)
    (F : FieldFiniteFamily (h.depth + 1) I)
    (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h)) (hr : h.height ∈ I)
    (i j : Fin (h.depth + 1)) {J : Set ℝ} (hJ : IsOpen J) (h0 : (0 : ℝ) ∈ J)
    (hadm : ∀ t ∈ J, Function.update h.height j (h.height j + t) ∈ fieldStrictHeightCone h.depth)
    (horder : ∀ t (ht : t ∈ J) s (hs : s ∈ J), t ≤ s →
      fieldMagnetizationLevel (fieldStepOfStrictHeights h
        (Function.update h.height j (h.height j + s)) (hadm s hs)) i ≤
      fieldMagnetizationLevel (fieldStepOfStrictHeights h
        (Function.update h.height j (h.height j + t)) (hadm t ht)) i) :
    0 ≤ F.PP i j (h.height, 0) := by
  let q := fun t : ℝ => Function.update h.height j (h.height j + t)
  let K := J ∩ q ⁻¹' I
  have hq : Continuous q := by
    apply continuous_pi
    intro k
    by_cases hkj : k = j
    · subst k
      simp only [q, Function.update_self]
      fun_prop
    · simpa only [q, Function.update_of_ne hkj] using continuous_const
  have hK : IsOpen K := hJ.inter (hI.preimage hq)
  have h0K : (0 : ℝ) ∈ K := by simpa [K, q] using And.intro h0 hr
  have hm : MonotoneOn (fun t => F.P i (q t, 0)) K := by
    intro a ha b hb hab
    have hga := fieldHeight_gradient_identification h F hU (q a) ha.2 (hadm a ha.1) i
    have hgb := fieldHeight_gradient_identification h F hU (q b) hb.2 (hadm b hb.1) i
    have hord := horder a ha.1 b hb.1 hab
    have hw : 0 ≤ h.cut i.succ - h.cut i.castSucc :=
      sub_nonneg.mpr (h.ordered_cut.monotone i.castSucc_le_succ)
    have hm := mul_le_mul_of_nonpos_left hord (show -(h.cut i.succ - h.cut i.castSucc) / 2 ≤ 0 by linarith)
    linarith
  have hd := F.coordinate_gradient_derivative h.height 0 hr i j
  have hn := hm.derivWithin_nonneg (x := 0)
  rw [hd.hasDerivWithinAt.derivWithin (hK.uniqueDiffWithinAt h0K)] at hn
  exact hn

theorem fieldHeight_hessian_mixed_nonneg (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (hI : IsOpen I)
    (F : FieldFiniteFamily (h.depth + 1) I)
    (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h)) (hr : h.height ∈ I)
    (hstrict : ∀ k, 0 < (fieldIncrement h k).2)
    (i j : Fin (h.depth + 1)) (hij : i < j) : 0 ≤ F.PP i j (h.height, 0) := by
  revert hij
  refine Fin.lastCases ?_ (fun j => ?_) j
  · intro hij
    apply fieldHeight_hessian_nonneg_of_coordinate_order h hI F hU hr i (Fin.last h.depth)
      isOpen_Ioi (show (0 : ℝ) ∈ Ioi (-(fieldIncrement h (Fin.last h.depth)).2) by
        have hh := hstrict (Fin.last h.depth)
        change -(fieldIncrement h (Fin.last h.depth)).2 < 0
        linarith)
      (fun t ht => fieldHeight_update_final_mem h hstrict t ht)
    intro t ht s hs hts
    exact fieldHeight_final_earlier_antitone h hstrict i hij ht hs hts
  · intro hij
    have hj : 0 < j.val := by change i.val < j.val at hij; omega
    apply fieldHeight_hessian_nonneg_of_coordinate_order h hI F hU hr i j.castSucc
      isOpen_Ioo (show (0 : ℝ) ∈ Ioo (-(fieldIncrement h j.castSucc).2)
        (fieldIncrement h j.succ).2 by
          have ha := hstrict j.castSucc
          have hb := hstrict j.succ
          constructor <;> linarith)
      (fun t ht => fieldHeight_update_interior_mem h hstrict j t ht)
    intro t ht s hs hts
    exact fieldHeight_interior_earlier_antitone h hstrict j hj i hij ht hs hts

theorem fieldHeight_hessian_nonpos (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (hI : IsOpen I)
    (F : FieldFiniteFamily (h.depth + 1) I)
    (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h))
    (r : Fin (h.depth + 1) → ℝ) (hr : r ∈ I)
    (hs : r ∈ fieldStrictHeightCone h.depth) (x : Fin (h.depth + 1) → ℝ) :
    ∑ i, ∑ j, F.PP i j (r, 0) * x i * x j ≤ 0 := by
  let k := fieldStepOfStrictHeights h r hs
  have hk : ∀ j, 0 < (fieldIncrement k j).2 := fun j => hs j
  have hpos : ∀ i, 0 < r i := by
    intro i
    have h0 : 0 < r 0 := by simpa [fieldHeightIncrement] using hs 0
    exact h0.trans_le ((fieldStrictHeightCone_strictMono hs).monotone (Fin.zero_le i))
  apply F.hessian_nonpos r 0 hr hpos
  · intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact fieldHeight_hessian_mixed_nonneg k hI F hU hr hk i j hlt
    · rw [F.symmetric i j (r, 0) hr]
      exact fieldHeight_hessian_mixed_nonneg k hI F hU hr hk j i hgt
  · exact fun i => fieldHeight_radial_hessian_nonpos h hI F hU r hr hs i

end InvariantIsing

end

end OAI
