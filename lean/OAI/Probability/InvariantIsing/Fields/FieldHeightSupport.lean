import OAI.Probability.InvariantIsing.Fields.FieldHeightBox
import OAI.Probability.InvariantIsing.Fields.FieldHeightHessianSign

namespace OAI

/-! The actual scalar-field supporting inequality on strict finite
height vectors. The Hessian criterion follows from the mixed and radial derivative signs. -/

noncomputable section
open IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

theorem fieldHeight_support_strict (h : FieldStep) (r s : Fin (h.depth + 1) → ℝ)
    (hr : r ∈ fieldStrictHeightCone h.depth) (hs : s ∈ fieldStrictHeightCone h.depth) :
    fieldValue (fieldStepOfStrictHeights h s hs) 0 ≤
      fieldValue (fieldStepOfStrictHeights h r hr) 0 +
        ∑ i, (-(h.cut i.succ - h.cut i.castSucc) / 2 *
          fieldMagnetizationLevel (fieldStepOfStrictHeights h r hr) i) * (s i - r i) := by
  classical
  obtain ⟨m, V, hm, hrI, hsI⟩ := fieldHeightBox_pair r s hr hs
  let I := fieldHeightBox h.depth m V
  have hI : IsOpen I := isOpen_fieldHeightBox _ _ _
  have hconv : Convex ℝ I := convex_fieldHeightBox _ _ _
  obtain ⟨F, hF⟩ := fieldHeightBox_family h m V hm
  have hpath (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : r + t • (s - r) ∈ I := by
    have he : r + t • (s - r) = (1 - t) • r + t • s := by module
    rw [he]
    exact hconv hrI hsI (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ∑ i, ∑ j, F.PP i j (r + t • (s - r), 0) * (s i - r i) * (s j - r j) ≤ 0 :=
    fieldHeight_hessian_nonpos h hI F hF _ (hpath t ht)
      (fieldHeightBox_subset_strict hm.le (hpath t ht)) (s - r)
  have hsup := F.support_of_hessian hconv r s 0 hrI hsI hq
  let G : Fin (h.depth + 1) → ℝ := fun i => -(h.cut i.succ - h.cut i.castSucc) / 2 *
    fieldMagnetizationLevel (fieldStepOfStrictHeights h r hr) i
  have hgrad (i : Fin (h.depth + 1)) :
      F.P i (r, 0) = G i + (if i = Fin.last h.depth then (1 / 2 : ℝ) else 0) := by
    have hi := fieldHeight_gradient_identification h F hF r hrI hr i
    dsimp only [G]
    linarith
  have hsum : (∑ i, F.P i (r, 0) * (s i - r i)) =
      (∑ i, G i * (s i - r i)) + (s (Fin.last h.depth) - r (Fin.last h.depth)) / 2 := by
    simp_rw [hgrad, add_mul]
    rw [Finset.sum_add_distrib]
    congr 1
    simp [div_eq_mul_inv, mul_comm]
  have hrvalue : F.U (r, 0) - r (Fin.last h.depth) / 2 =
      fieldValue (fieldStepOfStrictHeights h r hr) 0 := by
    rw [hF]
    exact fieldHeightJointValue_strict h r hr 0
  have hsvalue : F.U (s, 0) - s (Fin.last h.depth) / 2 =
      fieldValue (fieldStepOfStrictHeights h s hs) 0 := by
    rw [hF]
    exact fieldHeightJointValue_strict h s hs 0
  rw [hsum] at hsup
  change fieldValue (fieldStepOfStrictHeights h s hs) 0 ≤
    fieldValue (fieldStepOfStrictHeights h r hr) 0 + ∑ i, G i * (s i - r i)
  linarith

end InvariantIsing

end

end OAI
