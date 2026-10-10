import OAI.MeasureTheory.Falconer.Estimates.DyadicTree
import OAI.MeasureTheory.Falconer.Frostman.GeometricCapacity

namespace OAI

/-! # Finite dyadic capacities in the original ambient dimension

These capacities construct the compactly supported Frostman law needed by the
application. At each occupied cube the available mass is the smaller of its
geometric capacity and the total available mass of its children.
-/
namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal NNReal
attribute [local instance] Classical.propDecidable

noncomputable def cubeOccupied {d : ℕ} (E : Set (Space d)) (s : ℝ)
    (Q : DyadicCube d) : ℝ :=
  if (E ∩ Q.carrier).Nonempty then Q.side^s else 0

noncomputable def cubeCapacity {d : ℕ} (E : Set (Space d)) (s : ℝ)
    (Q : DyadicCube d) : ℕ → ℝ
  | 0 => cubeOccupied E s Q
  | K+1 => min (cubeOccupied E s Q) (∑ b : Fin d → Bool, cubeCapacity E s (Q.child b) K)

theorem cubeOccupied_nonneg {d : ℕ} (E : Set (Space d)) (s : ℝ)
    (Q : DyadicCube d) (hQ : 0 ≤ Q.side) : 0 ≤ cubeOccupied E s Q := by
  unfold cubeOccupied
  split_ifs <;> positivity

theorem cubeCapacity_nonneg {d : ℕ} (E : Set (Space d)) (s : ℝ)
    (Q : DyadicCube d) (hQ : 0 ≤ Q.side) (K : ℕ) : 0 ≤ cubeCapacity E s Q K := by
  induction K generalizing Q with
  | zero => exact cubeOccupied_nonneg E s Q hQ
  | succ K ih =>
    exact le_min (cubeOccupied_nonneg E s Q hQ)
      (Finset.sum_nonneg fun b _ => ih (Q.child b) (by change 0 ≤ Q.side/2; positivity))

theorem cubeCapacity_le_occupied {d : ℕ} (E : Set (Space d)) (s : ℝ)
    (Q : DyadicCube d) (K : ℕ) : cubeCapacity E s Q K ≤ cubeOccupied E s Q := by
  cases K with
  | zero => exact le_rfl
  | succ K => exact min_le_left _ _

theorem cubeOccupied_le {d : ℕ} (E : Set (Space d)) (s : ℝ)
    (Q : DyadicCube d) (hQ : 0 ≤ Q.side) : cubeOccupied E s Q ≤ Q.side^s := by
  unfold cubeOccupied
  split_ifs
  · exact le_rfl
  · positivity

theorem content_le_cubeOccupied {d : ℕ} (E : Set (Space d)) {s : ℝ} (hs : 0 < s)
    (Q : DyadicCube d) (hQ : 0 ≤ Q.side) :
    PlanarFalconer.hausdorffContent s (E ∩ Q.carrier) ≤
      ENNReal.ofReal ((Real.sqrt d)^s * cubeOccupied E s Q) := by
  classical
  by_cases h : (E ∩ Q.carrier).Nonempty
  · rw [cubeOccupied,ite_eq_left h,← Real.mul_rpow (Real.sqrt_nonneg _) hQ]
    calc
      _ ≤ (ediam (E ∩ Q.carrier))^s := PlanarFalconer.content_le_diameter hs _
      _ ≤ (ENNReal.ofReal (Real.sqrt d * Q.side))^s := by
        apply ENNReal.rpow_le_rpow _ hs.le
        exact ediam_le_of_forall_dist_le fun x hx y hy => Q.dist_le hQ hx.2 hy.2
      _ = _ := ENNReal.ofReal_rpow_of_nonneg (by positivity) hs.le
  · rw [not_nonempty_iff_eq_empty.mp h,PlanarFalconer.content_empty hs,
      cubeOccupied,ite_eq_right h,mul_zero,ENNReal.ofReal_zero]

theorem content_le_cube_children {d : ℕ} (E : Set (Space d)) {s : ℝ} (hs : 0 < s)
    (Q : DyadicCube d) :
    PlanarFalconer.hausdorffContent s (E ∩ Q.carrier) ≤
      ∑ b : Fin d → Bool, PlanarFalconer.hausdorffContent s (E ∩ (Q.child b).carrier) := by
  simp_rw [← PlanarFalconer.contentOuter_apply hs]
  rw [Q.cover_children,inter_iUnion]
  exact (measure_iUnion_le _).trans_eq (tsum_fintype _)

theorem ofReal_finset_sum_nonneg {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ S, 0 ≤ f i) :
    ENNReal.ofReal (∑ i ∈ S, f i) = ∑ i ∈ S, ENNReal.ofReal (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha,Finset.sum_insert ha,
      ENNReal.ofReal_add (hf a (Finset.mem_insert_self _ _))
        (Finset.sum_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

theorem content_le_cubeCapacity {d : ℕ} (E : Set (Space d)) {s : ℝ} (hs : 0 < s)
    (Q : DyadicCube d) (hQ : 0 ≤ Q.side) (K : ℕ) :
    PlanarFalconer.hausdorffContent s (E ∩ Q.carrier) ≤
      ENNReal.ofReal ((Real.sqrt d)^s * cubeCapacity E s Q K) := by
  classical
  induction K generalizing Q with
  | zero => exact content_le_cubeOccupied E hs Q hQ
  | succ K ih =>
    change _ ≤ ENNReal.ofReal (_ * min _ _)
    by_cases h : cubeOccupied E s Q ≤ ∑ b : Fin d → Bool, cubeCapacity E s (Q.child b) K
    · rw [min_eq_left h]
      exact content_le_cubeOccupied E hs Q hQ
    · rw [min_eq_right (le_of_not_ge h),Finset.mul_sum,ofReal_finset_sum_nonneg]
      · exact (content_le_cube_children E hs Q).trans
          (Finset.sum_le_sum fun b _ => ih (Q.child b) (by change 0 ≤ Q.side/2; positivity))
      · intro b _
        exact mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
          (cubeCapacity_nonneg E s (Q.child b) (by change 0 ≤ Q.side/2; positivity) K)

theorem exists_uniform_cube_capacity {d : ℕ} (hd : 1 ≤ d)
    (E : Set (Space d)) (hE : IsCompact E) {s : ℝ≥0} (hs : 0 < s)
    (hDim : (s : ℝ≥0∞) < dimH E) (Q : DyadicCube d)
    (hQ : 0 < Q.side) (hEQ : E ⊆ Q.carrier) :
    ∃ c : ℝ, 0 < c ∧ ∀ K, c ≤ cubeCapacity E s Q K := by
  have hs' : 0 < (s:ℝ) := by exact_mod_cast hs
  have hp := PlanarFalconer.content_positive_of_lt_dimH E hs hDim
  have hf := PlanarFalconer.content_finite_of_bounded hs' hE.isBounded
  have hd' : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hF : 0 < (Real.sqrt d)^(s:ℝ) := Real.rpow_pos_of_pos (Real.sqrt_pos.mpr hd') _
  let c := (PlanarFalconer.hausdorffContent (s:ℝ) E).toReal / (Real.sqrt d)^(s:ℝ)
  have hc : 0 < c := div_pos (ENNReal.toReal_pos hp.ne' hf.ne) hF
  refine ⟨c,hc,fun K => ?_⟩
  have hb := content_le_cubeCapacity E hs' Q hQ.le K
  rw [inter_eq_left.mpr hEQ] at hb
  have hn := cubeCapacity_nonneg E (s:ℝ) Q hQ.le K
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [ENNReal.toReal_ofReal (mul_nonneg hF.le hn)] at hr
  exact (div_le_iff₀ hF).mpr (by simpa only [mul_comm] using hr)

end Falconer

end OAI
