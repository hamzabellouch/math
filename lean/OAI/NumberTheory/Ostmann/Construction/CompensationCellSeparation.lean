import OAI.NumberTheory.Ostmann.Arithmetic.MovingCompensationGapList

namespace OAI

/-! # Distinct compensation types occupy disjoint prime cells -/

namespace Ostmann

theorem movingCompensationTargets_upper (J B : ℝ) (ds : List ℝ)
    (hJ : 0 ≤ J) (hd : ∀ d ∈ ds, 0 ≤ d ∧ d ≤ B) :
    ∀ w ∈ movingCompensationTargets J ds, w ≤ 2 ^ ds.length * J / 2 := by
  induction ds with
  | nil => simp [movingCompensationTargets]
  | cons d ds ih =>
    have hd0 := hd d (by simp)
    have hds : ∀ e ∈ ds, 0 ≤ e ∧ e ≤ B := fun e he => hd e (by simp [he])
    have herr := (movingCompensationTargetError_bounds B ds hds).1
    have hsum := movingCompensationTargets_sum J ds
    have hpJ : 0 ≤ (2 : ℝ) ^ ds.length * J := by positivity
    intro w hw
    simp only [movingCompensationTargets, List.mem_cons] at hw
    simp only [List.length_cons, pow_succ]
    rcases hw with rfl | hw
    · linarith
    · have hh := ih hds w hw
      linarith

theorem movingCompensationTargets_separated (J B : ℝ) (ds : List ℝ)
    (hJ : 0 ≤ J) (hB : B ≤ J / 4)
    (hd : ∀ d ∈ ds, 0 ≤ d ∧ d ≤ B) :
    (movingCompensationTargets J ds).Pairwise (fun x y => y + J / 4 ≤ x) := by
  induction ds with
  | nil => simp [movingCompensationTargets]
  | cons d ds ih =>
    have hd0 := hd d (by simp)
    have hds : ∀ e ∈ ds, 0 ≤ e ∧ e ≤ B := fun e he => hd e (by simp [he])
    have herr := (movingCompensationTargetError_bounds B ds hds).2
    have hsum := movingCompensationTargets_sum J ds
    change ((J + (movingCompensationTargets J ds).sum - d) ::
      movingCompensationTargets J ds).Pairwise _
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih hds⟩
    intro w hw
    have hu := movingCompensationTargets_upper J B ds hJ hds w hw
    have hp : (1 : ℝ) ≤ 2 ^ ds.length := one_le_pow₀ (by norm_num)
    have hpB := mul_le_mul_of_nonneg_left hB (by positivity : 0 ≤ (2 : ℝ) ^ ds.length)
    have hpJ := mul_le_mul_of_nonneg_right hp hJ
    nlinarith only [hu, herr, hsum, hpB, hpJ, hd0.2]

theorem compensation_cell_separation (J E w v c d : ℝ)
    (hgap : v + J / 4 ≤ w) (hbudget : 16 * (E + 1) ≤ J)
    (hc : w / 4 ≤ c) (hd : d ≤ v / 4 + E) :
    d + 1 ≤ c := by linarith

end Ostmann

end OAI
