import OAI.Probability.SATComputability.HierarchyProgram
import OAI.Probability.DilutedSpin.FiniteProducts

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass Nat.Partrec
open scoped BigOperators

noncomputable def branchSum (bs : List (ℚ × List Code)) (f : List Code → ℝ) : ℝ :=
  (bs.map (fun b => (b.1 : ℝ) * f b.2)).sum

theorem normalizedBranches_expect (c : Code) (f : Code → ℝ) :
    ((normalizedBranches c).map (fun b => (b.1 : ℝ)*f b.2)).sum =
      (branchWeights c).toLaw.expect (fun i => f ((normalizedBranches c).get i).2) := by
  unfold DilutedSpinGlass.FiniteLaw.expect
  change _ = ∑ i : Fin (normalizedBranches c).length,
    (((normalizedBranches c).get i).1 : ℝ) * f ((normalizedBranches c).get i).2
  rw [← List.sum_ofFn]
  have h := congrArg (fun bs : List (ℚ × Code) =>
    (bs.map (fun b => (b.1 : ℝ)*f b.2)).sum) (List.ofFn_get (normalizedBranches c))
  simpa only [List.map_ofFn, Function.comp_def] using h.symm

theorem branchSum_cons (c : Code) (cs : List Code) (f : List Code → ℝ) :
    branchSum (chooseChildren (c::cs)) f =
      ((normalizedBranches c).map (fun b => (b.1 : ℝ) *
        branchSum (chooseChildren cs) (fun rest => f (b.2::rest)))).sum := by
  simp only [branchSum, chooseChildren, List.foldr_cons, List.map_flatMap,
    sum_flatMap_eq, List.map_map, Function.comp_def, Rat.cast_mul]
  apply congrArg List.sum
  apply List.map_congr_left
  intro b _
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro r _
  exact mul_assoc _ _ _

theorem chooseChildren_expect (cs : List Code) (f : List Code → ℝ) :
    branchSum (chooseChildren cs) f =
      (FiniteLaw.pi (fun i : Fin cs.length => (branchWeights (cs.get i)).toLaw)).expect
        (fun a => f (List.ofFn (fun i =>
          ((normalizedBranches (cs.get i)).get (a i)).2))) := by
  induction cs generalizing f with
  | nil => simp [branchSum, chooseChildren, FiniteLaw.expect, FiniteLaw.pi]
  | cons c cs ih =>
    rw [branchSum_cons]
    simp_rw [ih]
    rw [normalizedBranches_expect c (fun d =>
      (FiniteLaw.pi (fun i : Fin cs.length => (branchWeights (cs.get i)).toLaw)).expect
        (fun a => f (d :: List.ofFn (fun i =>
          ((normalizedBranches (cs.get i)).get (a i)).2)))), FiniteLaw.expect_pi_cons]
    apply FiniteLaw.expect_congr
    intro a
    apply FiniteLaw.expect_congr
    intro rest
    congr 1
    rw [List.ofFn_succ]
    rfl

theorem chooseChildren_expect_ofFn {L : ℕ} (cs : Fin L → Code) (f : List Code → ℝ) :
    branchSum (chooseChildren (List.ofFn cs)) f =
      (FiniteLaw.pi (fun i : Fin L => (branchWeights (cs i)).toLaw)).expect
        (fun a => f (List.ofFn (fun i => ((normalizedBranches (cs i)).get (a i)).2))) := by
  induction L generalizing f with
  | zero => simp [branchSum, chooseChildren, FiniteLaw.expect, FiniteLaw.pi]
  | succ L ih =>
    rw [List.ofFn_succ, branchSum_cons]
    simp_rw [ih]
    rw [normalizedBranches_expect (cs 0) (fun d =>
      (FiniteLaw.pi (fun i : Fin L => (branchWeights (cs i.succ)).toLaw)).expect
        (fun a => f (d :: List.ofFn (fun i =>
          ((normalizedBranches (cs i.succ)).get (a i)).2)))), FiniteLaw.expect_pi_cons]
    apply FiniteLaw.expect_congr
    intro a
    apply FiniteLaw.expect_congr
    intro rest
    congr 1
    rw [List.ofFn_succ]
    rfl

end FixedClauseThreshold.Computability

end OAI
