import Mathlib
import OAI.Combinatorics.TriangleRemoval.Probability.FiniteMean

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

structure MarkedChild where
  required : Bool
  law : PMF (Bool × Bool)
  priority : ℕ := 0

noncomputable def markedDemand : List MarkedChild → Bool
  | [] => false
  | a :: as => a.required || markedDemand as

noncomputable def markedCheck : List MarkedChild → PMF (Bool × Bool)
  | [] => PMF.pure (true, true)
  | a :: as => a.law.bind (fun z =>
      if z.1 then PMF.pure (false, ((!a.required) || z.2) && !markedDemand as)
      else (markedCheck as).map (fun y => (y.1, ((!a.required) || z.2) && y.2)))

noncomputable def markedGood (p : PMF (Bool × Bool)) : ℝ :=
  pmfMean p (fun z => if z.2 then 1 else 0)

noncomputable def markedFailure (p : PMF (Bool × Bool)) : ℝ :=
  pmfMean p (fun z => if z.1 then 0 else 1)

theorem markedGood_nonneg (p : PMF (Bool × Bool)) : 0 ≤ markedGood p := by
  apply pmfMean_nonneg
  intro z _
  split <;> norm_num

theorem markedGood_le_one (p : PMF (Bool × Bool)) : markedGood p ≤ 1 := by
  rw [← pmfMean_const p 1]
  apply pmfMean_mono
  intro z _
  split <;> norm_num

theorem markedFailure_nonneg (p : PMF (Bool × Bool)) : 0 ≤ markedFailure p := by
  apply pmfMean_nonneg
  intro z _
  split <;> norm_num

noncomputable def markedBound : List MarkedChild → ℝ
  | [] => 1
  | a :: as => (if a.required then markedGood a.law
      else if markedDemand as then markedFailure a.law else 1) * markedBound as

theorem markedBound_nonneg (as : List MarkedChild) : 0 ≤ markedBound as := by
  induction as with
  | nil => exact zero_le_one
  | cons a as ih =>
    apply mul_nonneg _ ih
    split
    · exact markedGood_nonneg _
    · split
      · exact markedFailure_nonneg _
      · exact zero_le_one

theorem markedBound_of_no_demand (as : List MarkedChild) (h : markedDemand as = false) :
    markedBound as = 1 := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    have hh : a.required = false ∧ markedDemand as = false := by
      simpa only [markedDemand, Bool.or_eq_false_iff] using h
    simp [markedBound, hh.1, hh.2, ih hh.2]

theorem marked_visitation_bound (as : List MarkedChild) :
    markedGood (markedCheck as) ≤ markedBound as := by
  induction as with
  | nil => simp [markedGood, markedCheck, markedBound]
  | cons a as ih =>
    let f : Bool × Bool → ℝ := fun z =>
      if a.required then (if z.2 then 1 else 0)
      else if markedDemand as then (if z.1 then 0 else 1) else 1
    have hf : pmfMean a.law f =
        if a.required then markedGood a.law
        else if markedDemand as then markedFailure a.law else 1 := by
      cases hr : a.required <;> cases hd : markedDemand as <;>
        simp [f, hr, hd, markedGood, markedFailure]
    change pmfMean (a.law.bind _) _ ≤ _
    rw [pmfMean_bind]
    calc
      _ ≤ pmfMean a.law (fun z => f z * markedBound as) := by
        apply pmfMean_mono
        rintro ⟨b, g⟩ _
        have hb := markedBound_nonneg as
        have hg := markedGood_nonneg (markedCheck as)
        have hu := markedGood_le_one (markedCheck as)
        cases hr : a.required <;> cases hd : markedDemand as <;>
          cases b <;> cases g <;>
          simp only [hr, hd, Bool.not_false, Bool.not_true, Bool.false_or,
            Bool.true_or, Bool.false_and, Bool.true_and, Bool.and_false,
            Bool.and_true, Bool.false_eq_true, ↓reduceIte,
            pmfMean_pure, pmfMean_map, f, pmfMean_const,
            zero_mul, one_mul]
        all_goals first
          | exact ih
          | exact hb
          | exact le_refl _
          | simpa only [markedBound_of_no_demand as hd] using hu
          | simp only [markedBound_of_no_demand as hd, le_refl]
      _ = markedBound (a :: as) := by
        rw [pmfMean_mul_const, hf]
        rfl

noncomputable def ordinaryCheck : List (PMF Bool) → PMF Bool
  | [] => PMF.pure true
  | p :: ps => p.bind (fun b => if b then PMF.pure false else ordinaryCheck ps)

theorem markedCheck_original (as : List MarkedChild) :
    (markedCheck as).map Prod.fst = ordinaryCheck (as.map (fun a => a.law.map Prod.fst)) := by
  induction as with
  | nil => simp [markedCheck, ordinaryCheck, PMF.pure_map]
  | cons a as ih =>
    simp only [markedCheck, PMF.map_bind, List.map_cons, ordinaryCheck, PMF.bind_map]
    congr 1
    funext z
    simp only [Function.comp_apply]
    cases z.1 <;>
      simp only [ Bool.false_eq_true, ↓reduceIte, PMF.pure_map, PMF.map_comp]
    exact ih

end SharpTerminalLeave

end

end OAI
