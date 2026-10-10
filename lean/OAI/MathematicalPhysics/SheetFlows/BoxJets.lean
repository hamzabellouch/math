import Mathlib
import OAI.MathematicalPhysics.SheetFlows.ScheduledForce
import OAI.MathematicalPhysics.SheetFlows.JetProfiles

namespace OAI

/-! SheetFlows box jets. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace Solenoidal

def coordinateLinear : Fin 4 → SpaceTime →L[ℝ] ℝ :=
  ![ContinuousLinearMap.fst ℝ ℝ Space,
    (ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.snd ℝ ℝ Space),
    (ContinuousLinearMap.proj 1).comp (ContinuousLinearMap.snd ℝ ℝ Space),
    (ContinuousLinearMap.proj 2).comp (ContinuousLinearMap.snd ℝ ℝ Space)]

@[simp] theorem coordinateLinear_eq (j : Fin 4) (z : SpaceTime) :
    coordinateLinear j z = flatten z j := by
  fin_cases j <;> rfl

@[simp] theorem coordinateLinear_basis (i j : Fin 4) :
    coordinateLinear i (spacetimeBasis j) = if i=j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [coordinateLinear, spacetimeBasis, basis]

inductive BoxExpr where
  | const : ℚ → BoxExpr
  | coord : Fin 4 → JetExpr → BoxExpr
  | add : BoxExpr → BoxExpr → BoxExpr
  | mul : BoxExpr → BoxExpr → BoxExpr

namespace BoxExpr

def eval : BoxExpr → SpaceTime → ℝ
  | .const q => fun _ => q
  | .coord j e => fun z => e.eval (coordinateLinear j z)
  | .add e f => fun z => e.eval z + f.eval z
  | .mul e f => fun z => e.eval z * f.eval z

theorem smooth (e : BoxExpr) : ContDiff ℝ (⊤ : ℕ∞) e.eval := by
  induction e with
  | const q => exact contDiff_const
  | coord j e => exact e.smooth.comp (coordinateLinear j).contDiff
  | add e f he hf => exact he.add hf
  | mul e f he hf => exact he.mul hf

def diff (j : Fin 4) : BoxExpr → BoxExpr
  | .const _ => .const 0
  | .coord i e => if i=j then .coord i e.diff else .const 0
  | .add e f => .add (e.diff j) (f.diff j)
  | .mul e f => .add (.mul (e.diff j) f) (.mul e (f.diff j))

theorem diff_correct (e : BoxExpr) (j : Fin 4) (z : SpaceTime) :
    (e.diff j).eval z = fderiv ℝ e.eval z (spacetimeBasis j) := by
  induction e with
  | const q => simp [diff,eval]
  | coord i e =>
      have h := HasDerivAt.comp_hasFDerivAt z (e.diff_correct (coordinateLinear i z))
        (coordinateLinear i).hasFDerivAt
      have he : (.coord i e : BoxExpr).eval = e.eval ∘ coordinateLinear i := rfl
      rw [he, h.fderiv]
      by_cases hij : i=j
      · subst j
        simp only [diff, ↓reduceIte, eval, smul_apply, coordinateLinear_basis,
          smul_eq_mul, mul_one]
      · simp only [diff, eval, Rat.cast_zero, smul_apply,
          coordinateLinear_basis, ite_eq_right hij, smul_eq_mul, mul_zero]
  | add e f he hf =>
      simp only [diff, eval, fderiv_fun_add (e.smooth.differentiable (by simp) z)
        (f.smooth.differentiable (by simp) z), add_apply, he, hf]
  | mul e f he hf =>
      simp only [diff, eval, fderiv_fun_mul (e.smooth.differentiable (by simp) z)
        (f.smooth.differentiable (by simp) z), add_apply,
        smul_apply, smul_eq_mul, he, hf]
      ring

def mixed (e : BoxExpr) : List (Fin 4) → BoxExpr
  | [] => e
  | j::α => (e.mixed α).diff j

def bound : BoxExpr → ℚ → ℚ
  | .const q, _ => |q|
  | .coord _ e, R => e.bound R
  | .add e f, R => e.bound R + f.bound R
  | .mul e f, R => e.bound R * f.bound R

theorem bound_nonneg (e : BoxExpr) (R : ℚ) : 0 ≤ e.bound R := by
  induction e with
  | const q => exact abs_nonneg q
  | coord i e => exact e.bound_nonneg R
  | add e f he hf => exact add_nonneg he hf
  | mul e f he hf => exact mul_nonneg he hf

theorem bound_correct (e : BoxExpr) (R : ℚ) (z : SpaceTime)
    (hz : ∀ j, |flatten z j| ≤ |(R:ℝ)|) : |e.eval z| ≤ (e.bound R:ℝ) := by
  induction e with
  | const q => simp [eval,bound]
  | coord i e => exact e.bound_correct R (coordinateLinear i z) (by simpa using hz i)
  | add e f he hf =>
      simpa only [eval,bound,Rat.cast_add] using (abs_add_le _ _).trans (add_le_add he hf)
  | mul e f he hf =>
      simpa only [eval,bound,Rat.cast_mul,abs_mul] using
        mul_le_mul he hf (abs_nonneg _) (by exact_mod_cast e.bound_nonneg R)

end BoxExpr

def expressionField (e : Fin 3 → BoxExpr) : Field := fun t x j => (e j).eval (t,x)

theorem expressionField_smooth (e : Fin 3 → BoxExpr) : Smooth (expressionField e) :=
  contDiff_pi.mpr (fun j => (e j).smooth)

theorem mixedDerivative_expressionField (e : Fin 3 → BoxExpr) (α : List (Fin 4)) :
    mixedDerivative (expressionField e) α = fun z j => ((e j).mixed α).eval z := by
  induction α with
  | nil => rfl
  | cons k α ih =>
      ext z j
      rw [mixedDerivative,ih]
      change (fderiv ℝ (fun z j => ((e j).mixed α).eval z) z (spacetimeBasis k)) j = _
      rw [fderiv_pi (fun i => ((e i).mixed α).smooth.differentiable (by simp) z)]
      exact (((e j).mixed α).diff_correct k z).symm

def expressionBound (e : Fin 3 → BoxExpr) (α : List (Fin 4)) (R : ℚ) : ℚ :=
  ∑ j, ((e j).mixed α).bound R

theorem expressionBound_nonneg (e : Fin 3 → BoxExpr) (α : List (Fin 4)) (R : ℚ) :
    0 ≤ expressionBound e α R :=
  Finset.sum_nonneg (fun j _ => BoxExpr.bound_nonneg ((e j).mixed α) R)

theorem expressionBound_correct (e : Fin 3 → BoxExpr) (α : List (Fin 4)) (R : ℚ)
    (z : SpaceTime) (hz : ∀ j, |flatten z j| ≤ |(R:ℝ)|) :
    ‖mixedDerivative (expressionField e) α z‖ ≤ (expressionBound e α R : ℝ) := by
  apply (pi_norm_le_iff_of_nonneg (by exact_mod_cast expressionBound_nonneg e α R)).mpr
  intro j
  rw [mixedDerivative_expressionField]
  change |((e j).mixed α).eval z| ≤ _
  apply (BoxExpr.bound_correct _ R z hz).trans
  exact_mod_cast Finset.single_le_sum (fun i _ => BoxExpr.bound_nonneg _ _) (Finset.mem_univ j)

def closedPeriodCell : Set SpaceTime := Set.Icc (0,0) (1,fun _ => 10)

theorem mixedDerivative_eqOn_open {u v : Field} {S : Set SpaceTime} (hS : IsOpen S)
    (h : Set.EqOn (fun z => u z.1 z.2) (fun z => v z.1 z.2) S) (α : List (Fin 4)) :
    Set.EqOn (mixedDerivative u α) (mixedDerivative v α) S := by
  induction α with
  | nil => exact h
  | cons j α ih =>
      intro z hz
      change fderiv ℝ (mixedDerivative u α) z (spacetimeBasis j) = _
      rw [(ih.eventuallyEq_of_mem (hS.mem_nhds hz)).fderiv_eq]
      rfl

theorem mixedDerivative_eqOn_cell {u v : Field} (hu : Smooth u) (hv : Smooth v)
    (h : Set.EqOn (fun z => u z.1 z.2) (fun z => v z.1 z.2) closedPeriodCell)
    (α : List (Fin 4)) :
    Set.EqOn (mixedDerivative u α) (mixedDerivative v α) closedPeriodCell := by
  have hc : Convex ℝ closedPeriodCell := convex_Icc _ _
  have hn : (interior closedPeriodCell).Nonempty := by
    have he : interior closedPeriodCell =
        (Set.Ioo (0:ℝ) 1) ×ˢ (Set.pi Set.univ (fun _ : Fin 3 => Set.Ioo (0:ℝ) 10)) := by
      simp [closedPeriodCell, Set.Icc_prod_eq, interior_prod_eq, interior_Icc,
        ← Set.pi_univ_Icc, interior_pi_set]
    rw [he]
    exact ⟨(1/2,fun _ => 5), by norm_num [Set.mem_pi]⟩
  have hi : Set.EqOn (mixedDerivative u α) (mixedDerivative v α) (interior closedPeriodCell) :=
    mixedDerivative_eqOn_open isOpen_interior (h.mono interior_subset) α
  have hh := hi.closure (mixedDerivative_contDiff hu α).continuous (mixedDerivative_contDiff hv α).continuous
  have hclosure : closure (interior closedPeriodCell) = closedPeriodCell :=
    hc.closure_interior_eq_closure_of_nonempty_interior hn |>.trans isClosed_Icc.closure_eq
  rwa [hclosure] at hh

theorem periodic_expression_mixed_bound {u : Field} (hu : Smooth u)
    (hs : SpatiallyPeriodic u) (ht : OnePeriodic u) (e : Fin 3 → BoxExpr)
    (he : Set.EqOn (fun z => u z.1 z.2) (fun z => expressionField e z.1 z.2) closedPeriodCell)
    (α : List (Fin 4)) (z : SpaceTime) :
    ‖mixedDerivative u α z‖ ≤ (expressionBound e α 10 : ℝ) := by
  have hp := periodic_field_reduction
    (mixedDerivative_spatially_periodic hu hs α) (mixedDerivative_onePeriodic hu ht α) z.1 z.2
  change mixedDerivative u α z = mixedDerivative u α (Int.fract z.1,wrapSpace z.2) at hp
  rw [hp]
  have hx : (Int.fract z.1,wrapSpace z.2) ∈ closedPeriodCell :=
    ⟨⟨Int.fract_nonneg _, (wrapSpace_mem z.2).1⟩,
      ⟨(Int.fract_lt_one _).le, (wrapSpace_mem z.2).2⟩⟩
  rw [mixedDerivative_eqOn_cell hu (expressionField_smooth e) he α hx]
  apply expressionBound_correct
  intro j
  fin_cases j
  · simp only [flatten, Rat.cast_ofNat, abs_of_pos (by norm_num : (0:ℝ)<10)]
    rw [abs_of_nonneg (Int.fract_nonneg _)]
    exact (Int.fract_lt_one _).le.trans (by norm_num)
  all_goals
    change |wrapSpace z.2 _| ≤ |(10:ℝ)|
    rw [abs_of_nonneg ((wrapSpace_mem z.2).1 _)]
    simpa using (wrapSpace_mem z.2).2 _

end Solenoidal
end

end OAI
