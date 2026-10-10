import Mathlib
import OAI.MathematicalPhysics.SheetFlows.BoxJets

namespace OAI

/-! SheetFlows rational formula. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace Solenoidal

namespace BoxExpr

def suml : List BoxExpr → BoxExpr
  | [] => .const 0
  | e :: l => .add e (suml l)

@[simp] theorem eval_suml (l : List BoxExpr) (z : SpaceTime) :
    (suml l).eval z = (l.map (fun e => e.eval z)).sum := by
  induction l with
  | nil => simp [suml,eval]
  | cons e l ih => simp [suml,eval,ih]

def sum {ι : Type*} [Fintype ι] (f : ι → BoxExpr) : BoxExpr :=
  suml (Finset.univ.toList.map f)

@[simp] theorem eval_sum {ι : Type*} [Fintype ι] (f : ι → BoxExpr) (z : SpaceTime) :
    (sum f).eval z = ∑ i, (f i).eval z := by
  simp [sum, List.map_map, Function.comp_def]

end BoxExpr

def HasRationalFormula (u : Field) : Prop :=
  ∃ e : Fin 3 → BoxExpr,
    Set.EqOn (fun z => u z.1 z.2) (fun z => expressionField e z.1 z.2) closedPeriodCell

namespace HasRationalFormula

theorem zero : HasRationalFormula (0 : Field) := by
  refine ⟨fun _ => .const 0, ?_⟩
  intro z hz
  ext j
  simp [expressionField,BoxExpr.eval]

theorem add {u v : Field} (hu : HasRationalFormula u) (hv : HasRationalFormula v) :
    HasRationalFormula (u+v) := by
  obtain ⟨e,he⟩ := hu
  obtain ⟨f,hf⟩ := hv
  refine ⟨fun j => .add (e j) (f j), ?_⟩
  intro z hz
  ext j
  have h₁ := congrFun (he hz) j
  have h₂ := congrFun (hf hz) j
  exact congrArg₂ (·+·) h₁ h₂

theorem smul {u : Field} (hu : HasRationalFormula u) (q : ℚ) :
    HasRationalFormula ((q:ℝ) • u) := by
  obtain ⟨e,he⟩ := hu
  refine ⟨fun j => .mul (.const q) (e j), ?_⟩
  intro z hz
  ext j
  have hh := congrFun (he hz) j
  simpa only [expressionField,BoxExpr.eval,Pi.smul_apply,smul_eq_mul] using congrArg ((q:ℝ)*·) hh

theorem sum {ι : Type*} [Fintype ι] {u : ι → Field}
    (hu : ∀ i, HasRationalFormula (u i)) : HasRationalFormula (∑ i, u i) := by
  choose e he using hu
  refine ⟨fun j => BoxExpr.sum (fun i => e i j), ?_⟩
  intro z hz
  ext j
  simp only [Finset.sum_apply,expressionField,BoxExpr.eval_sum]
  exact Finset.sum_congr rfl (fun i _ => congrFun (he i hz) j)

theorem mixed {u : Field} (hu : HasRationalFormula u) (hs : Smooth u) (α : List (Fin 4)) :
    HasRationalFormula (fun t x => mixedDerivative u α (t,x)) := by
  obtain ⟨e,he⟩ := hu
  refine ⟨fun j => (e j).mixed α, ?_⟩
  intro z hz
  have hh := mixedDerivative_eqOn_cell hs (expressionField_smooth e) he α hz
  rw [mixedDerivative_expressionField] at hh
  exact hh

theorem directional {u : Field} (hu : HasRationalFormula u) (hs : Smooth u) (j : Fin 4) :
    HasRationalFormula (fieldDirectional u (spacetimeBasis j)) := hu.mixed hs [j]

theorem fullTimePartial {u : Field} (hu : HasRationalFormula u) (hs : Smooth u) :
    HasRationalFormula (Solenoidal.fullTimePartial u) := by
  rw [fullTimePartial_eq_fieldDirectional hs]
  exact hu.directional hs 0

theorem spatialPartial {u : Field} (hu : HasRationalFormula u) (hs : Smooth u) (j : Fin 3) :
    HasRationalFormula (Solenoidal.spatialPartial u j) := by
  rw [spatialPartial_eq_fieldDirectional hs]
  have hh := hu.directional hs j.succ
  have he : spacetimeBasis j.succ = (0,basis j) := by fin_cases j <;> rfl
  rwa [he] at hh

theorem laplacian {u : Field} (hu : HasRationalFormula u) (hs : Smooth u) :
    HasRationalFormula (Solenoidal.laplacian u) :=
  .sum (fun j => (hu.spatialPartial hs j).spatialPartial (smooth_spatialPartial hs j) j)

theorem directForce {u : Field} (hu : HasRationalFormula u) (hs : Smooth u) (q : ℚ) :
    HasRationalFormula (globalDirectForce q u) := by
  have hh := (hu.fullTimePartial hs).add ((hu.laplacian hs).smul (-q))
  convert hh using 1
  ext t x j
  simp [globalDirectForce,sub_eq_add_neg]

theorem bounds {u : Field} (hu : HasRationalFormula u) (hs : Smooth u)
    (hx : SpatiallyPeriodic u) (ht : OnePeriodic u) :
    ∃ e : Fin 3 → BoxExpr, ∀ α z,
      ‖mixedDerivative u α z‖ ≤ (expressionBound e α 10 : ℝ) := by
  obtain ⟨e,he⟩ := hu
  exact ⟨e,periodic_expression_mixed_bound hs hx ht e he⟩

end HasRationalFormula

def spatialCoordinate (i : Fin 3) (e : JetExpr) : BoxExpr := .coord i.succ e

@[simp] theorem spatialCoordinate_eval (i : Fin 3) (e : JetExpr) (t : ℝ) (x : Space) :
    (spatialCoordinate i e).eval (t,x) = e.eval (x i) := by
  fin_cases i <;> rfl

theorem tensorVelocity_formula (i : Fin 3) (g : Fin 3 → ℝ → ℝ)
    (h : ∀ j, Nonempty (PeriodicJet 10 (g j))) :
    HasRationalFormula (tensorVelocity i g) := by
  classical
  let p := fun j => Classical.choice (h j)
  let e : BoxExpr := .mul (.mul (spatialCoordinate 0 (p 0).expression)
    (spatialCoordinate 1 (p 1).expression)) (spatialCoordinate 2 (p 2).expression)
  refine ⟨fun j => .mul e (.const (if j=i then 1 else 0)), ?_⟩
  intro z hz
  have hx (j : Fin 3) : z.2 j ∈ Set.Icc (0:ℝ) 10 := ⟨hz.1.2 j,hz.2.2 j⟩
  ext j
  have h₀ := (p 0).on_chart (hx 0)
  have h₁ := (p 1).on_chart (hx 1)
  have h₂ := (p 2).on_chart (hx 2)
  simp only [tensorVelocity,tensorScalar,Fin.prod_univ_succ,Fin.isValue,
    Fin.prod_univ_zero,mul_one,Pi.smul_apply,smul_eq_mul,
    expressionField,BoxExpr.eval,e,spatialCoordinate_eval]
  change g 0 (z.2 0) * (g 1 (z.2 1) * g 2 (z.2 2)) * basis i j = _
  rw [h₀,h₁,h₂]
  by_cases hji : j=i
  · subst j; simp [basis,mul_assoc]
  · simp [basis,hji]

theorem timeProfile_formula {u : Field} (hu : HasRationalFormula u) {g : ℝ → ℝ}
    (p : PeriodicJet 1 g) : HasRationalFormula (fun t x => g t • u t x) := by
  obtain ⟨e,he⟩ := hu
  refine ⟨fun j => .mul (.coord 0 p.expression) (e j), ?_⟩
  intro z hz
  ext j
  have hh := congrFun (he hz) j
  have ht := p.on_chart (show z.1 ∈ Set.Icc (0:ℝ) (1:ℚ) by simpa using And.intro hz.1.1 hz.2.1)
  change g z.1 * u z.1 z.2 j = p.expression.eval z.1 * (e j).eval z
  change u z.1 z.2 j = (e j).eval z at hh
  rw [hh,ht]

def slotLeftRat (m : ℕ) (i : Fin m) : ℚ := 1/4 + (i:ℕ) / (2*m)
def slotRightRat (m : ℕ) (i : Fin m) : ℚ := slotLeftRat m i + 1/(4*m)

@[simp] theorem slotLeftRat_cast (m : ℕ) (i : Fin m) :
    (slotLeftRat m i : ℝ) = slotLeft m i := by
  simp [slotLeftRat,slotLeft]

@[simp] theorem slotRightRat_cast (m : ℕ) (i : Fin m) :
    (slotRightRat m i : ℝ) = slotRight m i := by
  simp [slotRightRat,slotRight]

def scheduledPulse_jet {m : ℕ} (i : Fin m) : PeriodicJet 1 (scheduledPulse m i) := by
  have hl : slotLeftRat m i < slotRightRat m i := by
    have hh : (slotLeftRat m i : ℝ) < slotRightRat m i := by
      simpa only [slotLeftRat_cast,slotRightRat_cast] using (slot_bounds i).2.1
    exact_mod_cast hh
  have ha : 0 ≤ slotLeftRat m i := by
    have := (slot_bounds i).1
    have : (0:ℝ) ≤ slotLeftRat m i := by rw [slotLeftRat_cast]; linarith
    exact_mod_cast this
  have hb : slotRightRat m i ≤ 1 := by
    have := (slot_bounds i).2.2
    have : (slotRightRat m i:ℝ) ≤ 1 := by rw [slotRightRat_cast]; linarith
    exact_mod_cast this
  simpa only [slotLeftRat_cast,slotRightRat_cast,scheduledPulse] using
    periodicPulse_jet (slotLeftRat m i) (slotRightRat m i) hl ha hb

theorem scheduleVelocity_formula {m : ℕ} (v : Fin m → Space → Space)
    (h : ∀ i, HasRationalFormula (fun _ => v i)) :
    HasRationalFormula (scheduleVelocity v) := by
  have hh := HasRationalFormula.sum (fun i => timeProfile_formula (h i) (scheduledPulse_jet i))
  convert hh using 1
  ext t x j
  simp [scheduleVelocity,Finset.sum_apply]

end Solenoidal
end

end OAI
