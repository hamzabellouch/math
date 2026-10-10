import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarBranchAnchors
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.NormalizedPulseSchedule

namespace OAI

/-! The eight actual local trajectories, translated to the fixed initial
particle chart. Their derivatives are derivatives of the full processor,
not merely of isolated polynomial fields. -/

noncomputable section
namespace ForcedComputation.Recorder.Planar
open ShearFlows PlanarHamiltonian PlanarRouting PlanarTiming Set
open scoped ContDiff

theorem mem_translated_collar (δ : Fin 2 → ℚ) (R : RationalBox 2) (r : ℚ) (x : Plane) :
    translatedPoint δ x ∈ (rectangleCollar (translatedBox δ R) r).carrier ↔
      x ∈ (rectangleCollar R r).carrier := by
  constructor
  · intro h j
    have hj := h j
    change ((R.lower j - 2 * r : ℚ) : ℝ) ≤ x j ∧
      x j ≤ ((R.upper j + 2 * r : ℚ) : ℝ)
    change ((R.lower j + δ j - 2 * r : ℚ) : ℝ) ≤ x j + (δ j : ℝ) ∧
      x j + (δ j : ℝ) ≤ ((R.upper j + δ j + 2 * r : ℚ) : ℝ) at hj
    push_cast at hj ⊢
    constructor <;> linarith [hj.1, hj.2]
  · intro h j
    have hj := h j
    change ((R.lower j + δ j - 2 * r : ℚ) : ℝ) ≤ x j + (δ j : ℝ) ∧
      x j + (δ j : ℝ) ≤ ((R.upper j + δ j + 2 * r : ℚ) : ℝ)
    change ((R.lower j - 2 * r : ℚ) : ℝ) ≤ x j ∧
      x j ≤ ((R.upper j + 2 * r : ℚ) : ℝ) at hj
    push_cast at hj ⊢
    constructor <;> linarith [hj.1, hj.2]

def branchCurve (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) (x : Plane) (k : Fin 8) : ℝ → Plane :=
  (compiledPulse M hM (branchIndices M hM b k)).curve
    (branchAnchors M hM b x k.castSucc)

theorem branchCurve_start (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) (x : Plane) (k : Fin 8) :
    branchCurve M hM b x k (cut (actions M hM).length (branchIndices M hM b k).val) =
      branchAnchors M hM b x k.castSucc :=
  Pulse.curve_before (compiledPulse_valid M hM _) _ (cut_le_start _)

theorem branchCurve_endpoint (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) (x : Plane) (k : Fin 8) :
    (compiledPulse M hM (branchIndices M hM b k)).primitive.endpoint
      (branchAnchors M hM b x k.castSucc) = branchAnchors M hM b x k.succ := by
  change ((actions M hM).get (branchIndices M hM b k)).primitive.endpoint _ = _
  rw [branchIndices_get]
  exact branchAnchors_endpoint M hM b x k

theorem branchCurve_finish (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) (x : Plane) (k : Fin 8) :
    branchCurve M hM b x k (cut (actions M hM).length ((branchIndices M hM b k).val + 1)) =
      branchAnchors M hM b x k.succ := by
  unfold branchCurve
  rw [Pulse.curve_after (compiledPulse_valid M hM _) _ (by
    change (finish (branchIndices M hM b k) : ℝ) ≤ _
    rw [finish_eq_cut])]
  exact branchCurve_endpoint M hM b x k

def normalizedAnchors (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (b : Branch (finiteMachine (freshMachine I.1) (freshInput_valid hI).1))
    (x : Plane) (k : Fin 9) : Plane :=
  translatedPoint (initialShift (freshInput I) (freshInput_valid hI))
    (branchAnchors (freshMachine I.1) (freshInput_valid hI).1 b x k)

def normalizedCurve (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (b : Branch (finiteMachine (freshMachine I.1) (freshInput_valid hI).1))
    (x : Plane) (k : Fin 8) (t : ℝ) : Plane :=
  translatedPoint (initialShift (freshInput I) (freshInput_valid hI))
    (branchCurve (freshMachine I.1) (freshInput_valid hI).1 b x k t)

theorem normalizedCurve_start (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (b : Branch (finiteMachine (freshMachine I.1) (freshInput_valid hI).1))
    (x : Plane) (k : Fin 8) :
    normalizedCurve I hI b x k
      (cut (actions (freshMachine I.1) (freshInput_valid hI).1).length
        (branchIndices (freshMachine I.1) (freshInput_valid hI).1 b k).val) =
      normalizedAnchors I hI b x k.castSucc := by
  unfold normalizedCurve normalizedAnchors
  rw [branchCurve_start]

theorem normalizedCurve_finish (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (b : Branch (finiteMachine (freshMachine I.1) (freshInput_valid hI).1))
    (x : Plane) (k : Fin 8) :
    normalizedCurve I hI b x k
      (cut (actions (freshMachine I.1) (freshInput_valid hI).1).length
        ((branchIndices (freshMachine I.1) (freshInput_valid hI).1 b k).val + 1)) =
      normalizedAnchors I hI b x k.succ := by
  unfold normalizedCurve normalizedAnchors
  rw [branchCurve_finish]

theorem normalizedCurve_smooth (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (b : Branch (finiteMachine (freshMachine I.1) (freshInput_valid hI).1))
    (x : Plane) (k : Fin 8) : ContDiff ℝ ∞ (normalizedCurve I hI b x k) := by
  exact (Pulse.curve_smooth _ _).add contDiff_const

theorem normalizedCurve_mem (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (b : Branch (finiteMachine (freshMachine I.1) (freshInput_valid hI).1))
    {x : Plane} (hx : x ∈ (instruction (freshMachine I.1) (freshInput_valid hI).1 b).source.carrier)
    (k : Fin 8) (t : ℝ) : normalizedCurve I hI b x k t ∈
      (normalizedPulse I hI (branchIndices (freshMachine I.1) (freshInput_valid hI).1 b k)).rectangle.carrier :=
  (mem_translatedBox _ _ _).mpr (branch_curve_mem_rectangle _ _ b hx k t)

theorem normalizedCurve_chart (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (b : Branch (finiteMachine (freshMachine I.1) (freshInput_valid hI).1))
    {x : Plane} (hx : x ∈ (instruction (freshMachine I.1) (freshInput_valid hI).1 b).source.carrier)
    (k : Fin 8) (t : ℝ) (j : Fin 2) :
    0 < normalizedCurve I hI b x k t j ∧ normalizedCurve I hI b x k t j < 1 := by
  have hm := normalizedCurve_mem I hI b hx k t j
  have hb := (normalizedPulse_inUnit I hI
    (branchIndices (freshMachine I.1) (freshInput_valid hI).1 b k)).2.2 j
  have hc := (normalizedPulse_valid I hI
    (branchIndices (freshMachine I.1) (freshInput_valid hI).1 b k)).1
  have hb' : (0 : ℝ) <
      ((normalizedPulse I hI (branchIndices (freshMachine I.1) (freshInput_valid hI).1 b k)).rectangle.lower j : ℝ) -
        2 * (normalizedPulse I hI (branchIndices (freshMachine I.1) (freshInput_valid hI).1 b k)).collar ∧
      ((normalizedPulse I hI (branchIndices (freshMachine I.1) (freshInput_valid hI).1 b k)).rectangle.upper j : ℝ) +
        2 * (normalizedPulse I hI (branchIndices (freshMachine I.1) (freshInput_valid hI).1 b k)).collar < 1 := by
    exact_mod_cast hb
  have hc' : (0 : ℝ) < (normalizedPulse I hI
      (branchIndices (freshMachine I.1) (freshInput_valid hI).1 b k)).collar := by exact_mod_cast hc
  constructor <;> linarith [hm.1, hm.2, hb'.1, hb'.2]

theorem normalizedCurve_ode (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (b : Branch (finiteMachine (freshMachine I.1) (freshInput_valid hI).1))
    {x : Plane} (hx : x ∈ (instruction (freshMachine I.1) (freshInput_valid hI).1 b).source.carrier)
    (k : Fin 8) (t : ℝ)
    (ht : t ∈ Icc
      (cut (actions (freshMachine I.1) (freshInput_valid hI).1).length
        (branchIndices (freshMachine I.1) (freshInput_valid hI).1 b k).val)
      (cut (actions (freshMachine I.1) (freshInput_valid hI).1).length
        ((branchIndices (freshMachine I.1) (freshInput_valid hI).1 b k).val + 1))) :
    HasDerivAt (normalizedCurve I hI b x k)
      (planarSlice (normalizedHamiltonian I hI) t (normalizedCurve I hI b x k t)) t := by
  have hm := branch_curve_mem_rectangle _ _ b hx k t
  have hd := Pulse.translated_hasDerivAt
    (initialShift (freshInput I) (freshInput_valid hI)) (compiledPulse_valid _ _ _)
    hm (Pulse.curve_ode (compiledPulse_valid _ _ _) _ t hm)
  have h₀ := normalizedCurve_chart I hI b hx k t 0
  have h₁ := normalizedCurve_chart I hI b hx k t 1
  have he := normalizedSlice_on_cell I hI
    (branchIndices (freshMachine I.1) (freshInput_valid hI).1 b k) ht
    (normalizedCurve I hI b x k t) h₀ h₁
  exact hd.congr_deriv he.symm

end ForcedComputation.Recorder.Planar

end

end OAI
