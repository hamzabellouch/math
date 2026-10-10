import OAI.Analysis.Mahler.ContinuousWedge
import OAI.Analysis.Mahler.SourceLevelFlux

namespace OAI

open ContinuousAlternatingMap
open scoped Topology

namespace Mahler
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]

/-- Linear jet operator for the normalization -D(u)(iv)/4. -/
def sourceDCOperator : (E →L[ℝ] ℂ) →L[ℝ] E [⋀^Fin 1]→L[ℝ] ℂ :=
  (ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℂ) (0 : Fin 1)).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((-1/4 : ℂ) • (ContinuousLinearMap.compL ℝ E E ℂ).flip complexStructure)

omit [FiniteDimensional ℝ E] in
lemma contDiffAt_sourceDC [FiniteDimensional ℝ E] {u : E → ℂ} {x : E} {r : ℕ}
    (hu : ContDiffAt ℝ (r+1) u x) : ContDiffAt ℝ r (oneForm (dcLinear u)) x := by
  have hd : ContDiffAt ℝ r (fderiv ℝ u) x := hu.fderiv_right (by norm_num)
  exact sourceDCOperator.contDiff.contDiffAt.comp x hd

lemma contDiffAt_sourceDDC {u : E → ℂ} {x : E} {r : ℕ}
    (hu : ContDiffAt ℝ (r+2) u x) :
    ContDiffAt ℝ r (extDeriv (oneForm (dcLinear u))) x := by
  have hd : ContDiffAt ℝ (r+1) (oneForm (dcLinear u)) x :=
    contDiffAt_sourceDC (by convert hu using 1 ; norm_num [add_assoc])
  have hdd : ContDiffAt ℝ r (fderiv ℝ (oneForm (dcLinear u))) x :=
    hd.fderiv_right (by norm_num)
  exact (alternatizeUncurryFinCLM ℝ E ℂ).contDiff.contDiffAt.comp x hdd

/-- The recursive shuffle power as a continuous form. -/
def continuousWedgePower (a : E [⋀^Fin 2]→L[ℝ] ℂ) :
    (k : ℕ) → E [⋀^WedgePowerSlots k]→L[ℝ] ℂ
  | 0 => ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) 1
  | k+1 => continuousWedge a (continuousWedgePower a k)

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] in
lemma continuousWedgePower_toAlternatingMap [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] (a : E [⋀^Fin 2]→L[ℝ] ℂ) (k : ℕ) :
    (continuousWedgePower a k).toAlternatingMap = wedgePower a.toAlternatingMap k := by
  induction k with
  | zero => rfl
  | succ k ih => change wedge _ _ = _; rw [ih]; rfl

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
lemma contDiffAt_continuousWedgePower [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {a : X → E [⋀^Fin 2]→L[ℝ] ℂ} {x : X} {r : WithTop ℕ∞}
    (ha : ContDiffAt ℝ r a x) (k : ℕ) :
    ContDiffAt ℝ r (fun y => continuousWedgePower (a y) k) x := by
  induction k with
  | zero => exact contDiffAt_const
  | succ k ih => exact contDiffAt_continuousWedge ha ih

def continuousSourceBoundaryForm (u : E → ℂ) (k : ℕ) (x : E) :
    E [⋀^Fin 1 ⊕ WedgePowerSlots k]→L[ℝ] ℂ :=
  continuousWedge (oneForm (dcLinear u) x)
    (continuousWedgePower (extDeriv (oneForm (dcLinear u)) x) k)

lemma continuousSourceBoundaryForm_eq {n : ℕ} (u : ComplexEuclidean n → ℂ)
    (k : ℕ) (x : ComplexEuclidean n) :
    (continuousSourceBoundaryForm u k x).toAlternatingMap = sourceBoundaryForm u k x := by
  unfold continuousSourceBoundaryForm sourceBoundaryForm
  change wedge _ _ = _
  rw [continuousWedgePower_toAlternatingMap]

lemma continuousSourceBoundaryForm_apply {n : ℕ} (u : ComplexEuclidean n → ℂ)
    (k : ℕ) (x : ComplexEuclidean n) (v : Fin 1 ⊕ WedgePowerSlots k → ComplexEuclidean n) :
    continuousSourceBoundaryForm u k x v = sourceBoundaryForm u k x v :=
  congrArg (fun a => a v) (continuousSourceBoundaryForm_eq u k x)

/-- C1 regularity of the whole actual flux form uses C3 of its potential. -/
theorem contDiffAt_sourceBoundaryForm {u : E → ℂ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (k : ℕ) :
    ContDiffAt ℝ 1 (continuousSourceBoundaryForm u k) x := by
  exact contDiffAt_continuousWedge
    (contDiffAt_sourceDC (hu.of_le (by norm_num) : ContDiffAt ℝ (1+1) u x))
    (contDiffAt_continuousWedgePower
      (contDiffAt_sourceDDC (hu : ContDiffAt ℝ (1+2) u x)) k)

variable {n N m : ℕ} {U : Set (ComplexEuclidean n)}
  {f : Fin N → ComplexEuclidean n → ℂ} {G : Fin N → MvPolynomial (Fin n) ℂ}

theorem MassHypotheses.contDiffOn_energyBoundaryForm (h : MassHypotheses n N m U f G) (k : ℕ) :
    ContDiffOn ℝ 1 (continuousSourceBoundaryForm (energy f) k) U := by
  intro x hx
  exact (contDiffAt_sourceBoundaryForm (h.contDiffAt_energy hx 3) k).contDiffWithinAt

theorem MassHypotheses.contDiffOn_logBoundaryForm (h : MassHypotheses n N m U f G) (k : ℕ) :
    ContDiffOn ℝ 1 (continuousSourceBoundaryForm (logTau f) k) (U \ {0}) := by
  intro x hx
  exact (contDiffAt_sourceBoundaryForm
    (h.contDiffAt_logTau hx.1 (by simpa using hx.2) 3) k).contDiffWithinAt

end
end Mahler

end OAI
