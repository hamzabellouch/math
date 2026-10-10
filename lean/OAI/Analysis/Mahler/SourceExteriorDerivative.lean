import OAI.Analysis.Mahler.SourceFluxRegularity

namespace OAI

open ContinuousAlternatingMap
open scoped Topology

namespace Mahler
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma continuousWedgeCLM_apply (a : E [⋀^ι]→L[ℝ] ℂ) (b : E [⋀^κ]→L[ℝ] ℂ) :
    continuousWedgeCLM a b = continuousWedge a b := rfl

/-- Actual real Frechet differentiation of the whole shuffle product. -/
theorem fderiv_continuousWedge_apply {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {a : X → E [⋀^ι]→L[ℝ] ℂ} {b : X → E [⋀^κ]→L[ℝ] ℂ} {x : X}
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x) (v : X) :
    fderiv ℝ (fun y => continuousWedge (a y) (b y)) x v =
      continuousWedge (fderiv ℝ a x v) (b x) + continuousWedge (a x) (fderiv ℝ b x v) := by
  let W := continuousWedgeCLM (E := E) (ι := ι) (κ := κ)
  have hW : HasFDerivAt (fun z : E [⋀^ι]→L[ℝ] ℂ => W z) W (a x) :=
    ContinuousLinearMap.hasFDerivAt (E := E [⋀^ι]→L[ℝ] ℂ)
      (F := (E [⋀^κ]→L[ℝ] ℂ) →L[ℝ] E [⋀^ι ⊕ κ]→L[ℝ] ℂ) W
  have hWa : HasFDerivAt (fun y => W (a y)) (W.comp (fderiv ℝ a x)) x :=
    HasFDerivAt.comp (E := X) (F := E [⋀^ι]→L[ℝ] ℂ)
      (G := (E [⋀^κ]→L[ℝ] ℂ) →L[ℝ] E [⋀^ι ⊕ κ]→L[ℝ] ℂ) x hW ha.hasFDerivAt
  have hd := HasFDerivAt.clm_apply (E := X) (G := E [⋀^κ]→L[ℝ] ℂ)
    (H := E [⋀^ι ⊕ κ]→L[ℝ] ℂ) hWa hb.hasFDerivAt
  change HasFDerivAt (fun y => continuousWedge (a y) (b y)) _ x at hd
  rw [hd.fderiv]
  exact add_comm _ _

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

/-- The exact finite product-rule variation of a bundled exterior power. -/
def continuousWedgePowerVariation (a da : E [⋀^Fin 2]→L[ℝ] ℂ) :
    (k : ℕ) → E [⋀^WedgePowerSlots k]→L[ℝ] ℂ
  | 0 => 0
  | k+1 => continuousWedge da (continuousWedgePower a k) +
      continuousWedge a (continuousWedgePowerVariation a da k)

theorem fderiv_continuousWedgePower_apply {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {a : X → E [⋀^Fin 2]→L[ℝ] ℂ} {x : X}
    (ha : ContDiffAt ℝ 1 a x) (k : ℕ) (v : X) :
    fderiv ℝ (fun y => continuousWedgePower (a y) k) x v =
      continuousWedgePowerVariation (a x) (fderiv ℝ a x v) k := by
  induction k with
  | zero =>
    change fderiv ℝ (fun _ : X => ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) (1 : ℂ)) x v = 0
    rw [(hasFDerivAt_const _ x).fderiv]
    rfl
  | succ k ih =>
    change fderiv ℝ (fun y => continuousWedge (a y) (continuousWedgePower (a y) k)) x v = _
    rw [fderiv_continuousWedge_apply (ha.differentiableAt one_ne_zero)
      ((contDiffAt_continuousWedgePower ha k).differentiableAt one_ne_zero), ih]
    rfl

/-- Closedness of the actual dd^c field is a consequence of symmetric second
derivatives, through d²=0. -/
theorem extDeriv_sourceDDC_zero {u : E → ℂ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) :
    extDeriv (extDeriv (oneForm (dcLinear u))) x = 0 := by
  have hd : ContDiffAt ℝ 2 (oneForm (dcLinear u)) x :=
    contDiffAt_sourceDC (hu : ContDiffAt ℝ (2+1) u x)
  exact extDeriv_extDeriv_apply hd (by norm_num)

variable {n N m : ℕ} {U : Set (ComplexEuclidean n)}
  {f : Fin N → ComplexEuclidean n → ℂ} {G : Fin N → MvPolynomial (Fin n) ℂ}

theorem MassHypotheses.extDeriv_energyDDC_zero (h : MassHypotheses n N m U f G)
    {x : ComplexEuclidean n} (hx : x ∈ U) :
    extDeriv (extDeriv (oneForm (dcLinear (energy f)))) x = 0 :=
  extDeriv_sourceDDC_zero (h.contDiffAt_energy hx 3)

theorem MassHypotheses.extDeriv_logDDC_zero (h : MassHypotheses n N m U f G)
    {x : ComplexEuclidean n} (hx : x ∈ U) (hne : x ≠ 0) :
    extDeriv (extDeriv (oneForm (dcLinear (logTau f)))) x = 0 :=
  extDeriv_sourceDDC_zero (h.contDiffAt_logTau hx hne 3)

end
end Mahler

end OAI
