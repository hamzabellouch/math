import OAI.Analysis.Mahler.SourceFluxRegularity
import OAI.Analysis.Mahler.PuncturedSublevelStokes

namespace OAI

open ContinuousAlternatingMap Set Filter MeasureTheory
open scoped Topology Manifold

namespace Mahler
noncomputable section

/-- The leading one-form slot precedes the interleaved two-form slots. -/
def sourceBoundarySlots (k : ℕ) : Fin 1 ⊕ WedgePowerSlots k ≃ Fin (2*k+1) :=
  ((Equiv.sumCongr (Equiv.refl (Fin 1)) ((pairSlotEquiv k).trans finProdFinEquiv)).trans
    finSumFinEquiv).trans (finCongr (by omega))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def sourceReindex (e : ι ≃ κ) (a : E [⋀^ι]→L[ℝ] ℂ) : E [⋀^κ]→L[ℝ] ℂ :=
  { a.toAlternatingMap.domDomCongr e with
    cont := a.cont.comp (continuous_pi (fun i => continuous_apply (e i))) }

def sourceReindexCLM (e : ι ≃ κ) : (E [⋀^ι]→L[ℝ] ℂ) →L[ℝ] E [⋀^κ]→L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := sourceReindex e
      map_add' := fun _ _ => by ext v; rfl
      map_smul' := fun _ _ => by ext v; rfl }

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

def sourceRealBoundaryForm (u : E → ℂ) (k : ℕ) (x : E) :
    E [⋀^Fin (2*k+1)]→L[ℝ] ℝ :=
  Complex.reCLM.compContinuousAlternatingMap
    (sourceReindex (sourceBoundarySlots k) (continuousSourceBoundaryForm u k x))

omit [FiniteDimensional ℝ E] in
lemma sourceRealBoundaryForm_apply [FiniteDimensional ℝ E] (u : E → ℂ) (k : ℕ) (x : E)
    (v : Fin (2*k+1) → E) :
    sourceRealBoundaryForm u k x v =
      (continuousSourceBoundaryForm u k x (fun s => v (sourceBoundarySlots k s))).re := rfl

lemma contDiffAt_sourceRealBoundaryForm {u : E → ℂ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (k : ℕ) :
    ContDiffAt ℝ 1 (sourceRealBoundaryForm u k) x := by
  exact ((ContinuousLinearMap.compContinuousAlternatingMapCLM ℝ E ℂ ℝ (Fin (2*k+1))
      Complex.reCLM).contDiff.contDiffAt.comp x
    ((sourceReindexCLM (E := E) (sourceBoundarySlots k)).contDiff.contDiffAt.comp x
      (contDiffAt_sourceBoundaryForm hu k)))

def sourceCoordinateForm {d : ℕ} (Ψ : (Fin d → ℝ) ≃L[ℝ] E)
    (u : E → ℂ) (k : ℕ) (x : Fin d → ℝ) :
    (Fin d → ℝ) [⋀^Fin (2*k+1)]→L[ℝ] ℝ :=
  (sourceRealBoundaryForm u k (Ψ x)).compContinuousLinearMap Ψ.toContinuousLinearMap

lemma contDiffAt_sourceCoordinateForm {d : ℕ}
    (Ψ : (Fin d → ℝ) ≃L[ℝ] E) {u : E → ℂ} {x : Fin d → ℝ}
    (hu : ContDiffAt ℝ 3 u (Ψ x)) (k : ℕ) :
    ContDiffAt ℝ 1 (sourceCoordinateForm Ψ u k) x := by
  exact (ContinuousAlternatingMap.compContinuousLinearMapCLM Ψ.toContinuousLinearMap).contDiff.contDiffAt.comp x
    ((contDiffAt_sourceRealBoundaryForm hu k).comp x Ψ.contDiff.contDiffAt)

variable {n N m : ℕ} {U : Set (ComplexEuclidean n)}
  {f : Fin N → ComplexEuclidean n → ℂ} {G : Fin N → MvPolynomial (Fin n) ℂ}

theorem MassHypotheses.contDiffOn_coordinateEnergy (h : MassHypotheses n N m U f G)
    {d : ℕ} (Ψ : (Fin d → ℝ) ≃L[ℝ] ComplexEuclidean n) (k : ℕ) :
    ContDiffOn ℝ 1 (sourceCoordinateForm Ψ (energy f) k) (Ψ ⁻¹' U) := by
  intro x hx
  exact (contDiffAt_sourceCoordinateForm Ψ (h.contDiffAt_energy hx 3) k).contDiffWithinAt

theorem MassHypotheses.contDiffOn_coordinateLog (h : MassHypotheses n N m U f G)
    {d : ℕ} (Ψ : (Fin d → ℝ) ≃L[ℝ] ComplexEuclidean n) (k : ℕ) :
    ContDiffOn ℝ 1 (sourceCoordinateForm Ψ (logTau f) k) ((Ψ ⁻¹' U) \ {0}) := by
  intro x hx
  have hn : Ψ x ≠ 0 := by
    intro hz
    have : x = 0 := Ψ.injective (by simpa using hz)
    exact hx.2 (by simpa using this)
  exact (contDiffAt_sourceCoordinateForm Ψ (h.contDiffAt_logTau hx.1 hn 3) k).contDiffWithinAt

/-- The level equation holds on the open chart-face domain;
this theorem applies the full R^(-(k+1)) law to the real Stokes form. -/
theorem sourceCoordinateForm_regular_face {d : ℕ}
    (h : MassHypotheses n N m U f G)
    (Ψ : (Fin (d+1) → ℝ) ≃L[ℝ] ComplexEuclidean n)
    (p : MahlerStokes.RegularBoundaryPatch (d+1) (Ψ ⁻¹' U) (fun x => tau f (Ψ x)))
    {R : ℝ} (hR : 0 < R) {y : Fin d → ℝ} (hy : y ∈ p.faceDomain R) (k : ℕ) :
    MahlerStokes.pullbackForm (p.faceParam R) (sourceCoordinateForm Ψ (logTau f) k) y =
      (R⁻¹)^(k+1) •
        MahlerStokes.pullbackForm (p.faceParam R) (sourceCoordinateForm Ψ (energy f) k) y := by
  have hd := Ψ.hasFDerivAt.comp y
    ((p.contDiffAt_faceParam R hy).differentiableAt (by norm_num)).hasFDerivAt
  change HasFDerivAt (fun z => Ψ (p.faceParam R z)) _ y at hd
  have hs := sourceBoundaryForm_regular_face h Ψ p hR hy k
  rw [hd.fderiv] at hs
  ext v
  have he := congrArg (fun a => (a (fun s => v (sourceBoundarySlots k s))).re) hs
  simpa only [MahlerStokes.pullbackForm, sourceCoordinateForm, sourceRealBoundaryForm_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousLinearMap.comp_apply, Function.comp_def, continuousSourceBoundaryForm_apply, ContinuousLinearMap.coe_coe,
    AlternatingMap.compLinearMap_apply, AlternatingMap.smul_apply, ← Complex.ofReal_inv,
    ← Complex.ofReal_pow, Complex.real_smul, smul_eq_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using he

end
end Mahler

end OAI
