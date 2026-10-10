import OAI.Geometry.SurfaceImmersion.Geometry.UnperturbedSolverScale
import OAI.Geometry.SurfaceImmersion.Correction.CompactModeCoefficients

namespace OAI

/-! Actual unperturbed solvers require only compact good-mode geometry. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates PhaseMean RealModes

/-- The exact-correction stage has no polynomial perturbation. -/
def emptyMetricPolynomial : Fin 3 → Fin 0 → Expression := fun _ => Fin.elim0

/-- Construct the unit-scale data from a good phase chart; no higher-jet
compactness assumption is needed for a polynomial term that is absent. -/
theorem geometric_unperturbed_solver
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (K : Compacts Base)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    (hKe : (modeSupport K : Set SmallModes.Base) ⊆ e.source)
    (hphase : ∀ x ∈ e.source, (e x).1 = coordinatePhase φ x)
    {KE KV Ω : Set SmallModes.Base}
    (hKE : IsCompact KE) (hKV : IsCompact KV)
    (hEK : e.source ⊆ KE) (hVK : e.target ⊆ KV) (hKVΩ : KV ⊆ Ω)
    (hdom : RealModeDomain ((G ∘ planeCoordinateIsometry.symm) ∘ e.symm) Ω) :
    ∃ c : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K 1 1,
      c.e = e ∧ (∀ m, c.D m = 0) := by
  have hmap : ContDiff ℝ ∞ ((G ∘ planeCoordinateIsometry.symm) ∘ e.symm) :=
    (hG.comp planeCoordinateIsometry.symm.contDiff).comp hi
  choose J hJ hj using fun m => compact_local_weighted_bound e.open_source isOpen_univ
    hKE hEK (subset_univ KE) he.contDiffOn m
  choose C hC hc using fun m => (hdom.complexDomain hmap).compact_reconstruction_bounds
    e.open_target hKV hVK hKVΩ (m+1)
  have hdomain : RealModeDomain ((G ∘ planeCoordinateIsometry.symm) ∘ e.symm) e.target :=
    ⟨e.open_target,fun x hx => hdom.determinant x (hKVΩ (hVK hx)),
      fun x hx => hdom.good x (hKVΩ (hVK hx))⟩
  have hP : ∀ k l, (emptyMetricPolynomial k l).SmoothCoeffs univ := fun _ l => Fin.elim0 l
  refine ⟨{
    U := univ
    O := univ
    openU := isOpen_univ
    openO := isOpen_univ
    smoothP := hP
    mapsG := mapsTo_univ _ _
    supportU := subset_univ _
    smoothPhase := hφ
    e := e
    smoothForward := he.contDiffOn
    smoothInverse := hi.contDiffOn
    supportChart := hKe
    phase := hphase
    smoothMap := hmap
    domain := hdomain.complexDomain hmap
    C := C
    D := fun _ => 0
    J := J
    nonnegC := fun m => zero_le_one.trans (hC m)
    nonnegD := fun _ => le_rfl
    oneLEJ := hJ
    coordinates := ?_
    coefficients := fun m => hc m 1 zero_lt_one le_rfl
    polynomial := ?_
  },rfl,fun _ => rfl⟩
  · intro m j _ hjm x hx
    simpa only [one_pow,one_mul] using hj m 1 zero_le_one le_rfl j hjm x hx
  · intro m Z
    rw [phaseChartPolynomialOperator_zero]
    simp

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
