import OAI.Analysis.Mahler.ReferenceSphere
import OAI.Analysis.Mahler.OpenExteriorNormalization
import OAI.Analysis.Mahler.LevelFace
import OAI.Analysis.Mahler.ComplexCoordinates

namespace OAI

open Complex ContinuousAlternatingMap Set Filter
open scoped Topology

namespace Mahler
noncomputable section
variable {n N m : ℕ} {U : Set (ComplexEuclidean n)}
  {f : Fin N → ComplexEuclidean n → ℂ} {G : Fin N → MvPolynomial (Fin n) ℂ}

/-- Smoothness of the literal energy, at any finite order, is derived from
first-order holomorphicity on the open source domain. -/
theorem MassHypotheses.contDiffAt_energy (h : MassHypotheses n N m U f G)
    {x : ComplexEuclidean n} (hx : x ∈ U) (r : ℕ) :
    ContDiffAt ℝ r (energy f) x := by
  apply ContDiffAt.sum
  intro j _
  have hj : ContDiffAt ℝ r (f j) x :=
    ((contDiffOn_nat_of_differentiableOn_open h.open_domain r (h.holomorphic j)).contDiffAt
      (h.open_domain.mem_nhds hx)).restrict_scalars ℝ
  exact (Complex.conjCLE.contDiff.contDiffAt.comp x hj).mul hj

theorem MassHypotheses.tau_pos (h : MassHypotheses n N m U f G)
    {x : ComplexEuclidean n} (hx : x ∈ U) (hne : x ≠ 0) : 0 < tau f x := by
  have hnot : ¬∀ j, f j x = 0 := fun hz => hne ((h.isolated_zero x hx).mp hz)
  obtain ⟨j, hj⟩ := not_forall.mp hnot
  exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
    ⟨j, Finset.mem_univ j, Complex.normSq_pos.mpr hj⟩

theorem MassHypotheses.contDiffAt_logTau (h : MassHypotheses n N m U f G)
    {x : ComplexEuclidean n} (hx : x ∈ U) (hne : x ≠ 0) (r : ℕ) :
    ContDiffAt ℝ r (logTau f) x := by
  rw [logTau_eq]
  exact ((Complex.contDiffAt_log (x := energy f x) (n := r) (by
    rw [energy_eq_tau]; exact Complex.ofReal_mem_slitPlane.mpr (h.tau_pos hx hne))).restrict_scalars ℝ).comp x
    (h.contDiffAt_energy hx r)

/-- The finite shuffle form used in both Stokes equations. -/
def sourceBoundaryForm (u : ComplexEuclidean n → ℂ) (k : ℕ) (x : ComplexEuclidean n) :
    ComplexEuclidean n [⋀^Fin 1 ⊕ WedgePowerSlots k]→ₗ[ℝ] ℂ :=
  wedge (oneForm (dcLinear u) x).toAlternatingMap
    (wedgePower (extDeriv (oneForm (dcLinear u)) x).toAlternatingMap k)

/-- Full scaling on any parametrization of a positive level.
The tangent condition follows by differentiating its level equation. -/
theorem sourceBoundaryForm_level_pullback {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {φ : V → ComplexEuclidean n} {y : V} {R : ℝ}
    (h : MassHypotheses n N m U f G) (hR : 0 < R) (hx : φ y ∈ U)
    (hφ : DifferentiableAt ℝ φ y)
    (hlevel : (fun z => tau f (φ z)) =ᶠ[𝓝 y] (fun _ => R)) (k : ℕ) :
    (sourceBoundaryForm (logTau f) k (φ y)).compLinearMap (fderiv ℝ φ y).toLinearMap =
      ((R : ℂ)⁻¹)^(k+1) •
        (sourceBoundaryForm (energy f) k (φ y)).compLinearMap (fderiv ℝ φ y).toLinearMap := by
  have hval : tau f (φ y) = R := hlevel.self_of_nhds
  have he : (energy f ∘ φ) =ᶠ[𝓝 y] (fun _ => (R : ℂ)) := by
    filter_upwards [hlevel] with z hz
    simp [energy_eq_tau, hz]
  have hd := (h.contDiffAt_energy hx 1).differentiableAt (by simp)
  have hz := congrArg (fun L : V →L[ℝ] ℂ => L)
    ((hd.hasFDerivAt.comp y hφ.hasFDerivAt).fderiv.symm.trans he.fderiv_eq)
  rw [(hasFDerivAt_const (R : ℂ) y).fderiv] at hz
  let S := LinearMap.range (fderiv ℝ φ y).toLinearMap
  have ht (v : S) : fderiv ℝ (energy f) (φ y) v = 0 := by
    obtain ⟨w, hw⟩ := v.property
    change (fderiv ℝ φ y) w = (v : ComplexEuclidean n) at hw
    have hv := congrArg (fun L : V →L[ℝ] ℂ => L w) hz
    change fderiv ℝ (energy f) (φ y) ((fderiv ℝ φ y) w) = 0 at hv
    rw [hw] at hv
    exact hv
  have hs := level_boundaryForm_scaling h.open_domain hx h.holomorphic
    (hval.symm ▸ hR) S ht k
  have hs' : (sourceBoundaryForm (logTau f) k (φ y)).compLinearMap S.subtype =
      ((R : ℂ)⁻¹)^(k+1) •
        (sourceBoundaryForm (energy f) k (φ y)).compLinearMap S.subtype := by
    unfold sourceBoundaryForm
    simp only [wedge_compLinearMap, wedgePower_compLinearMap]
    simpa only [energy_eq_tau, hval] using hs
  have htup (v : Fin 1 ⊕ WedgePowerSlots k → V) :
      ∀ i, (fderiv ℝ φ y) (v i) ∈ S := fun i => ⟨v i, rfl⟩
  ext v
  have hv := congrArg (fun a => a (fun i => (⟨(fderiv ℝ φ y) (v i), htup v i⟩ : S))) hs'
  exact hv

/-- Instantiation on the actual regular boundary charts constructed by Stokes. -/
theorem sourceBoundaryForm_regular_face {d : ℕ}
    (h : MassHypotheses n N m U f G)
    (Ψ : (Fin (d+1) → ℝ) ≃L[ℝ] ComplexEuclidean n)
    (p : MahlerStokes.RegularBoundaryPatch (d+1) (Ψ ⁻¹' U) (fun x => tau f (Ψ x)))
    {R : ℝ} (hR : 0 < R) {y : Fin d → ℝ} (hy : y ∈ p.faceDomain R) (k : ℕ) :
    (sourceBoundaryForm (logTau f) k (Ψ (p.faceParam R y))).compLinearMap
      (fderiv ℝ (fun z => Ψ (p.faceParam R z)) y).toLinearMap =
      ((R : ℂ)⁻¹)^(k+1) •
        (sourceBoundaryForm (energy f) k (Ψ (p.faceParam R y))).compLinearMap
          (fderiv ℝ (fun z => Ψ (p.faceParam R z)) y).toLinearMap := by
  have hφ : DifferentiableAt ℝ (fun z => Ψ (p.faceParam R z)) y :=
    Ψ.differentiableAt.comp y
      ((p.contDiffAt_faceParam R hy).differentiableAt (by norm_num))
  have he : (fun z => tau f (Ψ (p.faceParam R z))) =ᶠ[𝓝 y] (fun _ => R) := by
    filter_upwards [(p.isOpen_faceDomain R).mem_nhds hy] with z hz
    exact p.level_faceParam R hz
  exact sourceBoundaryForm_level_pullback (φ := fun z => Ψ (p.faceParam R z))
    (y := y) h hR (p.domain_U (p.faceParam_mem R hy)) hφ he k

/-- The existing Stokes coordinates carry the wedge slots to the exact
positive interleaved frame used by the Hessian normalization. -/
theorem complexCoordinates_wedge_basis (s : WedgePowerSlots n) :
    MahlerStokes.complexCoordinates n
      (MahlerStokes.coordinateBasis (n*2) (finProdFinEquiv (pairSlotEquiv n s))) =
      interleavedBasis s := by
  exact MahlerStokes.complexCoordinates_basis n (pairSlotEquiv n s).1 (pairSlotEquiv n s).2

/-- Actual logarithmic top-form density is nonnegative in the positive
Stokes coordinate frame, with no positivity assumption. -/
theorem source_log_top_coefficient_nonneg (h : MassHypotheses n N m U f G)
    {x : ComplexEuclidean n} (hx : x ∈ U) (hne : x ≠ 0) :
    0 ≤ (wedgePower (extDeriv (oneForm (dcLinear (logTau f))) x).toAlternatingMap n
      (fun s => MahlerStokes.complexCoordinates n
        (MahlerStokes.coordinateBasis (n*2) (finProdFinEquiv (pairSlotEquiv n s))))).re := by
  simp only [complexCoordinates_wedge_basis]
  rw [extDeriv_logTau_top_of_open h.open_domain hx h.holomorphic (h.tau_pos hx hne)]
  simp only [AlternatingMap.smul_apply, smul_eq_mul, interleavedVolume_basis, mul_one,
    Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  exact mul_nonneg (Nat.cast_nonneg _) (Complex.nonneg_iff.mp
    (sourceHessian_logTau_det_nonneg_of_open coordinateDirection h.open_domain hx h.holomorphic
      (h.tau_pos hx hne))).1

/-- The mass coefficient in Stokes coordinates, with scale one. -/
theorem source_massDensity_coordinate_coefficient (h : MassHypotheses n N m U f G)
    {x : ComplexEuclidean n} (hx : x ∈ U) :
    massDensity f x =
      (wedgePower (extDeriv (oneForm (dcLinear (energy f))) x).toAlternatingMap n
        (fun s => MahlerStokes.complexCoordinates n
          (MahlerStokes.coordinateBasis (n*2) (finProdFinEquiv (pairSlotEquiv n s))))).re := by
  simp only [complexCoordinates_wedge_basis]
  exact h.massDensity_eq_topForm hx

end
end Mahler

end OAI
