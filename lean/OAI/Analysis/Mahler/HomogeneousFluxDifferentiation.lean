import OAI.Analysis.Mahler.SphereFluxDifferentiation
import OAI.Analysis.Mahler.HomogeneousDensityVariation
import OAI.Analysis.Mahler.BoundaryJet

namespace OAI

open Complex MeasureTheory Metric Set Filter ContinuousAlternatingMap
open scoped Topology BigOperators

namespace Mahler

lemma contDiffAt_dcLinear_one {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    {u : E → ℂ} {x : E} (hu : ContDiffAt ℝ 2 u x) :
    ContDiffAt ℝ 1 (dcLinear u) x := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ u) x := hu.fderiv_right (by norm_num)
  exact (hd.clm_comp contDiffAt_const).const_smul (-1 / 4 : ℂ)

lemma continuous_sphere_oneForm {k : ℕ}
    {a : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) →L[ℝ] ℂ}
    (ha : ∀ x : sphere (0 : ComplexEuclidean (k+1)) 1, ContDiffAt ℝ 1 a x) :
    Continuous (fun x : sphere (0 : ComplexEuclidean (k+1)) 1 => a x) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (ha x).continuousAt.comp continuous_subtype_val.continuousAt

lemma continuous_sphere_extDeriv {k : ℕ}
    {a : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) →L[ℝ] ℂ}
    (ha : ∀ x : sphere (0 : ComplexEuclidean (k+1)) 1, ContDiffAt ℝ 1 a x) :
    Continuous (fun x : sphere (0 : ComplexEuclidean (k+1)) 1 => extDeriv (oneForm a) x) := by
  rw [continuous_iff_continuousAt]
  intro x
  have ho : ContDiffAt ℝ 1 (oneForm a) (x : ComplexEuclidean (k+1)) :=
    (ofSubsingletonLIE (𝕜 := ℝ) (E := ComplexEuclidean (k+1)) (F := ℂ)
      (0 : Fin 1)).toContinuousLinearEquiv.contDiff.contDiffAt.comp (x : ComplexEuclidean (k+1)) (ha x)
  have hf : ContDiffAt ℝ 0 (fderiv ℝ (oneForm a)) (x : ComplexEuclidean (k+1)) :=
    ho.fderiv_right (by norm_num)
  exact ((alternatizeUncurryFinCLM ℝ (ComplexEuclidean (k+1)) ℂ).continuous.continuousAt.comp
    hf.continuousAt).comp continuous_subtype_val.continuousAt

lemma continuous_sphere_affine_oneForm_eval {k : ℕ}
    {a b : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) →L[ℝ] ℂ}
    (ha : ∀ x : sphere (0 : ComplexEuclidean (k+1)) 1, ContDiffAt ℝ 1 a x)
    (hb : ∀ x : sphere (0 : ComplexEuclidean (k+1)) 1, ContDiffAt ℝ 1 b x)
    (v : Fin 1 → ComplexEuclidean (k+1)) :
    Continuous (fun p : ℝ × sphere (0 : ComplexEuclidean (k+1)) 1 =>
      oneForm (a + p.1 • b) p.2 v) := by
  change Continuous (fun p : ℝ × sphere (0 : ComplexEuclidean (k+1)) 1 =>
    a p.2 (v 0) + p.1 • b p.2 (v 0))
  exact ((continuous_sphere_oneForm ha).comp continuous_snd).clm_apply continuous_const |>.add
    (continuous_fst.smul (((continuous_sphere_oneForm hb).comp continuous_snd).clm_apply continuous_const))

lemma continuous_sphere_affine_extDeriv_eval {k : ℕ}
    {a b : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) →L[ℝ] ℂ}
    (ha : ∀ x : sphere (0 : ComplexEuclidean (k+1)) 1, ContDiffAt ℝ 1 a x)
    (hb : ∀ x : sphere (0 : ComplexEuclidean (k+1)) 1, ContDiffAt ℝ 1 b x)
    (v : Fin 2 → ComplexEuclidean (k+1)) :
    Continuous (fun p : ℝ × sphere (0 : ComplexEuclidean (k+1)) 1 =>
      extDeriv (oneForm (a + p.1 • b)) p.2 v) := by
  have he (p : ℝ × sphere (0 : ComplexEuclidean (k+1)) 1) :
      extDeriv (oneForm (a + p.1 • b)) p.2 v =
        extDeriv (oneForm a) p.2 v + p.1 • extDeriv (oneForm b) p.2 v := by
    rw [extDeriv_oneForm_affine ((ha p.2).differentiableAt (by norm_num))
      ((hb p.2).differentiableAt (by norm_num))]
    rfl
  simp_rw [he]
  exact ((continuous_eval_const v).comp ((continuous_sphere_extDeriv ha).comp continuous_snd)).add
    (continuous_fst.smul ((continuous_eval_const v).comp
      ((continuous_sphere_extDeriv hb).comp continuous_snd)))

lemma continuous_wedgePowerVariation_eval {E X : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [TopologicalSpace X] {a b : X → E [⋀^Fin 2]→ₗ[ℝ] ℂ}
    (ha : ∀ v, Continuous (fun p => a p v))
    (hb : ∀ v, Continuous (fun p => b p v)) (k : ℕ)
    (v : WedgePowerSlots k → E) :
    Continuous (fun p => wedgePowerVariation (a p) (b p) k v) := by
  induction k with
  | zero => exact continuous_const
  | succ k ih =>
    exact (continuous_wedge_eval hb (continuous_wedgePower_eval ha k) _).add
      (continuous_wedge_eval ha ih _)

lemma continuous_sphere_affine_boundary_eval {k : ℕ}
    {a b : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) →L[ℝ] ℂ}
    (ha : ∀ x : sphere (0 : ComplexEuclidean (k+1)) 1, ContDiffAt ℝ 1 a x)
    (hb : ∀ x : sphere (0 : ComplexEuclidean (k+1)) 1, ContDiffAt ℝ 1 b x)
    (v : Fin (2*k+1) → ComplexEuclidean (k+1)) :
    Continuous (fun p : ℝ × sphere (0 : ComplexEuclidean (k+1)) 1 =>
      boundaryFormFin (a + p.1 • b) p.2 v) := by
  unfold boundaryFormFin
  simp only [AlternatingMap.domDomCongr_apply]
  apply continuous_wedge_eval
  · exact continuous_sphere_affine_oneForm_eval ha hb
  · exact continuous_wedgePower_eval (continuous_sphere_affine_extDeriv_eval ha hb) k

lemma continuous_sphere_affine_residual_eval {k : ℕ}
    {a b : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) →L[ℝ] ℂ}
    (ha : ∀ x : sphere (0 : ComplexEuclidean (k+1)) 1, ContDiffAt ℝ 1 a x)
    (hb : ∀ x : sphere (0 : ComplexEuclidean (k+1)) 1, ContDiffAt ℝ 1 b x)
    (v : Fin (2*k+1) → ComplexEuclidean (k+1)) :
    Continuous (fun p : ℝ × sphere (0 : ComplexEuclidean (k+1)) 1 =>
      boundaryResidualFin (a + p.1 • b) b p.2 v) := by
  unfold boundaryResidualFin
  simp only [AlternatingMap.domDomCongr_apply]
  apply continuous_wedge_eval
  · exact continuous_sphere_affine_oneForm_eval ha hb
  · apply continuous_wedgePowerVariation_eval (continuous_sphere_affine_extDeriv_eval ha hb)
    intro w
    change Continuous (fun p : ℝ × sphere (0 : ComplexEuclidean (k+1)) 1 =>
      extDeriv (oneForm b) p.2 w)
    exact (continuous_eval_const w).comp ((continuous_sphere_extDeriv hb).comp continuous_snd)

lemma MassHypotheses.homogeneous_path_C1 {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+1))} {f : Fin N → ComplexEuclidean (k+1) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+1)) ℂ} (h : MassHypotheses (k+1) N m U f G) :
    (∀ x : sphere (0 : ComplexEuclidean (k+1)) 1,
      ContDiffAt ℝ 1 ((m : ℝ) • dcLinear (logTau (coordinateMap (k+1)))) x) ∧
    (∀ x : sphere (0 : ComplexEuclidean (k+1)) 1,
      ContDiffAt ℝ 1 (betaLinear (polynomialMap G) (coordinateMap (k+1)) m) x) := by
  have hg (x : sphere (0 : ComplexEuclidean (k+1)) 1) :
      ContDiffAt ℝ 1 (dcLinear (logTau (polynomialMap G))) (x : ComplexEuclidean (k+1)) := by
    have hx : (x : ComplexEuclidean (k+1)) ≠ 0 := by
      intro hx
      have := x.property
      simp [hx] at this
    exact contDiffAt_dcLinear_one (contDiffAt_logTau_of_open isOpen_univ (mem_univ _)
      (fun j => (polynomialMap_differentiable G j).differentiableOn)
      (tau_pos_of_component_ne_zero (h.leading_nonzero x hx)))
  have h0 (x : sphere (0 : ComplexEuclidean (k+1)) 1) :
      ContDiffAt ℝ 1 ((m : ℝ) • dcLinear (logTau (coordinateMap (k+1))))
        (x : ComplexEuclidean (k+1)) := by
    have hx : (x : ComplexEuclidean (k+1)) ≠ 0 := by
      intro hx
      have := x.property
      simp [hx] at this
    exact (contDiffAt_dcLinear_one (contDiffAt_logTau_of_open isOpen_univ (mem_univ _)
      (fun j => (coordinateMap_differentiable (k+1) j).differentiableOn)
      (coordinateMap_tau_pos hx))).const_smul (m : ℝ)
  exact ⟨h0, fun x => (hg x).sub (h0 x)⟩

/-- The homogeneous flux has the residual flux as derivative,
from the mass hypotheses. No integral regularity premise remains.
The residual integral is retained; this theorem does not assert it is zero. -/
theorem MassHypotheses.homogeneousPathFlux_hasDerivAt {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+1))} {f : Fin N → ComplexEuclidean (k+1) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+1)) ℂ} (h : MassHypotheses (k+1) N m U f G)
    (t : ℝ) :
    HasDerivAt (homogeneousPathFlux k N m G)
      (sphereFlux k (boundaryResidualFin
        (alphaPath (polynomialMap G) (coordinateMap (k+1)) m t)
        (betaLinear (polynomialMap G) (coordinateMap (k+1)) m))) t := by
  obtain ⟨ha, hb⟩ := h.homogeneous_path_C1
  unfold homogeneousPathFlux
  apply sphereFlux_hasDerivAt_of_density (a := t-1) (b := t+1)
    (D := fun s => boundaryResidualFin
      (alphaPath (polynomialMap G) (coordinateMap (k+1)) m s)
      (betaLinear (polynomialMap G) (coordinateMap (k+1)) m))
  · intro v
    exact (continuous_sphere_affine_boundary_eval ha hb v).continuousOn
  · intro v
    exact (continuous_sphere_affine_residual_eval ha hb v).continuousOn
  · intro s hs x
    exact h.sphere_density_derivative (by
      simpa only [mem_sphere_iff_norm, sub_zero] using x.property) s
  · constructor <;> linarith

end Mahler

end OAI
