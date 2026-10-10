import OAI.Analysis.Mahler.HomogeneousDensityVariation

namespace OAI

open Complex

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- The required local smoothness follows from the literal holomorphic data,
for every finite order, wherever tau is positive. -/
lemma contDiffAt_logTau_order [FiniteDimensional ℂ E]
    {ι : Type*} [Fintype ι] {f : ι → E → ℂ} {U : Set E} {x : E}
    (q : ℕ) (hU : IsOpen U) (hx : x ∈ U)
    (hf : ∀ j, DifferentiableOn ℂ (f j) U) (ht : 0 < tau f x) :
    ContDiffAt ℝ q (logTau f) x := by
  have hc (j : ι) : ContDiffAt ℝ q (f j) x :=
    ((contDiffOn_nat_of_differentiableOn_open hU q (hf j)).contDiffAt
      (hU.mem_nhds hx)).restrict_scalars ℝ
  have he : ContDiffAt ℝ q (energy f) x := by
    apply ContDiffAt.sum
    intro j hj
    exact (Complex.conjCLE.contDiff.contDiffAt.comp x (hc j)).mul (hc j)
  rw [logTau_eq]
  exact ((Complex.contDiffAt_log (x := energy f x) (n := q) (by
    rw [energy_eq_tau]; exact Complex.ofReal_mem_slitPlane.mpr ht)).restrict_scalars ℝ).comp x he

lemma contDiffAt_dcLinear_order {u : E → ℂ} {x : E} (q : ℕ)
    (hu : ContDiffAt ℝ (q+1) u x) : ContDiffAt ℝ q (dcLinear u) x := by
  have hd : ContDiffAt ℝ q (fderiv ℝ u) x := hu.fderiv_right (by norm_cast)
  exact (hd.clm_comp contDiffAt_const).const_smul (-1 / 4 : ℂ)

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
lemma contDiffAt_oneForm_order [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] {a : E → E →L[ℝ] ℂ} {x : E} (q : ℕ)
    (ha : ContDiffAt ℝ q a x) : ContDiffAt ℝ q (oneForm a) x :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℂ) (0 : Fin 1)).toContinuousLinearEquiv.contDiff.contDiffAt.comp x ha

theorem MassHypotheses.alpha_beta_contDiffAt {n N m : ℕ}
    {U : Set (ComplexEuclidean n)} {f : Fin N → ComplexEuclidean n → ℂ}
    {G : Fin N → MvPolynomial (Fin n) ℂ} (h : MassHypotheses n N m U f G)
    {z : ComplexEuclidean n} (hz : z ≠ 0) (t : ℝ) (q : ℕ) :
    ContDiffAt ℝ q (alphaPath (polynomialMap G) (coordinateMap n) m t) z ∧
    ContDiffAt ℝ q (betaLinear (polynomialMap G) (coordinateMap n) m) z := by
  have hg := contDiffAt_dcLinear_order q (contDiffAt_logTau_order (q+1)
    isOpen_univ (Set.mem_univ z)
    (fun j => (polynomialMap_differentiable G j).differentiableOn)
    (tau_pos_of_component_ne_zero (h.leading_nonzero z hz)))
  have h0 := contDiffAt_dcLinear_order q (contDiffAt_logTau_order (q+1)
    isOpen_univ (Set.mem_univ z)
    (fun j => (coordinateMap_differentiable n j).differentiableOn)
    (coordinateMap_tau_pos hz))
  have hb := hg.sub (h0.const_smul (m : ℝ))
  exact ⟨(h0.const_smul (m : ℝ)).add (hb.const_smul t), hb⟩

/-- The d squared term vanishes along the homogeneous path; no
closedness or higher smoothness premise is added. -/
theorem MassHypotheses.alphaPath_extDeriv_extDeriv {n N m : ℕ}
    {U : Set (ComplexEuclidean n)} {f : Fin N → ComplexEuclidean n → ℂ}
    {G : Fin N → MvPolynomial (Fin n) ℂ} (h : MassHypotheses n N m U f G)
    {z : ComplexEuclidean n} (hz : z ≠ 0) (t : ℝ) :
    extDeriv (extDeriv (oneForm (alphaPath (polynomialMap G) (coordinateMap n) m t))) z = 0 := by
  apply extDeriv_extDeriv_apply
    (contDiffAt_oneForm_order 2 (h.alpha_beta_contDiffAt hz t 2).1)
  norm_num

end Mahler

end OAI
