import OAI.Geometry.EinsteinFour.ScalarPoissonKernelBesselEstimate
import Mathlib.Analysis.Normed.Ring.Units

namespace OAI

/-! A quantitative small-coefficient inverse on L2, with its actual
second-order distributional equation and H2 regularity. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap ENNReal BigOperators

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "L2" => Lp ℂ 2 (volume : Measure V)
local notation "Linf" => Lp ℂ ∞ (volume : Measure V)

/-- Physical multiplication by an essentially bounded coefficient. -/
def scalarL2Multiply (a : Linf) : L2 →L[ℂ] L2 :=
  LinearMap.mkContinuous
    { toFun := fun f => a • f
      map_add' := fun f g => Lp.add_smul a f g
      map_smul' := fun c f => by
        rw [← Lp.smul_comm]
        rfl }
    ‖a‖ (fun f => Lp.norm_smul_le a f)

theorem scalarL2Multiply_norm (a : Linf) (f : L2) :
    ‖scalarL2Multiply a f‖ ≤ ‖a‖ * ‖f‖ := Lp.norm_smul_le a f

theorem scalarL2Multiply_distribution (a : V → ℂ) (ha : a.HasTemperateGrowth)
    (haLp : MemLp a ∞ (volume : Measure V)) (f : L2) :
    (scalarL2Multiply (haLp.toLp a) f : 𝓢'(V, ℂ)) =
      smulLeftCLM ℂ a (f : 𝓢'(V, ℂ)) :=
  Lp.toTemperedDistribution_smul_eq ha haLp f

/-- The lower-order perturbation after composing on the right with Bessel(-2). -/
def scalarL2Perturbation (a : Fin 4 → Fin 4 → Linf) (b : Fin 4 → Linf) : L2 →L[ℂ] L2 :=
  (∑ i : Fin 4, ∑ j : Fin 4,
    (scalarL2Multiply (a i j)).comp (scalarBesselSecondL2 i j)) +
  ∑ i : Fin 4, (scalarL2Multiply (b i)).comp (scalarBesselFirstL2 i)

theorem scalarL2Perturbation_apply (a : Fin 4 → Fin 4 → Linf) (b : Fin 4 → Linf)
    (f : L2) :
    scalarL2Perturbation a b f =
      (∑ i : Fin 4, ∑ j : Fin 4, scalarL2Multiply (a i j) (scalarBesselSecondL2 i j f)) +
      ∑ i : Fin 4, scalarL2Multiply (b i) (scalarBesselFirstL2 i f) := by
  simp only [scalarL2Perturbation, add_apply, sum_apply, ContinuousLinearMap.comp_apply]

/-- Sixteen second-order terms and four first-order terms, with exact Fourier factors. -/
theorem scalarL2Perturbation_bound (a : Fin 4 → Fin 4 → Linf) (b : Fin 4 → Linf)
    (δ : ℝ) (ha : ∀ i j, ‖a i j‖ ≤ δ) (hb : ∀ i, ‖b i‖ ≤ δ) (f : L2) :
    ‖scalarL2Perturbation a b f‖ ≤
      (16 * (2 * Real.pi) ^ 2 * δ + 4 * (2 * Real.pi) * δ) * ‖f‖ := by
  have hδ : 0 ≤ δ := (norm_nonneg (b 0)).trans (hb 0)
  have hsecond (i j : Fin 4) :
      ‖scalarL2Multiply (a i j) (scalarBesselSecondL2 i j f)‖ ≤
        δ * ((2 * Real.pi) ^ 2 * ‖f‖) := by
    exact (scalarL2Multiply_norm _ _).trans
      (mul_le_mul (ha i j) (scalarBesselSecondL2_norm i j f) (norm_nonneg _) hδ)
  have hfirst (i : Fin 4) :
      ‖scalarL2Multiply (b i) (scalarBesselFirstL2 i f)‖ ≤
        δ * ((2 * Real.pi) * ‖f‖) := by
    exact (scalarL2Multiply_norm _ _).trans
      (mul_le_mul (hb i) (scalarBesselFirstL2_norm i f) (norm_nonneg _) hδ)
  rw [scalarL2Perturbation_apply]
  calc
    _ ≤ (∑ i : Fin 4, ∑ j : Fin 4,
        ‖scalarL2Multiply (a i j) (scalarBesselSecondL2 i j f)‖) +
        ∑ i : Fin 4, ‖scalarL2Multiply (b i) (scalarBesselFirstL2 i f)‖ := by
      apply (norm_add_le _ _).trans
      apply add_le_add
      · exact (norm_sum_le _ _).trans
          (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
      · exact norm_sum_le _ _
    _ ≤ (∑ _i : Fin 4, ∑ _j : Fin 4, δ * ((2 * Real.pi) ^ 2 * ‖f‖)) +
        ∑ _i : Fin 4, δ * ((2 * Real.pi) * ‖f‖) := by
      apply add_le_add
      · exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hsecond i j))
      · exact Finset.sum_le_sum (fun i _ => hfirst i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem scalarL2Perturbation_opNorm (a : Fin 4 → Fin 4 → Linf) (b : Fin 4 → Linf)
    (δ : ℝ) (ha : ∀ i j, ‖a i j‖ ≤ δ) (hb : ∀ i, ‖b i‖ ≤ δ) :
    ‖scalarL2Perturbation a b‖ ≤ 16 * (2 * Real.pi) ^ 2 * δ + 4 * (2 * Real.pi) * δ := by
  apply ContinuousLinearMap.opNorm_le_bound
  · have hδ : 0 ≤ δ := (norm_nonneg (b 0)).trans (hb 0)
    positivity
  · exact scalarL2Perturbation_bound a b δ ha hb

/-- Neumann inversion of `Id + K` in the actual Banach space. -/
def scalarPerturbationEquiv (K : L2 →L[ℂ] L2) (hK : ‖K‖ < 1) : L2 ≃L[ℂ] L2 :=
  ContinuousLinearEquiv.unitsEquiv ℂ L2 (Units.oneSub (-K) (by simpa only [norm_neg] using hK))

theorem scalarPerturbationEquiv_apply (K : L2 →L[ℂ] L2) (hK : ‖K‖ < 1) (f : L2) :
    scalarPerturbationEquiv K hK f = f + K f := by
  change ((1 - -K : L2 →L[ℂ] L2) f) = _
  simp only [sub_neg_eq_add, add_apply, one_apply_eq_self]

/-- An L2 right-hand side has a unique transformed unknown for small coefficients. -/
theorem scalarL2Perturbation_existsUnique (a : Fin 4 → Fin 4 → Linf) (b : Fin 4 → Linf)
    (δ : ℝ) (ha : ∀ i j, ‖a i j‖ ≤ δ) (hb : ∀ i, ‖b i‖ ≤ δ)
    (hsmall : 16 * (2 * Real.pi) ^ 2 * δ + 4 * (2 * Real.pi) * δ < 1) (f : L2) :
    ∃! v : L2, v + scalarL2Perturbation a b v = f := by
  let hK := (scalarL2Perturbation_opNorm a b δ ha hb).trans_lt hsmall
  let e := scalarPerturbationEquiv (scalarL2Perturbation a b) hK
  have he (v : L2) : e v = v + scalarL2Perturbation a b v :=
    scalarPerturbationEquiv_apply _ hK v
  refine ⟨e.symm f, ?_, ?_⟩
  · exact (he (e.symm f)).symm.trans (e.apply_symm_apply f)
  · intro v hv
    apply e.injective
    rw [e.apply_symm_apply, he]
    exact hv

private theorem scalarCoefficient_memLp (a : V → ℂ) (ha : a.HasTemperateGrowth)
    (δ : ℝ) (hb : ∀ x, ‖a x‖ ≤ δ) : MemLp a ∞ (volume : Measure V) :=
  memLp_top_of_bound ha.1.continuous.aestronglyMeasurable δ (.of_forall hb)

private theorem scalarCoefficient_Linf_bound (a : V → ℂ) (ha : MemLp a ∞ (volume : Measure V))
    (δ : ℝ) (hb : ∀ x, ‖a x‖ ≤ δ) : ‖ha.toLp a‖ ≤ δ := by
  have hδ : 0 ≤ δ := (norm_nonneg (a 0)).trans (hb 0)
  rw [Lp.norm_toLp, eLpNorm_exponent_top ha.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hδ
    (eLpNormEssSup_le_of_ae_bound (.of_forall hb))

private theorem scalarL2Perturbation_distribution
    (a : Fin 4 → Fin 4 → V → ℂ) (b : Fin 4 → V → ℂ)
    (ha : ∀ i j, (a i j).HasTemperateGrowth) (hb : ∀ i, (b i).HasTemperateGrowth)
    (haLp : ∀ i j, MemLp (a i j) ∞ (volume : Measure V))
    (hbLp : ∀ i, MemLp (b i) ∞ (volume : Measure V)) (f : L2) :
    (scalarL2Perturbation (fun i j => (haLp i j).toLp _) (fun i => (hbLp i).toLp _) f :
        𝓢'(V, ℂ)) =
      (∑ i : Fin 4, ∑ j : Fin 4, smulLeftCLM ℂ (a i j)
        (scalarCoordinateDerivative i
          (scalarCoordinateDerivative j (scalarBesselInverseL2 f : 𝓢'(V, ℂ))))) +
      ∑ i : Fin 4, smulLeftCLM ℂ (b i)
        (scalarCoordinateDerivative i (scalarBesselInverseL2 f : 𝓢'(V, ℂ))) := by
  have hsecond (i j : Fin 4) :
      (scalarL2Multiply ((haLp i j).toLp _) (scalarBesselSecondL2 i j f) : 𝓢'(V, ℂ)) =
        smulLeftCLM ℂ (a i j) (scalarCoordinateDerivative i
          (scalarCoordinateDerivative j (scalarBesselInverseL2 f : 𝓢'(V, ℂ)))) := by
    rw [scalarL2Multiply_distribution _ (ha i j), scalarBesselSecondL2_distribution]
  have hfirst (i : Fin 4) :
      (scalarL2Multiply ((hbLp i).toLp _) (scalarBesselFirstL2 i f) : 𝓢'(V, ℂ)) =
        smulLeftCLM ℂ (b i) (scalarCoordinateDerivative i
          (scalarBesselInverseL2 f : 𝓢'(V, ℂ))) := by
    rw [scalarL2Multiply_distribution _ (hb i), scalarBesselFirstL2_distribution]
  rw [scalarL2Perturbation_apply]
  change Lp.toTemperedDistributionCLM ℂ volume 2 _ = _
  simp only [map_add, map_sum, Lp.toTemperedDistributionCLM_apply, hsecond, hfirst]

/-- Small smooth bounded coefficients give a genuine H2 solution of the
perturbed distributional equation. No regularity of a prospective solution
is used in this construction. -/
theorem scalar_perturbedHelmholtz_solution
    (a : Fin 4 → Fin 4 → V → ℂ) (b : Fin 4 → V → ℂ)
    (ha : ∀ i j, (a i j).HasTemperateGrowth) (hb : ∀ i, (b i).HasTemperateGrowth)
    (δ : ℝ) (haBound : ∀ i j x, ‖a i j x‖ ≤ δ) (hbBound : ∀ i x, ‖b i x‖ ≤ δ)
    (hsmall : 16 * (2 * Real.pi) ^ 2 * δ + 4 * (2 * Real.pi) * δ < 1) (f : L2) :
    ∃ u : L2, MemSobolev 2 2 (u : 𝓢'(V, ℂ)) ∧
      normalizedScalarHelmholtz (u : 𝓢'(V, ℂ)) +
        (∑ i : Fin 4, ∑ j : Fin 4, smulLeftCLM ℂ (a i j)
          (scalarCoordinateDerivative i (scalarCoordinateDerivative j (u : 𝓢'(V, ℂ))))) +
        (∑ i : Fin 4, smulLeftCLM ℂ (b i)
          (scalarCoordinateDerivative i (u : 𝓢'(V, ℂ)))) = (f : 𝓢'(V, ℂ)) := by
  let haLp := fun i j => scalarCoefficient_memLp (a i j) (ha i j) δ (haBound i j)
  let hbLp := fun i => scalarCoefficient_memLp (b i) (hb i) δ (hbBound i)
  obtain ⟨v, hv, _⟩ := scalarL2Perturbation_existsUnique
    (fun i j => (haLp i j).toLp _) (fun i => (hbLp i).toLp _) δ
    (fun i j => scalarCoefficient_Linf_bound _ _ δ (haBound i j))
    (fun i => scalarCoefficient_Linf_bound _ _ δ (hbBound i)) hsmall f
  refine ⟨scalarBesselInverseL2 v, scalarBesselInverseL2_memSobolev v, ?_⟩
  have h := congrArg (Lp.toTemperedDistributionCLM ℂ volume 2) hv
  rw [map_add, Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistributionCLM_apply,
    Lp.toTemperedDistributionCLM_apply,
    scalarL2Perturbation_distribution a b ha hb haLp hbLp v] at h
  rw [scalarBesselInverseL2_helmholtz, add_assoc]
  exact h

end
end PositiveEinsteinFour.Geometry

end OAI
