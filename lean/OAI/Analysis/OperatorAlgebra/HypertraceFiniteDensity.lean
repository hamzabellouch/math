import OAI.Analysis.OperatorAlgebra.FinitePredualConjugation
import OAI.Analysis.TracialSplitting.Hypertraces

namespace OAI

/-! The convex separation step in the finite hypertrace argument.
An invariant state can be approximated on a prescribed finite set by finite
vector functionals whose conjugation defects are small in the predual norm.
This is norm control of the defects, not merely weak convergence. -/

noncomputable section
open scoped InnerProductSpace ComplexOrder ComplexStarModule
open Set

namespace WeakPureInfiniteness

variable {H I J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype I] [Fintype J]

abbrev HypertraceTestSpace (I J H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] :=
  (I → ℝ) × (J → finiteOperatorPredual (H := H))

instance hypertraceTestNormed : NormedAddCommGroup (HypertraceTestSpace I J H) :=
  inferInstance

instance hypertraceTestReal : NormedSpace ℝ (HypertraceTestSpace I J H) :=
  inferInstance

instance hypertraceTestBounded : IsBoundedSMul ℝ (HypertraceTestSpace I J H) :=
  NormedSpace.toIsBoundedSMul

instance hypertraceTestContinuousSMul : ContinuousSMul ℝ (HypertraceTestSpace I J H) :=
  IsBoundedSMul.continuousSMul

def hypertraceVectorTest (T : I → H →L[ℂ] H) (U : J → H ≃ₗᵢ[ℂ] H) (x : H) :
    HypertraceTestSpace I J H :=
  (fun i => (inner ℂ x (T i x)).re,
    fun j => finitePredualUnitary (U j) (finiteOperatorCoefficient x x) - finiteOperatorCoefficient x x)

def hypertraceStateTest (T : I → H →L[ℂ] H) (φ : (H →L[ℂ] H) →ₚ[ℂ] ℂ) :
    HypertraceTestSpace I J H := (fun i => (φ (T i)).re, 0)

private def testScalarPart (f : HypertraceTestSpace I J H →L[ℝ] ℝ) : (I → ℝ) →L[ℝ] ℝ :=
  f.comp (ContinuousLinearMap.inl ℝ _ _)

private def testPredualPart [DecidableEq J] (f : HypertraceTestSpace I J H →L[ℝ] ℝ)
    (j : J) : finiteOperatorPredual (H := H) →L[ℝ] ℝ :=
  (f.comp (ContinuousLinearMap.inr ℝ (I → ℝ) (J → finiteOperatorPredual (H := H)))).comp
    (ContinuousLinearMap.single ℝ (fun _ : J => finiteOperatorPredual (H := H)) j)

private lemma testFunctional_expansion [DecidableEq I] [DecidableEq J]
    (f : HypertraceTestSpace I J H →L[ℝ] ℝ) (s : I → ℝ) (z : J → finiteOperatorPredual (H := H)) :
    f (s, z) = (∑ i, testScalarPart f (Pi.single i 1) * s i) + ∑ j, testPredualPart f j (z j) := by
  have he : (s, z) = (s, 0) + (0, z) := by simp
  rw [he, map_add]
  congr 1
  · exact NuclearTrace.real_pi_linear_expansion (testScalarPart f) s
  · have hz : (0, z) = ∑ j, ((0, Pi.single j (z j)) : HypertraceTestSpace I J H) := by
      apply Prod.ext
      · simp only [Prod.fst_sum, Finset.sum_const_zero]
      · simpa only [Prod.snd_sum] using (Finset.univ_sum_single z).symm
    rw [hz, map_sum]
    rfl

private lemma operator_realPart_quadratic (T : H →L[ℂ] H) (x : H) :
    (inner ℂ x ((ℜ T : H →L[ℂ] H) x)).re = (inner ℂ x (T x)).re := by
  have hs : (inner ℂ x ((star T) x)).re = (inner ℂ x (T x)).re := by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
    exact inner_re_symm (𝕜 := ℂ) (T x) x
  rw [realPart_apply_coe]
  simp only [smul_apply, add_apply, inner_smul_right_eq_smul, inner_add_right,
    Complex.smul_re, Complex.add_re, smul_eq_mul, hs]
  ring

private lemma conjugatedOperator_inner (U : H ≃ₗᵢ[ℂ] H) (T : H →L[ℂ] H) (x : H) :
    inner ℂ x (conjugatedOperator U T x) = inner ℂ (U x) (T (U x)) := by
  change inner ℂ x (U.symm (T (U x))) = _
  rw [← U.inner_map_map x (U.symm (T (U x))), U.apply_symm_apply]

theorem hypertraceStateTest_mem_closure (T : I → H →L[ℂ] H)
    (hT : ∀ i, IsSelfAdjoint (T i)) (U : J → H ≃ₗᵢ[ℂ] H)
    (φ : (H →L[ℂ] H) →ₚ[ℂ] ℂ) (hφ : φ 1 = 1)
    (hU : ∀ j A, φ (conjugatedOperator (U j) A) = φ A) :
    hypertraceStateTest (J := J) T φ ∈
      closure (convexHull ℝ (hypertraceVectorTest T U '' Metric.closedBall 0 1)) := by
  classical
  by_contra hn
  obtain ⟨f, c, hf, hc⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (hypertraceVectorTest T U '' Metric.closedBall 0 1)).closure
      isClosed_closure hn
  choose A hA using fun j => finitePredual_real_duality (testPredualPart f j)
  let B (j : J) : H →L[ℂ] H := ℜ (A j)
  let S : H →L[ℂ] H :=
    (∑ i, testScalarPart f (Pi.single i 1) • T i) +
      ∑ j, (conjugatedOperator (U j) (B j) - B j)
  have hB (j : J) : IsSelfAdjoint (B j) := (ℜ (A j)).property
  have hS : IsSelfAdjoint S := by
    apply IsSelfAdjoint.add
    · exact isSelfAdjoint_sum _ fun i _ => (IsSelfAdjoint.all _).smul (hT i)
    · apply isSelfAdjoint_sum
      intro j _
      exact ((hB j).map (U j).symm.conjStarAlgEquiv).sub (hB j)
  have hquad (x : H) : f (hypertraceVectorTest T U x) = (inner ℂ x (S x)).re := by
    rw [testFunctional_expansion]
    simp only [hypertraceVectorTest, S, add_apply, sum_apply, inner_add_right,
      inner_sum, Complex.add_re, Complex.re_sum, smul_apply,
      inner_smul_right_eq_smul, Complex.smul_re, smul_eq_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [hA j]
    simp only [Submodule.coe_sub, sub_apply, finitePredualUnitary_apply,
      finiteOperatorCoefficient, operatorCoefficient_apply, conjugatedOperator_inner,
      inner_sub_right, Complex.sub_re, B, operator_realPart_quadratic]
  have hle : S ≤ c • (1 : H →L[ℂ] H) := NuclearTrace.operator_le_of_unit_quadratic hS (by
    intro x hx
    rw [← hquad]
    exact (hf _ (subset_closure (subset_convexHull ℝ _
      ⟨x, by simpa using hx, rfl⟩))).le)
  have heval : f (hypertraceStateTest (J := J) T φ) = (φ S).re := by
    rw [testFunctional_expansion]
    simp only [hypertraceStateTest, Pi.zero_apply, map_zero, Finset.sum_const_zero, add_zero]
    simp only [S, map_add, map_sum, φ.map_smul_of_tower, map_sub, hU,
      sub_self, Finset.sum_const_zero, add_zero, Complex.re_sum, Complex.smul_re, smul_eq_mul]
  have hb := (φ.monotone hle).1
  change (φ S).re ≤ (φ (c • 1)).re at hb
  rw [φ.map_smul_of_tower, hφ, Complex.smul_re, Complex.one_re, smul_eq_mul, mul_one] at hb
  exact (not_le_of_gt hc) (heval ▸ hb)

def finiteVectorDensity {n : ℕ} (w : Fin n → ℝ) (x : Fin n → H) :
    finiteOperatorPredual (H := H) :=
  ∑ k, (w k : ℂ) • finiteOperatorCoefficient (x k) (x k)

/-- Simultaneous finite state tests and norm-small conjugation defects.
This is the finite-rank density step used before the Powers--Størmer estimate. -/
theorem hypertrace_finite_density (T : I → H →L[ℂ] H)
    (hT : ∀ i, IsSelfAdjoint (T i)) (U : J → H ≃ₗᵢ[ℂ] H)
    (φ : (H →L[ℂ] H) →ₚ[ℂ] ℂ) (hφ : φ 1 = 1)
    (hU : ∀ j A, φ (conjugatedOperator (U j) A) = φ A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (w : Fin n → ℝ) (x : Fin n → H),
      (∀ k, 0 ≤ w k) ∧ (∑ k, w k = 1) ∧ (∀ k, ‖x k‖ ≤ 1) ∧
      (∀ i, |(φ (T i)).re - ∑ k, w k * (inner ℂ (x k) (T i (x k))).re| < ε) ∧
      ∀ j, ‖finitePredualUnitary (U j) (finiteVectorDensity w x) - finiteVectorDensity w x‖ < ε := by
  classical
  obtain ⟨z, hz, hzε⟩ := Metric.mem_closure_iff.mp
    (hypertraceStateTest_mem_closure T hT U φ hφ hU) ε hε
  obtain ⟨K, _, w, v, hw, hw1, hv, hsum⟩ := mem_convexHull_iff_exists_fintype.mp hz
  choose x hx hvx using hv
  let e : Fin (Fintype.card K) ≃ K := (Fintype.equivFin K).symm
  have hsum' : (∑ k : Fin (Fintype.card K), w (e k) • hypertraceVectorTest T U (x (e k))) = z := by
    rw [e.sum_comp (fun k => w k • hypertraceVectorTest T U (x k))]
    simpa only [← hvx] using hsum
  refine ⟨Fintype.card K, w ∘ e, x ∘ e, fun k => hw (e k),
    (e.sum_comp w).trans hw1, fun k => by simpa using hx (e k), ?_, ?_⟩
  · intro i
    have hb := ((norm_le_pi_norm ((hypertraceStateTest (J := J) T φ - z).1) i).trans
      (norm_fst_le (hypertraceStateTest (J := J) T φ - z))).trans_lt (by
        simpa only [dist_eq_norm] using hzε)
    have he : (∑ k : Fin (Fintype.card K), w (e k) *
        (inner ℂ (x (e k)) (T i (x (e k)))).re) = z.1 i := by
      simpa only [Prod.fst_sum, Finset.sum_apply, Prod.smul_fst, Pi.smul_apply,
        smul_eq_mul, hypertraceVectorTest] using
        congrArg (fun q : HypertraceTestSpace I J H => q.1 i) hsum'
    change ‖(φ (T i)).re - z.1 i‖ < ε at hb
    rw [← he] at hb
    simpa only [Function.comp_apply, Real.norm_eq_abs] using hb
  · intro j
    have hb := ((norm_le_pi_norm ((hypertraceStateTest (J := J) T φ - z).2) j).trans
      (norm_snd_le (hypertraceStateTest (J := J) T φ - z))).trans_lt (by
        simpa only [dist_eq_norm] using hzε)
    have he := congrArg (fun q : HypertraceTestSpace I J H => q.2 j) hsum'
    have hd : finitePredualUnitary (U j) (finiteVectorDensity (w ∘ e) (x ∘ e)) -
        finiteVectorDensity (w ∘ e) (x ∘ e) = z.2 j := by
      calc
        _ = ∑ k : Fin (Fintype.card K), (w (e k) : ℂ) •
            (finitePredualUnitary (U j) (finiteOperatorCoefficient (x (e k)) (x (e k))) -
              finiteOperatorCoefficient (x (e k)) (x (e k))) := by
          simp only [finiteVectorDensity, Function.comp_apply, map_sum, map_smul,
            smul_sub, Finset.sum_sub_distrib]
        _ = z.2 j := by
          simpa only [Prod.snd_sum, Finset.sum_apply, Prod.smul_snd, Pi.smul_apply,
            hypertraceVectorTest, Complex.coe_smul] using he
    change ‖0 - z.2 j‖ < ε at hb
    rw [zero_sub, norm_neg] at hb
    simpa only [hd] using hb

end WeakPureInfiniteness

end

end OAI
