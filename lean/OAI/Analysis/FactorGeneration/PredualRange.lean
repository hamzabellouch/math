import OAI.Analysis.FactorGeneration.CyclicPredual
import OAI.Analysis.FactorGeneration.FunctionalLimits
import OAI.Analysis.FactorGeneration.MatrixExpectation
import OAI.Analysis.FactorGeneration.PredualOrder

namespace OAI

noncomputable section

namespace Generator

/-! An actual separable Banach predual for the constructed matrix-generated
factor. The existential convention is exactly Generator.HasSeparablePredual. -/
section
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem cyclicPredualEvaluation_surjective : Function.Surjective (cyclicPredualEvaluationIsometry τ) := by
  intro φ
  let c : ℂ := (‖φ‖+1 : ℝ)
  have hc : c ≠ 0 := by dsimp [c]; exact_mod_cast ne_of_gt (by positivity : 0 < ‖φ‖+1)
  have hnorm : ‖c⁻¹ • φ‖ ≤ 1 := by
    rw [norm_smul,norm_inv]
    have hn : ‖c‖=‖φ‖+1 := by dsimp [c]; rw [Complex.norm_real,Real.norm_of_nonneg (by positivity)]
    rw [hn]
    exact (inv_mul_le_one₀ (by positivity : 0 < ‖φ‖+1)).mpr (by linarith)
  obtain ⟨a,_,ha⟩ := cyclicPredualEvaluation_unitBall_surjective τ (c⁻¹ • φ) hnorm
  refine ⟨c • a,?_⟩
  rw [map_smul]
  change c • cyclicPredualEvaluation τ a=φ
  rw [ha,smul_smul,mul_inv_cancel₀ hc,one_smul]

def cyclicPredualLinearEquiv : M.toStarSubalgebra ≃ₗᵢ[ℂ] StrongDual ℂ (cyclicPredual τ) :=
  LinearIsometryEquiv.ofSurjective (cyclicPredualEvaluationIsometry τ)
    (cyclicPredualEvaluation_surjective τ)

def algebraStarIsometry (M : VonNeumannAlgebra H) :
    M.toStarSubalgebra ≃ₗᵢ⋆[ℂ] M.toStarSubalgebra :=
  { starLinearEquiv ℂ with
    norm_map' := fun a => by
      change ‖star a.val‖=‖a.val‖
      rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint.norm_map] }

def cyclicPredualDualEquiv : StrongDual ℂ (cyclicPredual τ) ≃ₗᵢ⋆[ℂ] M.toStarSubalgebra :=
  (cyclicPredualLinearEquiv τ).symm.trans (algebraStarIsometry M)

theorem hasSeparablePredual_of_trace_separable
    (hsep : TopologicalSpace.IsSeparable (Set.range (fun a : M.toStarSubalgebra => a.val τ.vector))) :
    HasSeparablePredual M.toStarSubalgebra := by
  let := traceCyclicSpace_separable τ hsep
  let := cyclicPredual_separable τ
  exact ⟨cyclicPredual τ,inferInstance,inferInstance,inferInstance,inferInstance,
    ⟨cyclicPredualDualEquiv τ⟩⟩

end Tracial

namespace FiniteMatrixStage
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem generated_hasSeparablePredual (A : ℕ → FiniteMatrixStage N)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    (τ : TracialRepresentation M) (hNM : N ≤ M) : HasSeparablePredual (generated A) :=
  hasSeparablePredual_of_trace_separable (generatedTrace A τ hNM)
    (generated_norm₂_separable A hA τ hNM)

theorem exists_irreducible_matrix_generated_II1_separablePredual
    (τ : TracialRepresentation M) (hNM : N ≤ M)
    (hfactor : ∀ c : N.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
    (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ))) :
    ∃ A : ℕ → FiniteMatrixStage N,A 0=scalarStage N ∧
      Monotone (fun n => (A n).units.concreteAlgebra) ∧
      (∀ n,FiniteDimensional ℂ (A n).units.concreteAlgebra) ∧
      IsII1Factor (generated A) ∧ HasSeparablePredual (generated A) ∧
      generated A ≤ N.toStarSubalgebra ∧
      ∀ c : M.toStarSubalgebra,(∀ a : generated A,a.val*c.val=c.val*a.val) →
        c=τ.trace c • (1 : M.toStarSubalgebra) := by
  obtain ⟨A,hA,hmono,hfd,hII,hAN,hscalar⟩ :=
    exists_irreducible_matrix_generated_II1 τ hNM hfactor hdiff hirr hsep
  exact ⟨A,hA,hmono,hfd,hII,generated_hasSeparablePredual A hmono τ hNM,hAN,hscalar⟩

end FiniteMatrixStage

end

/-! Separability of the actual cyclic predual implies separability of the
trace-vector orbit. This does not identify an arbitrary given Banach predual
with the cyclic predual. -/
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

/-- A vector is determined by its trace-vector coefficient functional. -/
theorem cyclicCoefficient_traceVector_injective :
    Function.Injective (fun ξ : traceCyclicSpace τ =>
      cyclicCoefficient τ ξ (traceCyclicVector τ)) := by
  intro ξ η he
  apply (traceCyclicHom_cyclic τ).eq_of_inner_left ℂ
  rintro _ ⟨a, rfl⟩
  exact congrArg (fun f : StrongDual ℂ M.toStarSubalgebra => f a) he

/-- A countable total family of dual evaluations supplies a countable total
family of actual trace vectors. -/
theorem exists_countable_total_traceVectors
    [TopologicalSpace.SeparableSpace (cyclicPredual τ)] :
    ∃ a : ℕ → M.toStarSubalgebra, (∀ n, ‖a n‖ ≤ 1) ∧
      ∀ ξ : traceCyclicSpace τ,
        (∀ n, inner ℂ ξ (traceCyclicHom τ (a n) (traceCyclicVector τ)) = 0) → ξ = 0 := by
  obtain ⟨g, hg, htotal⟩ := exists_countable_total_dual (cyclicPredual τ)
  let a : ℕ → M.toStarSubalgebra := fun n => (cyclicPredualLinearEquiv τ).symm (g n)
  have he (n : ℕ) : cyclicPredualEvaluation τ (a n) = g n :=
    (cyclicPredualLinearEquiv τ).apply_symm_apply (g n)
  refine ⟨a, fun n => ?_, fun ξ hξ => ?_⟩
  · exact ((cyclicPredualLinearEquiv τ).symm.norm_map (g n)).le.trans (hg n)
  · let f : cyclicPredual τ := ⟨cyclicCoefficient τ ξ (traceCyclicVector τ),
        cyclicCoefficient_mem τ ξ (traceCyclicVector τ)⟩
    have hf : f = 0 := htotal f (fun n => by
      rw [← he]
      exact hξ n)
    apply (traceCyclicHom_cyclic τ).eq_zero_of_inner_left ℂ
    rintro _ ⟨b, rfl⟩
    exact congrArg (fun q : cyclicPredual τ => q.val b) hf

theorem traceCyclicSpace_separable_of_cyclicPredual
    [TopologicalSpace.SeparableSpace (cyclicPredual τ)] :
    TopologicalSpace.SeparableSpace (traceCyclicSpace τ) := by
  obtain ⟨a, _, ha⟩ := exists_countable_total_traceVectors τ
  let v : ℕ → traceCyclicSpace τ := fun n => traceCyclicHom τ (a n) (traceCyclicVector τ)
  let V := (Submodule.span ℂ (Set.range v)).topologicalClosure
  have htop : V = ⊤ := by
    apply Submodule.orthogonal_eq_bot_iff.mp
    apply eq_bot_iff.mpr
    intro ξ hξ
    change ξ = 0
    apply ha ξ
    intro n
    exact (Submodule.mem_orthogonal' V ξ).mp hξ (v n)
      (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨n, rfl⟩))
  have hs : TopologicalSpace.IsSeparable (V : Set (traceCyclicSpace τ)) :=
    (Set.countable_range v).isSeparable.span.closure
  rw [htop, Submodule.top_coe] at hs
  exact TopologicalSpace.isSeparable_univ_iff.mp hs

theorem traceOrbit_isSeparable_of_cyclicPredual
    [TopologicalSpace.SeparableSpace (cyclicPredual τ)] :
    TopologicalSpace.IsSeparable (Set.range (baseVector τ)) := by
  let := traceCyclicSpace_separable_of_cyclicPredual τ
  apply (TopologicalSpace.isSeparable_range
    (continuous_subtype_val : Continuous (fun ξ : traceCyclicSpace τ => ξ.val))).mono
  rintro ξ ⟨a, rfl⟩
  exact ⟨traceCyclicHom τ a (traceCyclicVector τ), rfl⟩

end Tracial

/-! The given predual as a closed separating subspace of the algebra norm dual, with its evaluation duality. -/
section
open scoped ComplexConjugate
variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (S : StarSubalgebra ℂ (H →L[ℂ] H))
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] S)

/-- Keep the norm topology explicit through the nested dual construction. -/
instance predualAlgebraDualNormed : NormedAddCommGroup (StrongDual ℂ S) := inferInstance

def predualFunctionals : Submodule ℂ (StrongDual ℂ S) :=
  (predualFunctionalIsometry S e).toLinearMap.range

instance predualFunctionals_normed : NormedAddCommGroup (predualFunctionals S e) := inferInstance

instance predualFunctionals_normedSpace : NormedSpace ℂ (predualFunctionals S e) := inferInstance

def predualFunctionalsEquiv : X ≃ₗᵢ⋆[ℂ] predualFunctionals S e :=
  (predualFunctionalIsometry S e).equivRange

@[simp] theorem predualFunctionalsEquiv_val (x : X) :
    (predualFunctionalsEquiv S e x).val = predualFunctional S e x := rfl

theorem predualFunctionals_isClosed [CompleteSpace X] :
    IsClosed (predualFunctionals S e : Set (StrongDual ℂ S)) :=
  (predualFunctionalIsometry S e).isometry.isClosedEmbedding.isClosed_range

theorem predualFunctionals_separable [TopologicalSpace.SeparableSpace X] :
    TopologicalSpace.SeparableSpace (predualFunctionals S e) :=
  (TopologicalSpace.isSeparable_range (predualFunctionalIsometry S e).continuous).separableSpace

def predualRangeEvaluation (a : S) : StrongDual ℂ (predualFunctionals S e) :=
  (ContinuousLinearMap.apply ℂ ℂ a).domRestrict (predualFunctionals S e)

@[simp] theorem predualRangeEvaluation_apply (a : S) (f : predualFunctionals S e) :
    predualRangeEvaluation S e a f = f.val a := rfl

theorem predualRangeEvaluation_norm (a : S) : ‖predualRangeEvaluation S e a‖ = ‖a‖ := by
  apply le_antisymm
  · apply (predualRangeEvaluation S e a).opNorm_le_bound (norm_nonneg a)
    intro f
    exact (f.val.le_opNorm a).trans_eq (mul_comm _ _)
  · rw [← e.symm.norm_map a]
    apply (e.symm a).opNorm_le_bound (norm_nonneg _)
    intro x
    have h := (predualRangeEvaluation S e a).le_opNorm (predualFunctionalsEquiv S e x)
    simpa only [predualRangeEvaluation_apply, predualFunctionalsEquiv_val,
      predualFunctional_apply, Complex.norm_conj, LinearIsometryEquiv.norm_map] using h

/-- Pull a dual functional back through the conjugate-linear range equivalence. -/
def predualRangePullback (φ : StrongDual ℂ (predualFunctionals S e)) : StrongDual ℂ X :=
  LinearMap.mkContinuous
    { toFun := fun x => conj (φ (predualFunctionalsEquiv S e x))
      map_add' := by intros; simp
      map_smul' := by
        intro c x
        rw [(predualFunctionalsEquiv S e).map_smulₛₗ]
        simp }
    ‖φ‖ (by
      intro x
      change ‖conj (φ (predualFunctionalsEquiv S e x))‖ ≤ ‖φ‖ * ‖x‖
      simpa only [Complex.norm_conj, LinearIsometryEquiv.norm_map] using
        φ.le_opNorm (predualFunctionalsEquiv S e x))

/-- Every functional on the embedded given predual is evaluation at an actual a in S. -/
theorem predualRangeEvaluation_surjective : Function.Surjective (predualRangeEvaluation S e) := by
  intro φ
  refine ⟨e (predualRangePullback S e φ), ?_⟩
  ext f
  obtain ⟨x, rfl⟩ := (predualFunctionalsEquiv S e).surjective f
  simp only [predualRangeEvaluation_apply, predualFunctionalsEquiv_val,
    predualFunctional_apply, e.symm_apply_apply]
  change conj (conj (φ (predualFunctionalsEquiv S e x))) = _
  exact star_star _

end

/-! Hahn–Banach comparison of preduals from normal-functional membership and evaluation surjectivity. -/
section
variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (S : StarSubalgebra ℂ (H →L[ℂ] H))
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] S)

/-- A closed separating predual contained in an evaluation predual equals it.
The inclusion is a substantive hypothesis, not supplied by this theorem. -/
theorem predualFunctionals_eq_of_le (F : Submodule ℂ (StrongDual ℂ S))
    (hincl : predualFunctionals S e ≤ F)
    (hdual : ∀ φ : StrongDual ℂ F, ∃ a : S, ∀ f : F, φ f = f.val a) :
    predualFunctionals S e = F := by
  let : NormedAddCommGroup F := inferInstance
  let : NormedSpace ℂ F := inferInstance
  apply le_antisymm hincl
  intro f hf
  let K : Submodule ℂ F := (predualFunctionals S e).comap F.subtype
  let : IsClosed (K : Set F) :=
    (predualFunctionals_isClosed S e).preimage continuous_subtype_val
  let z : F := ⟨f, hf⟩
  by_contra hz
  have hq : K.mkQ z ≠ 0 := by
    intro heq
    exact hz ((Submodule.Quotient.mk_eq_zero K).mp heq)
  obtain ⟨g, hg⟩ := SeparatingDual.exists_ne_zero (R := ℂ) hq
  obtain ⟨a, ha⟩ := hdual (g.comp K.mkQL)
  have ha0 : a = 0 := by
    apply predualFunctional_separates S e a 0
    intro x
    have hmem : predualFunctional S e x ∈ predualFunctionals S e := ⟨x, rfl⟩
    let fx : F := ⟨predualFunctional S e x, hincl hmem⟩
    have hk : K.mkQ fx = 0 := (Submodule.Quotient.mk_eq_zero K).mpr hmem
    have hx := ha fx
    change g (K.mkQ fx) = predualFunctional S e x a at hx
    rw [hk, map_zero] at hx
    simpa only [map_zero] using hx.symm
  apply hg
  have hz' := ha z
  change g (K.mkQ z) = f a at hz'
  simpa only [ha0, map_zero] using hz'

end

/-! Conditional comparison with the constructed cyclic predual. Membership
of the given-predual evaluations in that space is an explicit unproved input;
it is not obtained merely from their order-limit convergence. -/
namespace Tracial
open UltrapowerBridge
variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M.toStarSubalgebra)

/-- Normal-functional membership is sufficient for equality with the given predual. -/
theorem predualFunctionals_eq_cyclicPredual_of_membership
    (hmem : ∀ x : X, predualFunctional M.toStarSubalgebra e x ∈ cyclicPredual τ) :
    predualFunctionals M.toStarSubalgebra e = cyclicPredual τ := by
  apply predualFunctionals_eq_of_le M.toStarSubalgebra e (cyclicPredual τ)
  · rintro f ⟨x, rfl⟩
    exact hmem x
  · intro φ
    obtain ⟨a, ha⟩ := cyclicPredualEvaluation_surjective τ φ
    refine ⟨a, fun f => ?_⟩
    exact (congrArg (fun ψ : StrongDual ℂ (cyclicPredual τ) => ψ f) ha).symm

/-- Under the same explicit membership input, separability transfers to the cyclic predual. -/
theorem cyclicPredual_separable_of_given_membership [TopologicalSpace.SeparableSpace X]
    (hmem : ∀ x : X, predualFunctional M.toStarSubalgebra e x ∈ cyclicPredual τ) :
    TopologicalSpace.SeparableSpace (cyclicPredual τ) := by
  rw [← predualFunctionals_eq_cyclicPredual_of_membership τ e hmem]
  exact predualFunctionals_separable M.toStarSubalgebra e

/-! The original given-predual evaluations suffice for trace-orbit separability
once their normal-functional membership (equivalently unit-ball WOT
continuity) is proved. The remaining input is displayed literally. -/

omit [CompleteSpace X] in
theorem given_predual_membership_iff_unitBall_continuity :
    (∀ x : X, predualFunctional M.toStarSubalgebra e x ∈ cyclicPredual τ) ↔
      ∀ x : X, Continuous (fun T : weakOperatorBall M 1 =>
        predualFunctional M.toStarSubalgebra e x ⟨T.val.toCLM, T.property.1⟩) := by
  exact forall_congr' (fun x => mem_cyclicPredual_iff_unitBall_continuous τ _)

theorem traceOrbit_isSeparable_of_given_membership [TopologicalSpace.SeparableSpace X]
    (hmem : ∀ x : X, predualFunctional M.toStarSubalgebra e x ∈ cyclicPredual τ) :
    TopologicalSpace.IsSeparable (Set.range (baseVector τ)) := by
  let := cyclicPredual_separable_of_given_membership τ e hmem
  exact traceOrbit_isSeparable_of_cyclicPredual τ

theorem traceOrbit_isSeparable_of_given_unitBall_continuity [TopologicalSpace.SeparableSpace X]
    (hc : ∀ x : X, Continuous (fun T : weakOperatorBall M 1 =>
      predualFunctional M.toStarSubalgebra e x ⟨T.val.toCLM, T.property.1⟩)) :
    TopologicalSpace.IsSeparable (Set.range (baseVector τ)) :=
  traceOrbit_isSeparable_of_given_membership τ e
    ((given_predual_membership_iff_unitBall_continuity τ e).mpr hc)

end Tracial

end Generator

end

end OAI
