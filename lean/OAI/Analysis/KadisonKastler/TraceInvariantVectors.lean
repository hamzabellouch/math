import OAI.Analysis.KadisonKastler.TraceHilbertActions

namespace OAI

/-! # Scalar invariant vectors in the trace completion

Relative convex averaging identifies invariant vectors without assuming
that a Hilbert-space vector is represented by a bounded algebra element.
-/

namespace KadisonKastler

noncomputable section

variable {H E R : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [CStarAlgebra R] {M : VonNeumannAlgebra H}

/-- An invariant coefficient has the same value at an element and its
scalar trace, by continuity on the actual relative orbit hull. -/
theorem inner_trace_scalar_of_relative_invariant
    (τ : FaithfulTracialState (Algebra M)) (J : Algebra M →ₗ[ℂ] E)
    (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x) (hτ : FiniteVectorTrace τ)
    (φ : R →⋆ₐ[ℂ] Algebra M)
    (hirr : ∀ b : Algebra M, (∀ r : R, φ r * b = b * φ r) →
      ∃ c : ℂ, b = c • (1 : Algebra M))
    (v : E) (hinv : ∀ (u : unitary R) x,
      inner ℂ v (J (φ u * x * star (φ u))) = inner ℂ v (J x))
    (x : Algebra M) :
    inner ℂ v (J (τ.toLinearMap x • (1 : Algebra M))) = inner ℂ v (J x) := by
  let S : Set E := {w | inner ℂ v w = inner ℂ v (J x)}
  have hc : Convex ℝ S := (convex_singleton _).linear_preimage
    ((innerSL ℂ v).toLinearMap.restrictScalars ℝ)
  have hs : IsClosed S := isClosed_eq (by fun_prop) continuous_const
  have hsub : J '' relativeUnitaryOrbit φ x ⊆ S := by
    rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
    exact hinv u x
  have hh := trace_scalar_mem_relativeOrbit_hull J hJ hτ φ hirr x
  rw [diagonalTraceHull_eq] at hh
  exact (closure_minimal (convexHull_min hsub hc) hs) hh

/-- In a dense tracial realization, invariant coefficients force the
vector to be a scalar multiple of the trace vector. -/
theorem scalar_of_relative_invariant_coefficients
    (τ : FaithfulTracialState (Algebra M)) (J : Algebra M →ₗ[ℂ] E)
    (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x) (hτ : FiniteVectorTrace τ)
    (hdense : DenseRange J)
    (htrace : ∀ x, inner ℂ (J 1) (J x) = τ.toLinearMap x)
    (φ : R →⋆ₐ[ℂ] Algebra M)
    (hirr : ∀ b : Algebra M, (∀ r : R, φ r * b = b * φ r) →
      ∃ c : ℂ, b = c • (1 : Algebra M))
    (v : E) (hinv : ∀ (u : unitary R) x,
      inner ℂ v (J (φ u * x * star (φ u))) = inner ℂ v (J x)) :
    ∃ z : ℂ, v = z • J 1 := by
  refine ⟨star (inner ℂ v (J 1)), ?_⟩
  apply ext_inner_right ℂ
  intro w
  apply isClosed_property hdense (isClosed_eq (by fun_prop) (by fun_prop))
  intro x
  have hx := inner_trace_scalar_of_relative_invariant τ J hJ hτ φ hirr v hinv x
  rw [map_smul, inner_smul_right] at hx
  rw [inner_smul_left, starRingEnd_apply, star_star, htrace]
  exact hx.symm.trans (mul_comm _ _)

@[simp] theorem concreteTraceEmbedding_inner
    (hM : Generator.IsII1Factor M.toStarSubalgebra) (x y : Algebra M) :
    inner ℂ (concreteTraceEmbedding hM x) (concreteTraceEmbedding hM y) =
      (concreteFactorTrace hM).toLinearMap (star x * y) :=
  Generator.Tracial.traceFreeInclusion_inner (traceHilbert_factor hM)
    hM.diffuse hM.finite (traceHilbert_nonzero hM) x y

/-- A vector fixed by one unitary conjugation has an invariant coefficient. -/
theorem concreteTrace_inner_conjugation_of_fixed
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (u : unitary (Algebra M)) (v : ConcreteTraceHilbert hM)
    (hfixed : concreteTraceLeftAction hM u
      (concreteTraceRightAction hM (star (u : Algebra M)) v) = v)
    (x : Algebra M) :
    inner ℂ v (concreteTraceEmbedding hM
      ((u : Algebra M) * x * star (u : Algebra M))) =
        inner ℂ v (concreteTraceEmbedding hM x) := by
  let W := concreteTraceLeftUnitary hM u * concreteTraceRightUnitary hM (star u)
  have hW : (W : ConcreteTraceHilbert hM →L[ℂ] ConcreteTraceHilbert hM) v = v :=
    hfixed
  have hWx : (W : ConcreteTraceHilbert hM →L[ℂ] ConcreteTraceHilbert hM)
      (concreteTraceEmbedding hM x) =
      concreteTraceEmbedding hM ((u : Algebra M) * x * star (u : Algebra M)) := by
    change concreteTraceLeftAction hM (u : Algebra M)
      (concreteTraceRightAction hM (star (u : Algebra M)) (concreteTraceEmbedding hM x)) = _
    rw [concreteTraceRightAction_embedding, concreteTraceLeftAction_embedding, mul_assoc]
  calc
    _ = inner ℂ ((W : ConcreteTraceHilbert hM →L[ℂ] ConcreteTraceHilbert hM) v)
        ((W : ConcreteTraceHilbert hM →L[ℂ] ConcreteTraceHilbert hM)
          (concreteTraceEmbedding hM x)) := by rw [hW, hWx]
    _ = _ := Unitary.inner_map_map W v (concreteTraceEmbedding hM x)


/-- The actual two-sided unitary action of an irreducible subalgebra has
only scalar trace vectors as invariant vectors. -/
theorem concreteTrace_scalar_of_conjugation_invariant
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (φ : R →⋆ₐ[ℂ] Algebra M)
    (hirr : ∀ b : Algebra M, (∀ r : R, φ r * b = b * φ r) →
      ∃ c : ℂ, b = c • (1 : Algebra M))
    (v : ConcreteTraceHilbert hM)
    (hinv : ∀ u : unitary R,
      concreteTraceLeftAction hM (φ u)
        (concreteTraceRightAction hM (star (φ u)) v) = v) :
    ∃ z : ℂ, v = z • concreteTraceEmbedding hM 1 := by
  apply scalar_of_relative_invariant_coefficients (concreteFactorTrace hM)
    (concreteTraceEmbedding hM) (concreteTraceEmbedding_norm hM)
    (concreteFactorTrace_finiteVector hM) (concreteTraceEmbedding_denseRange hM)
    (fun x => by simp only [concreteTraceEmbedding_inner, star_one, one_mul]) φ hirr v
  intro u x
  exact concreteTrace_inner_conjugation_of_fixed hM
    (Unitary.map (StarMonoidHom.ofClass φ) u) v (hinv u) x

end

end KadisonKastler

end OAI
