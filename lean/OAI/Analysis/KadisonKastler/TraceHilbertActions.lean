import OAI.Analysis.KadisonKastler.ConcreteTraceHilbert
import OAI.Analysis.KadisonKastler.FiniteBimodularBound

namespace OAI

/-! # Bimodule actions on the trace Hilbert space

The canonical completion carries left and right multiplication. Its unitary
actions give the bounded-ball estimate.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

/-- Left multiplication in the canonical trace representation. -/
def concreteTraceLeftAction (hM : Generator.IsII1Factor M.toStarSubalgebra) :
    Algebra M →⋆ₐ[ℂ] (ConcreteTraceHilbert hM →L[ℂ] ConcreteTraceHilbert hM) :=
  Generator.Tracial.traceFreeHilbertAction (traceHilbert_factor hM)
    hM.diffuse hM.finite (traceHilbert_nonzero hM)

/-- Right multiplication in the canonical trace representation. -/
def concreteTraceRightAction (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (a : Algebra M) : ConcreteTraceHilbert hM →L[ℂ] ConcreteTraceHilbert hM :=
  Generator.Tracial.traceFreeRightAction (traceHilbert_factor hM)
    hM.diffuse hM.finite (traceHilbert_nonzero hM) a

@[simp] theorem concreteTraceLeftAction_embedding
    (hM : Generator.IsII1Factor M.toStarSubalgebra) (a x : Algebra M) :
    concreteTraceLeftAction hM a (concreteTraceEmbedding hM x) =
      concreteTraceEmbedding hM (a * x) := by
  exact Generator.Tracial.traceFreeHilbertAction_inclusion (traceHilbert_factor hM)
    hM.diffuse hM.finite (traceHilbert_nonzero hM) a x

@[simp] theorem concreteTraceRightAction_embedding
    (hM : Generator.IsII1Factor M.toStarSubalgebra) (a x : Algebra M) :
    concreteTraceRightAction hM a (concreteTraceEmbedding hM x) =
      concreteTraceEmbedding hM (x * a) := by
  change Generator.Tracial.traceFreeRightAction (traceHilbert_factor hM)
    hM.diffuse hM.finite (traceHilbert_nonzero hM) a
    (Generator.Tracial.traceFreeInclusion (traceHilbert_factor hM)
      hM.diffuse hM.finite (traceHilbert_nonzero hM)
      (Generator.Tracial.traceFreeCopy (traceHilbert_factor hM)
        hM.diffuse hM.finite (traceHilbert_nonzero hM) x)) = _
  rw [Generator.Tracial.traceFreeRightAction_inclusion]
  congr 1

/-- Left multiplication by a unitary is a unitary on the completion. -/
def concreteTraceLeftUnitary (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (u : unitary (Algebra M)) :
    unitary (ConcreteTraceHilbert hM →L[ℂ] ConcreteTraceHilbert hM) :=
  Unitary.map (StarMonoidHom.ofClass (concreteTraceLeftAction hM)) u

theorem concreteTraceRightUnitary_norm
    (hM : Generator.IsII1Factor M.toStarSubalgebra) (u : unitary (Algebra M))
    (x : ConcreteTraceHilbert hM) : ‖concreteTraceRightAction hM u x‖ = ‖x‖ := by
  revert x
  apply isClosed_property (concreteTraceEmbedding_denseRange hM)
    (isClosed_eq (by fun_prop) (by fun_prop))
  intro a
  rw [concreteTraceRightAction_embedding, concreteTraceEmbedding_norm,
    concreteTraceEmbedding_norm, traceTwoNorm_mul_unitary]

theorem concreteTraceRightUnitary_inverse
    (hM : Generator.IsII1Factor M.toStarSubalgebra) (u : unitary (Algebra M))
    (x : ConcreteTraceHilbert hM) :
    concreteTraceRightAction hM (star (u : Algebra M))
      (concreteTraceRightAction hM u x) = x := by
  revert x
  apply isClosed_property (concreteTraceEmbedding_denseRange hM)
    (isClosed_eq (by fun_prop) (by fun_prop))
  intro a
  rw [concreteTraceRightAction_embedding, concreteTraceRightAction_embedding,
    mul_assoc, Unitary.mul_star_self_of_mem u.property, mul_one]

/-- Right multiplication by a unitary is a unitary on the completion. -/
def concreteTraceRightUnitary (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (u : unitary (Algebra M)) :
    unitary (ConcreteTraceHilbert hM →L[ℂ] ConcreteTraceHilbert hM) :=
  Unitary.linearIsometryEquiv.symm
    { (concreteTraceRightAction hM u).toLinearMap with
      norm_map' := concreteTraceRightUnitary_norm hM u
      invFun := concreteTraceRightAction hM (star (u : Algebra M))
      left_inv := concreteTraceRightUnitary_inverse hM u
      right_inv := fun x => by
        change concreteTraceRightAction hM u
          (concreteTraceRightAction hM (star (u : Algebra M)) x) = x
        simpa only [Unitary.coe_star, star_star] using
          concreteTraceRightUnitary_inverse hM (star u) x }

@[simp] theorem concreteTraceLeftUnitary_coe
    (hM : Generator.IsII1Factor M.toStarSubalgebra) (u : unitary (Algebra M)) :
    (concreteTraceLeftUnitary hM u :
      ConcreteTraceHilbert hM →L[ℂ] ConcreteTraceHilbert hM) =
      concreteTraceLeftAction hM u := rfl

@[simp] theorem concreteTraceRightUnitary_coe
    (hM : Generator.IsII1Factor M.toStarSubalgebra) (u : unitary (Algebra M)) :
    (concreteTraceRightUnitary hM u :
      ConcreteTraceHilbert hM →L[ℂ] ConcreteTraceHilbert hM) =
      concreteTraceRightAction hM u := rfl

/-- The bounded-ball estimate on the constructed canonical Hilbert space,
with actual multiplication actions and no action-existence hypothesis. -/
theorem concreteTrace_bimodular_bound
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    {R : Type*} [CStarAlgebra R] (φ : R →⋆ₐ[ℂ] Algebra M)
    (hirr : ∀ b : Algebra M, (∀ r : R, φ r * b = b * φ r) →
      ∃ c : ℂ, b = c • (1 : Algebra M))
    (V : ConcreteTraceHilbert hM →L[ℂ] ConcreteTraceHilbert hM)
    (hVL : ∀ u : unitary R, Commute V (concreteTraceLeftAction hM (φ u)))
    (hVR : ∀ u : unitary R, Commute V (concreteTraceRightAction hM (φ u)))
    {K : ℝ} (hK : ∀ x y : Algebra M, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      ‖inner ℂ (V (concreteTraceEmbedding hM x)) (concreteTraceEmbedding hM y)‖ ≤ K) :
    ‖V‖ ≤ 384 * K := by
  let U (u : unitary R) : unitary (Algebra M) :=
    Unitary.map (StarMonoidHom.ofClass φ) u
  exact opNorm_le_of_irreducible_bimodular_tests (concreteFactorTrace hM)
    (concreteTraceEmbedding hM) (concreteTraceEmbedding_norm hM)
    (concreteTraceEmbedding_denseRange hM) (concreteFactorTrace_finiteVector hM)
    φ hirr V (fun u => concreteTraceLeftUnitary hM (U u))
    (fun u => concreteTraceRightUnitary hM (U u))
    (fun u x => (concreteTraceLeftAction_embedding hM (φ u) x).symm)
    (fun u x => (concreteTraceRightAction_embedding hM (φ u) x).symm)
    hVL hVR hK

end

end KadisonKastler

end OAI
