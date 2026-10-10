import OAI.GroupTheory.PolycyclicRecognition.Geometry.ParametricLieWords
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Analysis.Normed.Operator.NormedSpace

namespace OAI

/-! # Compact families of normalized Lie laws

Bounded brackets and generators satisfying fixed word-basis identities form
a compact parameter set. Limits retain the Lie identities and the exact word
normalizations, so bracket generation cannot disappear in a limit.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Metric

variable {V I J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A bilinear bracket satisfying alternation and Jacobi gives the ordinary
Lie ring structure on the existing additive group. -/
@[instance_reducible] def lieRingOfBilinear (B : V →L[ℝ] V →L[ℝ] V) (h : IsLieBracket B) : LieRing V where
  toAddCommGroup := inferInstance
  bracket := fun x y => B x y
  add_lie := by intro x y z; exact congrArg (fun f : V →L[ℝ] V => f z) (B.map_add x y)
  lie_add := by intro x y z; exact (B x).map_add y z
  lie_self := h.1
  leibniz_lie := h.2

/-- The bracket is compatible with the original real vector-space structure. -/
@[instance_reducible] def lieAlgebraOfBilinear (B : V →L[ℝ] V →L[ℝ] V) (h : IsLieBracket B) :
    @LieAlgebra ℝ V _ (lieRingOfBilinear B h) := by
  letI := lieRingOfBilinear B h
  exact { toModule := NormedSpace.toModule
          lie_smul := fun t x y => (B x).map_smul t y }

variable [FiniteDimensional ℝ V] [Fintype I]

/-- Parameter data for a fixed normalization by bracket words. -/
def normalizedLieParameters (w : J → FreeMagma I) (b : J → V) (C : ℝ) :
    Set ((V →L[ℝ] V →L[ℝ] V) × (I → V)) :=
  {p | ‖p.1‖ ≤ C ∧ ‖p.2‖ ≤ C ∧ IsLieBracket p.1 ∧
    ∀ j, evalBilinearWord p.1 p.2 (w j) = b j}

/-- The exact word identities are closed, while the coefficient and
letter bounds give a compact ambient set. -/
theorem isCompact_normalizedLieParameters
    (w : J → FreeMagma I) (b : J → V) (C : ℝ) :
    IsCompact (normalizedLieParameters w b C) := by
  let : FiniteDimensional ℝ (V →L[ℝ] V) := ContinuousLinearMap.finiteDimensional
  let : FiniteDimensional ℝ (V →L[ℝ] V →L[ℝ] V) := ContinuousLinearMap.finiteDimensional
  let : PseudoMetricSpace (V →L[ℝ] V →L[ℝ] V) :=
    (inferInstance : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] V)).toPseudoMetricSpace
  let : ProperSpace (V →L[ℝ] V →L[ℝ] V) := FiniteDimensional.proper ℝ _
  let : ProperSpace (I → V) := FiniteDimensional.proper ℝ _
  have hc : IsClosed {p : (V →L[ℝ] V →L[ℝ] V) × (I → V) | IsLieBracket p.1} :=
    isClosed_setOf_isLieBracket.preimage continuous_fst
  have hw := isClosed_wordNormalizations w b
  have he : normalizedLieParameters w b C =
      (closedBall (0 : V →L[ℝ] V →L[ℝ] V) C ×ˢ closedBall (0 : I → V) C) ∩
        {p | IsLieBracket p.1 ∧ ∀ j, evalBilinearWord p.1 p.2 (w j) = b j} := by
    ext p
    simp only [normalizedLieParameters, mem_ofPred_eq, mem_inter_iff, mem_prod,
      mem_closedBall, dist_eq_norm, sub_zero]
    tauto
  rw [he]
  exact (isCompact_closedBall _ _ |>.prod (isCompact_closedBall _ _)).inter_right (hc.inter hw)

end PolycyclicRecognition

end

end OAI
