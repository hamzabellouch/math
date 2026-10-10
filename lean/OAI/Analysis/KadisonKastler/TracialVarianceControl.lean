import OAI.Analysis.KadisonKastler.TraceInvariantVectors

namespace OAI

/-! # Detecting nonscalar elements by one tracial commutator -/

namespace KadisonKastler

open Set

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

/-- Scalar averaging in the trace Hilbert space gives one unitary detecting
at least half the distance to the scalar trace. -/
theorem exists_unitary_trace_variance_control
    (hM : Generator.IsII1Factor M.toStarSubalgebra) (x : Algebra M) :
    ∃ u : unitary (Algebra M),
      traceTwoNorm (concreteFactorTrace hM)
        (x - (concreteFactorTrace hM).toLinearMap x • (1 : Algebra M)) ≤
      2 * traceTwoNorm (concreteFactorTrace hM) ((u : Algebra M) * x - x * u) := by
  classical
  let τ := concreteFactorTrace hM
  let J := concreteTraceEmbedding hM
  let d := traceTwoNorm τ (x - τ.toLinearMap x • (1 : Algebra M))
  by_cases hd : d = 0
  · exact ⟨1, by change d ≤ _; rw [hd]; exact mul_nonneg (by norm_num) (traceTwoNorm_nonneg _ _)⟩
  have hdp : 0 < d := lt_of_le_of_ne (traceTwoNorm_nonneg τ _) (Ne.symm hd)
  by_contra h
  push Not at h
  have hsub : J '' relativeUnitaryOrbit (StarAlgHom.id ℂ (Algebra M)) x ⊆
      Metric.closedBall (J x) (d / 2) := by
    rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm, ← map_sub, concreteTraceEmbedding_norm]
    change traceTwoNorm τ ((u : Algebra M) * x * star (u : Algebra M) - x) ≤ d / 2
    have he : (u : Algebra M) * x * star (u : Algebra M) - x =
        ((u : Algebra M) * x - x * u) * star (u : Algebra M) := by
      rw [sub_mul, mul_assoc x, Unitary.mul_star_self_of_mem u.property, mul_one]
    rw [he, ← Unitary.coe_star, traceTwoNorm_mul_unitary]
    have hu := h u
    change 2 * traceTwoNorm τ ((u : Algebra M) * x - x * u) < d at hu
    linarith
  have hh := trace_scalar_mem_relativeOrbit_hull J (concreteTraceEmbedding_norm hM)
    (concreteFactorTrace_finiteVector hM) (StarAlgHom.id ℂ (Algebra M))
    (traceHilbert_factor hM) x
  rw [diagonalTraceHull_eq] at hh
  have hb := (closure_minimal (convexHull_min hsub (convex_closedBall (J x) (d / 2)))
    Metric.isClosed_closedBall) hh
  rw [Metric.mem_closedBall, dist_eq_norm, ← map_sub, concreteTraceEmbedding_norm] at hb
  have hrev : traceTwoNorm τ (τ.toLinearMap x • (1 : Algebra M) - x) = d :=
    traceTwoNorm_sub_comm τ _ _
  rw [hrev] at hb
  linarith

end

end KadisonKastler

end OAI
