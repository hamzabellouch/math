import OAI.Analysis.KadisonKastler.TraceInvariantVectors
import OAI.Analysis.KadisonKastler.Jordan

namespace OAI

/-! # Primeness of finite factors from trace averaging

The scalar relative orbit average gives the prime-algebra property needed
for Jordan orientation, without introducing central-support machinery.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

/-- A finite factor is prime: annihilating all middle factors forces one
of the two outside factors to vanish. -/
theorem finiteFactor_isPrimeAlgebra
    (hM : Generator.IsII1Factor M.toStarSubalgebra) : IsPrimeAlgebra (Algebra M) := by
  intro a b hab
  let τ := concreteFactorTrace hM
  let J := concreteTraceEmbedding hM
  let q := star a * a
  let x := b * star b
  have hzero (u : unitary (Algebra M)) :
      inner ℂ (J q) (J ((u : Algebra M) * x * star (u : Algebra M))) = 0 := by
    rw [concreteTraceEmbedding_inner]
    have he : star q * ((u : Algebra M) * x * star (u : Algebra M)) =
        star a * (a * (u : Algebra M) * b) * star b * star (u : Algebra M) := by
      dsimp [q, x]
      simp only [star_mul, star_star, mul_assoc]
    rw [he, hab, mul_zero, zero_mul, zero_mul, map_zero]
  let F : Set (ConcreteTraceHilbert hM) := {z | inner ℂ (J q) z = 0}
  have hFconv : Convex ℝ F := (convex_singleton 0).linear_preimage
    ((innerSL ℂ (J q)).toLinearMap.restrictScalars ℝ)
  have hFclosed : IsClosed F := isClosed_eq (by fun_prop) continuous_const
  have hsub : J '' relativeUnitaryOrbit (StarAlgHom.id ℂ (Algebra M)) x ⊆ F := by
    rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
    exact hzero u
  have hmem := trace_scalar_mem_relativeOrbit_hull J (concreteTraceEmbedding_norm hM)
    (concreteFactorTrace_finiteVector hM) (StarAlgHom.id ℂ (Algebra M))
    (traceHilbert_factor hM) x
  rw [diagonalTraceHull_eq] at hmem
  have hscalar : inner ℂ (J q) (J (τ.toLinearMap x • (1 : Algebra M))) = 0 :=
    (closure_minimal (convexHull_min hsub hFconv) hFclosed) hmem
  have hq : star q = q := by simp only [q, star_mul, star_star]
  rw [map_smul, inner_smul_right, concreteTraceEmbedding_inner, mul_one, hq] at hscalar
  change τ.toLinearMap x * τ.toLinearMap q = 0 at hscalar
  rcases mul_eq_zero.mp hscalar with hb | ha
  · right
    apply τ.faithful b
    exact (τ.tracial (star b) b).trans hb
  · left
    exact τ.faithful a ha

end

end KadisonKastler

end OAI
