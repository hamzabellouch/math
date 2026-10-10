import OAI.Analysis.KadisonSimilarity.Tracial.ProjectionTraceContinuity
import OAI.Analysis.KadisonSimilarity.Tracial.ConcreteGNSNormality

namespace OAI

/-! Projection continuity in the original representation follows from
faithfulness and normality of the chosen trace's native GNS range. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge Filter
open scoped ComplexOrder Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance gnsProjection_closed {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (M : VonNeumannAlgebra E) :
    IsClosed (M.toStarSubalgebra : Set (E →L[ℂ] E)) := by
  change IsClosed (M : Set (E →L[ℂ] E))
  infer_instance

/-- Projection continuity for a faithful normal tracial geometry. -/
theorem projection_tendsto_zero_of_normal_geometry
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (M : VonNeumannAlgebra H) (G : TracialCornerGeometry M.toStarSubalgebra E)
    (τ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (hτ : ∀ a, τ a = G.trace a)
    (h1 : G.trace 1 = 1) (hf : Function.Injective G.vector)
    (N : VonNeumannAlgebra E) (hN : G.left.range = N.toStarSubalgebra)
    (p : ℕ → M.toStarSubalgebra) (hp : ∀ n, IsStarProjection (p n))
    (ht : Tendsto (fun n => (τ (p n)).re) atTop (𝓝 0)) (x : H) :
    Tendsto (fun n => (p n : H →L[ℂ] H) x) atTop (𝓝 0) := by
  let e : M.toStarSubalgebra ≃⋆ₐ[ℂ] N.toStarSubalgebra :=
    equivalenceOfConcreteRange N G.left (G.left_injective hf) hN
  let υ : TracialRepresentation N := G.normalTracialRepresentation h1 hf N hN
  let σ : N.toStarSubalgebra →ₚ[ℂ] ℂ := transportedPositiveTrace τ e
  have hσ (b : N.toStarSubalgebra) : σ b = υ.trace b := by
    have h := G.normalTracialRepresentation_trace h1 hf N hN (e.symm b)
    change υ.trace (e (e.symm b)) = G.trace (e.symm b) at h
    rw [e.apply_symm_apply] at h
    change τ (e.symm b) = υ.trace b
    exact (hτ _).trans h.symm
  have he (a : M.toStarSubalgebra) : σ (e a) = τ a :=
    transportedPositiveTrace_map τ e a
  have hfaith (q : M.toStarSubalgebra) (hq : IsStarProjection q)
      (hqt : (τ q).re = 0) : q = 0 := by
    have hn : ‖G.vector q‖ ^ 2 = 0 := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ), G.inner_vector,
        hq.isSelfAdjoint.star_eq, hq.isIdempotentElem.eq, ← hτ]
      exact hqt
    have hz : G.vector q = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
    exact hf (hz.trans (map_zero G.vector).symm)
  exact projection_tendsto_zero_of_trace_tendsto_zero M N e υ τ σ hσ he hfaith p hp ht x

/-- Vanishing trace of projections implies strong convergence in the
original representation, using the faithful normal GNS model. -/
theorem projection_tendsto_zero_of_normal_gns
    (M : VonNeumannAlgebra H) (τ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (h1 : τ 1 = 1) (htr : ∀ a b, τ (a * b) = τ (b * a))
    (hf : ∀ a, τ (star a * a) = 0 → a = 0) (hN : HasNormalGNS τ)
    (p : ℕ → M.toStarSubalgebra) (hp : ∀ n, IsStarProjection (p n))
    (ht : Tendsto (fun n => (τ (p n)).re) atTop (𝓝 0)) (x : H) :
    Tendsto (fun n => (p n : H →L[ℂ] H) x) atTop (𝓝 0) := by
  exact projection_tendsto_zero_of_normal_geometry M (gnsTracialGeometry τ htr)
    τ (fun _ => rfl) h1 (gnsTracialVector_injective τ hf)
    (representationVonNeumannAlgebra τ.gnsStarAlgHom) hN p hp ht x

end KadisonSimilarity

end

end OAI
