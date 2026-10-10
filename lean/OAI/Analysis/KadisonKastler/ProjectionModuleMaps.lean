import OAI.Analysis.KadisonKastler.RowPinching
import OAI.Analysis.KadisonKastler.Algebra
import OAI.Analysis.FactorGeneration.SpectralPinching

namespace OAI

/-! Norm spectral approximation reduces right modularity to projection tests. -/

namespace KadisonKastler

noncomputable section

open Generator.Tracial
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance projectionSpanOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance projectionSpanStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

theorem selfAdjoint_mem_closed_algebra_projection_span (M : VonNeumannAlgebra H)
    (x : Algebra M) (hx : IsSelfAdjoint x) :
    x ∈ (Submodule.span ℂ {p : Algebra M | IsStarProjection p}).topologicalClosure := by
  classical
  change x ∈ closure (Submodule.span ℂ {p : Algebra M | IsStarProjection p} : Set _)
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let p : AlgebraProjection M := ⟨1, IsStarProjection.one _⟩
  obtain ⟨Q, c, _, hc⟩ := exists_finite_spectral_approximation p x hx ε hε
  refine ⟨∑ i, (c i : ℂ) • (Q.piece i).val, ?_, ?_⟩
  · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Q.piece i).property)
  · simpa only [p, one_mul, mul_one, dist_eq_norm] using hc

theorem algebra_closed_projection_span_eq_top (M : VonNeumannAlgebra H) :
    (Submodule.span ℂ {p : Algebra M | IsStarProjection p}).topologicalClosure = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨a, ha, _, hsum⟩ := CStarAlgebra.exists_sum_four_nonneg x
  rw [hsum]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
    (selfAdjoint_mem_closed_algebra_projection_span M (a i) (ha i).isSelfAdjoint)

/-- A bounded map is right modular as soon as it is fixed by each projection
pinching. No continuity in the weak topology is required. -/
theorem right_module_of_projection_tests (M : VonNeumannAlgebra H)
    (F : Algebra M →L[ℂ] Algebra M)
    (hF : ∀ p : Algebra M, IsStarProjection p → ∀ x, F (x * p) = F x * p) :
    ∀ x y, F (x * y) = F x * y := by
  intro x y
  have hs : (Submodule.span ℂ {p : Algebra M | IsStarProjection p} : Set _) ⊆
      {b | F (x * b) = F x * b} := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem p hp => exact hF p hp x
    | zero =>
      change F (x * 0) = F x * 0
      simp only [mul_zero, map_zero]
    | add a b ha hb hia hib =>
      change F (x * a) = F x * a at hia
      change F (x * b) = F x * b at hib
      change F (x * (a + b)) = F x * (a + b)
      simp only [mul_add, map_add, hia, hib]
    | smul z a ha hia =>
      change F (x * a) = F x * a at hia
      change F (x * (z • a)) = F x * (z • a)
      simp only [mul_smul_comm, map_smul, hia]
  have hc : IsClosed {b : Algebra M | F (x * b) = F x * b} :=
    isClosed_eq (F.continuous.comp (continuous_const.mul continuous_id))
      (continuous_const.mul continuous_id)
  apply closure_minimal hs hc
  rw [← Submodule.topologicalClosure_coe, algebra_closed_projection_span_eq_top]
  trivial

theorem right_module_iff_projectionAverage_fixed (M : VonNeumannAlgebra H)
    (F : Algebra M →L[ℂ] Algebra M) :
    (∀ x y, F (x * y) = F x * y) ↔
      ∀ p : Algebra M, IsStarProjection p → projectionAverage p F.toLinearMap = F.toLinearMap := by
  constructor
  · intro h p hp
    exact (projectionAverage_fixed_iff hp _).2 (fun x => h x p)
  · intro h
    exact right_module_of_projection_tests M F fun p hp =>
      (projectionAverage_fixed_iff hp _).1 (h p hp)

/-- The value at the identity determines a right module map. -/
theorem right_module_eq_left_multiplication {A : Type*} [CStarAlgebra A]
    (F : A →ₗ[ℂ] A) (hF : ∀ x y, F (x * y) = F x * y) (x : A) :
    F x = F 1 * x := by simpa only [one_mul] using hF 1 x

end

end KadisonKastler

end OAI
