import OAI.Analysis.KadisonKastler.PublishedIndependence
import OAI.Analysis.KadisonKastler.ConcreteTraceTransfer

namespace OAI

/-! # Trace separability in a separably acting finite representation

A finite vector formula bounds the trace two-norm by finitely many
Hilbert-space coordinates. Countable dense subsets of their ranges lift
to countable two-norm dense subsets of any prescribed set of operators.
-/

namespace KadisonKastler

open TopologicalSpace
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

private def traceCoordinates {n : ℕ} (ξ η : Fin n → H) :
    Algebra M →ₗ[ℂ] (Fin n × Bool → H) where
  toFun x i := if i.2 then (x : H →L[ℂ] H) (ξ i.1) else (x : H →L[ℂ] H) (η i.1)
  map_add' x y := by
    ext ⟨i, b⟩
    cases b <;> rfl
  map_smul' c x := by
    ext ⟨i, b⟩
    cases b <;> rfl

private theorem traceTwoNorm_le_coordinates (τ : FaithfulTracialState (Algebra M))
    {n : ℕ} (ξ η : Fin n → H)
    (hrep : ∀ a : Algebra M,
      τ.toLinearMap a = ∑ i, inner ℂ (η i) ((a : H →L[ℂ] H) (ξ i)))
    (x : Algebra M) :
    traceTwoNorm τ x ≤ ((n : ℝ) + 1) * ‖traceCoordinates ξ η x‖ := by
  have hxξ (i : Fin n) : ‖(x : H →L[ℂ] H) (ξ i)‖ ≤ ‖traceCoordinates ξ η x‖ := by
    exact norm_le_pi_norm (traceCoordinates ξ η x) (i, true)
  have hxη (i : Fin n) : ‖(x : H →L[ℂ] H) (η i)‖ ≤ ‖traceCoordinates ξ η x‖ := by
    exact norm_le_pi_norm (traceCoordinates ξ η x) (i, false)
  have hs : traceTwoNorm τ x ^ 2 ≤ (n : ℝ) * ‖traceCoordinates ξ η x‖ ^ 2 := by
    rw [traceTwoNorm_sq, hrep, Complex.re_sum]
    calc
      _ ≤ ∑ _i : Fin n, ‖traceCoordinates ξ η x‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        change (inner ℂ (η i) (star (x : H →L[ℂ] H) ((x : H →L[ℂ] H) (ξ i)))).re ≤ _
        rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
        calc
          _ ≤ ‖(x : H →L[ℂ] H) (η i)‖ * ‖(x : H →L[ℂ] H) (ξ i)‖ := by
            simpa only [RCLike.re_eq_complex_re] using
              re_inner_le_norm (𝕜 := ℂ) ((x : H →L[ℂ] H) (η i)) ((x : H →L[ℂ] H) (ξ i))
          _ ≤ ‖traceCoordinates ξ η x‖ * ‖traceCoordinates ξ η x‖ :=
            mul_le_mul (hxη i) (hxξ i) (norm_nonneg _) (norm_nonneg _)
          _ = _ := (pow_two _).symm
      _ = _ := by simp
  have hn : (n : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hb := mul_le_mul_of_nonneg_right hn (sq_nonneg ‖traceCoordinates ξ η x‖)
  have hp : 0 ≤ ((n : ℝ) + 1) * ‖traceCoordinates ξ η x‖ := by positivity
  nlinarith [traceTwoNorm_nonneg τ x]

/-- Every subset of a separably acting finite representation is separable
for its faithful trace two-norm. -/
theorem FiniteVectorTrace.traceSeparable [SeparableSpace H]
    {τ : FaithfulTracialState (Algebra M)} (hτ : FiniteVectorTrace τ)
    (S : Set (Algebra M)) : TraceSeparable τ S := by
  obtain ⟨n, ξ, η, hrep⟩ := hτ
  let F := traceCoordinates (M := M) ξ η
  obtain ⟨D, hDc, hDsub, hDdense⟩ := exists_countable_dense_subset (F '' S)
  choose lift hliftS hliftF using fun z : D => hDsub z.property
  let E : Set (Algebra M) := Set.range lift
  have hEc : E.Countable := by
    let := hDc.to_subtype
    exact Set.countable_range lift
  refine ⟨E, hEc, ?_, ?_⟩
  · rintro x ⟨z, rfl⟩
    exact hliftS z
  · intro x hx ε hε
    have hc : 0 < (n : ℝ) + 1 := by positivity
    obtain ⟨z, hz, hclose⟩ := Metric.mem_closure_iff.mp (hDdense ⟨x, hx, rfl⟩)
      (ε / ((n : ℝ) + 1)) (div_pos hε hc)
    let zD : D := ⟨z, hz⟩
    refine ⟨lift zD, ⟨zD, rfl⟩, ?_⟩
    have hb := traceTwoNorm_le_coordinates τ ξ η hrep (x - lift zD)
    have he : ‖F (x - lift zD)‖ = dist (F x) z := by
      rw [map_sub, hliftF zD, dist_eq_norm]
    change traceTwoNorm τ (x - lift zD) ≤ ((n : ℝ) + 1) * ‖F (x - lift zD)‖ at hb
    rw [he] at hb
    apply hb.trans_lt
    simpa only [mul_comm] using (lt_div_iff₀ hc).mp hclose

end

end KadisonKastler

end OAI
