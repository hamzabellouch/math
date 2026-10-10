import Mathlib
import OAI.Combinatorics.TriangleRemoval.Spectral.NormalizedOnes
import OAI.Combinatorics.TriangleRemoval.Spectral.RealTraceAdjMatrix

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix InnerProductSpace
open scoped BigOperators

namespace SharpTerminalLeave
open scoped BigOperators Matrix.Norms.L2Operator

section GraphStar
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem graph_star_approximation (n : ℕ) (hr : Even (n+3)) (D δ : ℝ)
    (hD : 1 ≤ D) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hrow : ∀ x : V, |((Finset.univ.filter (G.Adj x)).card : ℝ) - D| ≤ δ*D)
    (hmain : |((graphEmbeddings (SimpleGraph.cycleGraph (n+3)) G).card : ℝ) - D^(n+3)| ≤
      δ * D^(n+3))
    (hcyc : ∀ b, 3 ≤ b → b < n+3 →
      ((graphEmbeddings (SimpleGraph.cycleGraph b) G).card : ℝ) ≤ 2 * D^b) :
    ‖D⁻¹ • G.adjMatrix ℝ - averagingProjector‖ ≤
      4 * (((n+4 : ℕ) : ℝ) * δ + ((n+3 : ℕ) : ℝ)^(n+4) * 2^(n+3) *
        ((Fintype.card V : ℝ) / D^((n+3)/2) + 1/D)) ^ (1 / ((n+3 : ℕ) : ℝ)) + 7*δ := by
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hDne : D ≠ 0 := ne_of_gt hD0
  let W : ℝ := ((n+3 : ℕ) : ℝ)^(n+4) * 2^(n+3) *
        ((Fintype.card V : ℝ) / D^((n+3)/2) + 1/D)
  let E : ℝ := ((n+4 : ℕ) : ℝ)*δ + W
  let θ : ℝ := E ^ (1 / ((n+3 : ℕ) : ℝ))
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hθ : 0 ≤ θ := Real.rpow_nonneg hE _
  have hθpow : θ ^ (n+3) = E := by
    dsimp [θ]
    rw [← Real.rpow_mul_natCast hE]
    have hn : ((n+3 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [div_mul_cancel₀ _ hn,Real.rpow_one]
  have hdeg : ∀ x : V, ((Finset.univ.filter (G.Adj x)).card : ℝ) ≤ 2*D := by
    intro x
    have hh := (abs_le.mp (hrow x)).2
    nlinarith
  have htrace := normalized_link_trace_bound G n hr D δ hD hdeg hmain hcyc
  have hber : 1 - ((n+3 : ℕ) : ℝ)*δ ≤ (1-δ)^(n+3) := by
    simpa only [sub_eq_add_neg, mul_neg] using
      (one_add_mul_le_pow (a := -δ) (by linarith) (n+3))
  have htrace' : Matrix.trace ((D⁻¹ • G.adjMatrix ℝ)^(n+3)) ≤ (1-δ)^(n+3) + θ^(n+3) := by
    rw [hθpow]
    have hh := (abs_le.mp htrace).2
    dsimp [E]
    change Matrix.trace ((D⁻¹ • G.adjMatrix ℝ)^(n+3)) - 1 ≤ δ + W at hh
    push_cast at hber ⊢
    nlinarith
  have hrows : ∀ x : V, |(∑ y, (D⁻¹ • G.adjMatrix ℝ) x y) - 1| ≤ δ := by
    intro x
    have hsum : (∑ y, G.adjMatrix ℝ x y) =
        ((Finset.univ.filter (G.Adj x)).card : ℝ) := by
      simp only [SimpleGraph.adjMatrix_apply]
      exact Finset.sum_boole _ _
    simp only [Matrix.smul_apply,smul_eq_mul,← Finset.mul_sum,hsum]
    have heq : D⁻¹ * ((Finset.univ.filter (G.Adj x)).card : ℝ) - 1 =
        D⁻¹ * (((Finset.univ.filter (G.Adj x)).card : ℝ) - D) := by
      field_simp
    rw [heq,abs_mul,abs_of_pos (inv_pos.mpr hD0)]
    calc
      _ ≤ D⁻¹ * (δ*D) := mul_le_mul_of_nonneg_left (hrow x) (inv_nonneg.mpr hD0.le)
      _ = δ := by field_simp
  have hpos : ∀ x y, 0 ≤ (D⁻¹ • G.adjMatrix ℝ) x y := by
    intro x y
    change 0 ≤ D⁻¹ * G.adjMatrix ℝ x y
    exact mul_nonneg (inv_nonneg.mpr hD0.le) (by simp [SimpleGraph.adjMatrix_apply]; split_ifs <;> norm_num)
  exact star_approximation_from_trace _ ((G.isHermitian_adjMatrix ℝ).smul (isSelfAdjoint_iff.mpr rfl))
    δ θ hδ0 hδ1 hθ hpos hrows (n+3) hr (by omega) htrace'

end GraphStar
end SharpTerminalLeave

end
end

end OAI
