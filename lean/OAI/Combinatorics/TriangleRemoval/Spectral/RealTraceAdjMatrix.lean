import Mathlib
import OAI.Combinatorics.TriangleRemoval.Spectral.ClosedWalkFamily

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
section RealTrace
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

lemma real_trace_adjMatrix_eq (n : ℕ) :
    Matrix.trace (G.adjMatrix ℝ ^ (n+3)) =
      ((graphEmbeddings (SimpleGraph.cycleGraph (n+3)) G).card : ℝ) +
        (nonsimpleWords G (n+3)).card := by
  have hNat := trace_adjMatrix_eq_closedWords G n
  rw [closedWords_card_eq] at hNat
  have ht : Matrix.trace (G.adjMatrix ℝ ^ (n+3)) =
      ((Matrix.trace (G.adjMatrix ℕ ^ (n+3)) : ℕ) : ℝ) := by
    simp only [Matrix.trace, Matrix.diag_apply, Nat.cast_sum,
      SimpleGraph.adjMatrix_pow_apply_eq_card_walk, Nat.cast_id]
  rw [ht, hNat, Nat.cast_add]

theorem normalized_link_trace_bound (n : ℕ) (hr : Even (n+3)) (D δ : ℝ)
    (hD : 1 ≤ D)
    (hdeg : ∀ x : V, ((Finset.univ.filter (G.Adj x)).card : ℝ) ≤ 2*D)
    (hmain : |((graphEmbeddings (SimpleGraph.cycleGraph (n+3)) G).card : ℝ) - D^(n+3)| ≤
      δ * D^(n+3))
    (hcyc : ∀ b, 3 ≤ b → b < n+3 →
      ((graphEmbeddings (SimpleGraph.cycleGraph b) G).card : ℝ) ≤ 2 * D^b) :
    |Matrix.trace (((D⁻¹) • G.adjMatrix ℝ) ^ (n+3)) - 1| ≤
      δ + ((n+3 : ℕ) : ℝ)^(n+4) * 2^(n+3) *
        ((Fintype.card V : ℝ) / D^((n+3)/2) + 1/D) := by
  classical
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hDne : D ≠ 0 := ne_of_gt hD0
  let Δ : ℕ := ⌊2*D⌋₊
  have hΔlo : D ≤ (Δ : ℝ) := by
    have hh := Nat.lt_floor_add_one (2*D)
    change 2*D < (Δ : ℝ)+1 at hh
    linarith
  have hΔhi : (Δ : ℝ) ≤ 2*D := Nat.floor_le (by positivity)
  have hΔ0 : 1 ≤ Δ := by exact_mod_cast hD.trans hΔlo
  have hdeg' : ∀ x : V, (Finset.univ.filter (G.Adj x)).card ≤ Δ := by
    intro x
    exact (Nat.le_floor_iff (by positivity : 0 ≤ 2*D)).mpr (hdeg x)
  have hcyc' : ∀ b, 3 ≤ b → b < n+3 →
      (graphEmbeddings (SimpleGraph.cycleGraph b) G).card ≤ 2 * Δ^b := by
    intro b hb hbr
    have hh := (hcyc b hb hbr).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hD0.le hΔlo b) (by norm_num : (0:ℝ) ≤ 2))
    exact_mod_cast hh
  have hcount := nonsimpleWords_card_le G n Δ 2 hΔ0 hdeg' hcyc'
  have hcountR : ((nonsimpleWords G (n+3)).card : ℝ) ≤
      ((n+3 : ℕ) : ℝ)^(n+4) *
        ((Fintype.card V : ℝ) * (2*D)^((n+3)/2) + 2*(2*D)^(n+2)) := by
    have hh : ((nonsimpleWords G (n+3)).card : ℝ) ≤
      ((n+3 : ℕ) : ℝ)^(n+4) *
        ((Fintype.card V : ℝ) * (Δ:ℝ)^((n+3)/2) + 2*(Δ:ℝ)^(n+2)) := by
      exact_mod_cast hcount
    refine hh.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact add_le_add
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg Δ) hΔhi _) (Nat.cast_nonneg _))
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg Δ) hΔhi _) (by norm_num))
  have hhalf : (n+3)/2 + (n+3)/2 = n+3 := by
    obtain ⟨k, hk⟩ := hr
    omega
  have hhalfle : (n+3)/2 ≤ n+3 := Nat.div_le_self _ _
  have hp2 : (2:ℝ)^((n+3)/2) ≤ 2^(n+3) := pow_le_pow_right₀ (by norm_num) hhalfle
  have hpow : D^(n+3) = D^((n+3)/2) * D^((n+3)/2) := by rw [← pow_add, hhalf]
  have hpow' : D^(n+3) = D^(n+2) * D := by rw [← pow_succ]
  have hratio : ((nonsimpleWords G (n+3)).card : ℝ) / D^(n+3) ≤
      ((n+3 : ℕ) : ℝ)^(n+4) * 2^(n+3) *
        ((Fintype.card V : ℝ) / D^((n+3)/2) + 1/D) := by
    apply (div_le_iff₀ (pow_pos hD0 _)).mpr
    have htree : (Fintype.card V : ℝ) * (2*D)^((n+3)/2) ≤
        2^(n+3) * ((Fintype.card V : ℝ)/D^((n+3)/2)) * D^(n+3) := by
      rw [mul_pow, hpow]
      field_simp
      nlinarith [mul_le_mul_of_nonneg_right hp2
        (mul_nonneg (Nat.cast_nonneg (Fintype.card V)) (pow_nonneg hD0.le ((n+3)/2)))]
    have hcycle : 2*(2*D)^(n+2) = 2^(n+3) * (1/D) * D^(n+3) := by
      rw [mul_pow, hpow', show n+3 = (n+2)+1 by omega, pow_succ]
      field_simp
      ring
    calc
      _ ≤ ((n+3 : ℕ) : ℝ)^(n+4) *
          ((Fintype.card V : ℝ) * (2*D)^((n+3)/2) + 2*(2*D)^(n+2)) := hcountR
      _ ≤ ((n+3 : ℕ) : ℝ)^(n+4) *
          (2^(n+3) * ((Fintype.card V : ℝ)/D^((n+3)/2)) * D^(n+3) +
            2^(n+3) * (1/D) * D^(n+3)) := mul_le_mul_of_nonneg_left (add_le_add htree hcycle.le) (by positivity)
      _ = _ := by ring
  have htrace : Matrix.trace (((D⁻¹) • G.adjMatrix ℝ) ^ (n+3)) =
      (((graphEmbeddings (SimpleGraph.cycleGraph (n+3)) G).card : ℝ) +
        (nonsimpleWords G (n+3)).card) / D^(n+3) := by
    rw [smul_pow, Matrix.trace_smul, real_trace_adjMatrix_eq]
    simp only [smul_eq_mul, inv_pow, div_eq_mul_inv, mul_comm]
  rw [htrace]
  calc
    _ = |(((graphEmbeddings (SimpleGraph.cycleGraph (n+3)) G).card : ℝ) - D^(n+3)) /
          D^(n+3) + (nonsimpleWords G (n+3)).card / D^(n+3)| := by
      congr 1
      field_simp
      ring
    _ ≤ |(((graphEmbeddings (SimpleGraph.cycleGraph (n+3)) G).card : ℝ) - D^(n+3)) /
          D^(n+3)| + |((nonsimpleWords G (n+3)).card : ℝ) / D^(n+3)| := abs_add_le _ _
    _ ≤ δ + ((n+3 : ℕ) : ℝ)^(n+4) * 2^(n+3) *
        ((Fintype.card V : ℝ) / D^((n+3)/2) + 1/D) := by
      apply add_le_add
      · rw [abs_div, abs_of_pos (pow_pos hD0 _)]
        exact (div_le_iff₀ (pow_pos hD0 _)).mpr hmain
      · rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (pow_nonneg hD0.le _))]
        exact hratio

end RealTrace
end SharpTerminalLeave

end
end

end OAI
