import OAI.Probability.SwitchChain.PairFiberConnectivity
import OAI.Probability.SwitchChain.SpectralFromSquare

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Problem315.PairResampling
attribute [local instance] Classical.propDecidable

theorem generator_centered_poincare {n : Nat} {d : Fin n → Nat}
    (hsquare : ∀ f : StateSpace n d,
      ⟪f, generator n d f⟫ ≤ ⟪generator n d f, generator n d f⟫)
    (f : StateSpace n d) (hf : ∑ G : GraphState n d, f G = 0) :
    ‖f‖ ^ 2 ≤ ⟪f, generator n d f⟫ := by
  classical
  apply Analytic.norm_sq_le_inner_of_square_ge (generator n d).toLinearMap
    generator_isSymmetric generator_nonneg hsquare f
  intro y hy
  have hconst := (generator_eq_zero_iff_constant y).mp hy
  by_cases hne : Nonempty (GraphState n d)
  · let G : GraphState n d := Classical.choice hne
    rw [state_inner]
    simp_rw [hconst _ G]
    rw [← Finset.mul_sum, hf, mul_zero]
  · have : IsEmpty (GraphState n d) := not_nonempty_iff.mp hne
    simp [state_inner]

theorem uniformVariance_le_generator {n : Nat} {d : Fin n → Nat}
    (hgraph : Graphical n d)
    (hsquare : ∀ f : StateSpace n d,
      ⟪f, generator n d f⟫ ≤ ⟪generator n d f, generator n d f⟫)
    (f : GraphState n d → ℝ) :
    uniformVariance n d f ≤
      ⟪WithLp.toLp 2 f, generator n d (WithLp.toLp 2 f)⟫ / (stateCount n d : ℝ) := by
  classical
  let : Nonempty (GraphState n d) := hgraph
  have hN : (0 : ℝ) < (stateCount n d : ℝ) := by
    exact_mod_cast (show 0 < stateCount n d by
      simpa only [stateCount, allGraphStates, Finset.card_univ] using
        (Fintype.card_pos (α := GraphState n d)))
  let v : StateSpace n d := WithLp.toLp 2 f
  let c : ℝ := uniformAverage n d f
  let k : StateSpace n d := WithLp.toLp 2 (fun _ : GraphState n d => c)
  let x : StateSpace n d := v - k
  have hx : (∑ G : GraphState n d, x G) = 0 := by
    simp only [x, v, k, PiLp.sub_apply]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change (∑ G : GraphState n d, f G) - (Fintype.card (GraphState n d) : ℝ) *
      ((∑ G : GraphState n d, f G) / (stateCount n d : ℝ)) = 0
    have hcard : (Fintype.card (GraphState n d) : ℝ) = stateCount n d := rfl
    rw [hcard]
    field_simp
    ring
  have hk : generator n d k = 0 := generator_constant c
  have hgen : generator n d x = generator n d v := by
    change generator n d (v - k) = generator n d v
    rw [map_sub, hk, sub_zero]
  have horth : ⟪k, generator n d v⟫ = 0 := by
    have h := generator_isSymmetric (n := n) (d := d) k v
    change ⟪generator n d k, v⟫ = ⟪k, generator n d v⟫ at h
    rw [hk, inner_zero_left] at h
    exact h.symm
  have henergy : ⟪x, generator n d x⟫ = ⟪v, generator n d v⟫ := by
    rw [hgen]
    change ⟪v - k, generator n d v⟫ = _
    rw [inner_sub_left, horth, sub_zero]
  have hnorm : ‖x‖ ^ 2 = ∑ G ∈ allGraphStates n d, (f G - c) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, state_inner]
    simp only [x, v, k, PiLp.sub_apply, allGraphStates, pow_two]
  have hp := generator_centered_poincare hsquare x hx
  rw [henergy, hnorm] at hp
  exact div_le_div_of_nonneg_right hp (le_of_lt hN)

theorem spectralGap_of_square_and_comparison {n : Nat} {d : Fin n → Nat}
    (hn : 4 ≤ n) (hgraph : Graphical n d)
    (hsquare : ∀ f : StateSpace n d,
      ⟪f, generator n d f⟫ ≤ ⟪generator n d f, generator n d f⟫)
    (hcomparison : ∀ f : GraphState n d → ℝ,
      ⟪WithLp.toLp 2 f, generator n d (WithLp.toLp 2 f)⟫ / (stateCount n d : ℝ) ≤
        (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ)) * dirichletEnergy n d f) :
    hasSpectralGapAtLeast n d ((1 : ℝ) /
      (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ))) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hc : (0 : ℝ) < (Nat.choose n 4 : ℝ) := by exact_mod_cast Nat.choose_pos hn
  have hD : (0 : ℝ) < 24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ) := by positivity
  intro f
  have h := (uniformVariance_le_generator hgraph hsquare f).trans (hcomparison f)
  rw [one_div, ← div_eq_inv_mul]
  apply (div_le_iff₀ hD).mpr
  simpa only [mul_comm] using h

end Problem315.PairResampling

end

end OAI
