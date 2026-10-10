import OAI.Analysis.KadisonKastler.TraceUnitaryImages

namespace OAI

/-! # Passing the group approximation bound to every unitary -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H E I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {M N : VonNeumannAlgebra H}

/-- Uniform operator-norm bounds on the group elements extend to every
unitary through the two finite traces and their strong continuity. -/
theorem unitary_transfer_bound_of_traceDense
    (τM : FaithfulTracialState (Algebra M)) (τN : FaithfulTracialState (Algebra N))
    (hτM : FiniteVectorTrace τM) (hτN : FiniteVectorTrace τN)
    (J : Algebra M →ₗ[ℂ] E) (K : Algebra N →ₗ[ℂ] E)
    (hJ : ∀ a, ‖J a‖ = traceTwoNorm τM a)
    (hK : ∀ a, ‖K a‖ = traceTwoNorm τN a)
    (S : unitary (E →L[ℂ] E)) (θ : Algebra M →ₗ[ℂ] Algebra N)
    (hθ : ∀ a, K (θ a) = (S : E →L[ℂ] E) (J a))
    (hθU : ∀ u : unitary (Algebra M), θ u ∈ unitary (Algebra N))
    (ρ : I → unitary (Algebra M))
    (hρ : ∀ u : unitary (Algebra M), ∀ ε : ℝ, 0 < ε →
      ∃ i, traceTwoNorm τM ((u : Algebra M) - ρ i) < ε)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ i, ‖(θ (ρ i) : H →L[ℂ] H) - (ρ i : Algebra M)‖ ≤ C)
    (u : unitary (Algebra M)) :
    ‖(θ u : H →L[ℂ] H) - (u : Algebra M)‖ ≤ C := by
  classical
  choose index hindex using fun n : ℕ =>
    hρ u (1 / ((n : ℝ) + 1)) (by positivity)
  let g : ℕ → Algebra M := fun n => ρ (index n)
  have hM2 : Tendsto (fun n => traceTwoNorm τM (g n - u)) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => traceTwoNorm_nonneg _ _)
      (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [g, traceTwoNorm_sub_comm τM] using (hindex n).le
  have hN2 : Tendsto (fun n => traceTwoNorm τN (θ (g n) - θ u)) atTop (𝓝 0) := by
    have he (n : ℕ) : traceTwoNorm τN (θ (g n) - θ u) = traceTwoNorm τM (g n - u) := by
      rw [← hK, map_sub, hθ, hθ, ← map_sub, Unitary.norm_map, ← map_sub, hJ]
    simpa only [he] using hM2
  have hg1 (n : ℕ) : ‖g n‖ ≤ 1 := norm_unitary_le_one (ρ (index n))
  have hθg1 (n : ℕ) : ‖θ (g n)‖ ≤ 1 :=
    norm_unitary_le_one (⟨θ (g n), hθU (ρ (index n))⟩ : unitary (Algebra N))
  have hu1 : ‖(u : Algebra M)‖ ≤ 1 := norm_unitary_le_one u
  have hθu1 : ‖θ u‖ ≤ 1 :=
    norm_unitary_le_one (⟨θ u, hθU u⟩ : unitary (Algebra N))
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro ξ
  have hMs := hτM.strongContinuous.tendsto atTop (fun n => g n - u)
    (show (0 : ℝ) ≤ 2 by norm_num)
    (fun n => (norm_sub_le _ _).trans (by linarith [hg1 n])) hM2 ξ
  have hNs := hτN.strongContinuous.tendsto atTop (fun n => θ (g n) - θ u)
    (show (0 : ℝ) ≤ 2 by norm_num)
    (fun n => (norm_sub_le _ _).trans (by linarith [hθg1 n])) hN2 ξ
  have hMs' : Tendsto (fun n => (g n : H →L[ℂ] H) ξ) atTop
      (𝓝 ((u : Algebra M).val ξ)) := by
    apply tendsto_sub_nhds_zero_iff.mp
    exact hMs
  have hNs' : Tendsto (fun n => (θ (g n) : H →L[ℂ] H) ξ) atTop
      (𝓝 ((θ u : H →L[ℂ] H) ξ)) := by
    apply tendsto_sub_nhds_zero_iff.mp
    exact hNs
  have hl := (hNs'.sub hMs').norm
  exact le_of_tendsto hl (Eventually.of_forall fun n =>
    ((θ (g n) : H →L[ℂ] H) - (g n : H →L[ℂ] H)).le_of_opNorm_le
      (hbound (index n)) ξ)

end

end KadisonKastler

end OAI
