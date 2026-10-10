import OAI.MathematicalPhysics.Heisenberg.SpinAveragedKMS

namespace OAI

section
noncomputable section
open scoped Classical BigOperators ComplexConjugate
open Filter Topology
namespace Heisenberg

lemma complex_nat_inv_mul_re (n : ℕ) (z : ℂ) :
    ((n : ℂ)⁻¹ * z).re = z.re / (n : ℝ) := by
  have hc : (n : ℂ)⁻¹ = Complex.ofReal ((n : ℝ)⁻¹) := by
    simp only [Complex.ofReal_inv, Complex.ofReal_natCast]
  rw [hc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

lemma cubeAverage_order {d ℓ : ℕ} (Λ : Finset (Site d)) (hΛ : Λ.Nonempty)
    (ω : State d ℓ) (hmag : (Λ.card : ℝ) * ℓ / 8 ≤ (ω.functional (totalZ Λ)).re) :
    (ℓ : ℝ) / 8 ≤ ((cubeAverage Λ hΛ ω).functional (spinZ d ℓ 0)).re := by
  have hr := congrArg Complex.re (cubeAverage_spinZ Λ hΛ ω)
  rw [complex_nat_inv_mul_re] at hr
  rw [hr]
  have hp : 0 < (Λ.card : ℝ) := by exact_mod_cast hΛ.card_pos
  exact (le_div_iff₀ hp).mpr (by nlinarith)

theorem ordered_state_exists (d ℓ : ℕ) (hd : 2≤d) [NeZero ℓ] :
    ∃ β₀ : ℝ,0<β₀ ∧ ∀ β : ℝ,β₀≤β →
      ∃ ω : State (d+1) ℓ,TranslationInvariant ω ∧ IsKMS β ω ∧
        (ω.functional (spinZ (d+1) ℓ 0)).im=0 ∧
        (ℓ:ℝ)/8≤(ω.functional (spinZ (d+1) ℓ 0)).re := by
  obtain ⟨τ,hτ⟩:=exists_tracial_state (d+1) ℓ
  obtain ⟨β₀,hβ₀,horder⟩:=Selection.field_ordered_cubes d ℓ hd τ hτ
  refine ⟨β₀,hβ₀,?_⟩
  intro β hβ
  let h : ℕ → ℝ:=fun n=>(n+1:ℝ)⁻¹
  have hhpos (n : ℕ) : 0<h n := by dsimp [h]; positivity
  have hh : Tendsto h atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hex (n : ℕ) : ∃ m : ℕ,n ≤ m ∧
      ((box (d+1) (m+1)).card:ℝ)*ℓ/8≤
        ((gibbsState τ (shiftedField (box (d+1) (m+1)) (h n)) β).functional (totalZ (box (d+1) (m+1)))).re := by
    exact ((eventually_ge_atTop n).and (horder β hβ (h n) (hhpos n))).exists
  choose m hm hmag using hex
  let N : ℕ → ℕ:=fun n=>m n+1
  have hN : Tendsto N atTop atTop := tendsto_atTop_mono (fun n=>by exact (hm n).trans (Nat.le_succ _)) tendsto_id
  let η : ℕ → State (d+1) ℓ:=fun n=>gibbsState τ (shiftedField (box (d+1) (N n)) (h n)) β
  let ρ : ℕ → State (d+1) ℓ:=fun n=>cubeAverage (box (d+1) (N n)) (box_nonempty (d+1) (N n)) (η n)
  have hρ (n : ℕ) : (ℓ:ℝ)/8≤((ρ n).functional (spinZ (d+1) ℓ 0)).re :=
    cubeAverage_order _ _ (η n) (hmag n)
  obtain ⟨ω,κ,hκ,hω⟩:=state_subsequence ρ
  refine ⟨ω,?_,?_,?_,?_⟩
  · exact cubeAverage_limit_TI (N∘κ) (hN.comp hκ.tendsto_atTop) (η∘κ) ω hω
  · exact cubeAverage_limit_KMS τ hτ (lt_of_lt_of_le hβ₀ hβ) (N∘κ) (hN.comp hκ.tendsto_atTop)
      (h∘κ) (hh.comp hκ.tendsto_atTop) ω hω
  · exact state_selfAdjoint_im ω (star_spinZ (d+1) ℓ 0)
  · exact ge_of_tendsto (Complex.continuous_re.tendsto _ |>.comp (hω (spinZ (d+1) ℓ 0)))
      (Filter.Eventually.of_forall (fun n=>hρ (κ n)))

theorem spontaneous_magnetization (d ℓ : ℕ) (hd : 3≤d) (hℓ : 1≤ℓ) :
    DynamicsConverges d ℓ ∧
      ∃ β₀ : ℝ,0<β₀ ∧ ∀ β : ℝ,β₀≤β →
        ∃ ω : State d ℓ,TranslationInvariant ω ∧ IsKMS β ω ∧
          (ω.functional (spinZ d ℓ 0)).im=0 ∧
          (ℓ:ℝ)/8≤(ω.functional (spinZ d ℓ 0)).re := by
  have : NeZero ℓ:=⟨by omega⟩
  refine ⟨dynamics_converges d ℓ,?_⟩
  obtain ⟨k,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : d≠0)
  exact ordered_state_exists k ℓ (by omega)

end Heisenberg
end
end

end OAI
