import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Choose

namespace OAI

namespace MarkovSuperreflexivity

theorem exists_linearMap_approx_subtype
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ι : E →ₗᵢ[ℝ] F) (hι : DenseRange ι)
    (V : Submodule ℝ F) [FiniteDimensional ℝ V]
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ T : V →ₗ[ℝ] E, ∀ v : V, ‖ι (T v) - (v : F)‖ ≤ δ * ‖v‖ := by
  classical
  let b := Module.finBasis ℝ V
  obtain ⟨C : ℝ, hC : 0 < C,
      hbound : ∀ {L : V →L[ℝ] F} {M : ℝ},
        0 ≤ M → (∀ i, ‖L (b i)‖ ≤ M) → ‖L‖ ≤ C * M⟩ :=
    b.exists_opNorm_le (F := F)
  let ρ : ℝ := δ / C
  have hρ : 0 < ρ := div_pos hδ hC
  have happrox : ∀ i : Fin (Module.finrank ℝ V),
      ∃ x : E, ‖ι x - (b i : F)‖ < ρ := by
    intro i
    obtain ⟨x, hx⟩ := hι.exists_dist_lt (b i : F) hρ
    exact ⟨x, by simpa only [dist_eq_norm'] using hx⟩
  choose a ha using happrox
  let T : V →ₗ[ℝ] E := b.constr ℝ a
  let U : V →L[ℝ] F :=
    LinearMap.toContinuousLinearMap (ι.toLinearMap.comp T - V.subtype)
  have hUb : ∀ i, ‖U (b i)‖ ≤ ρ := by
    intro i
    change ‖ι (b.constr ℝ a (b i)) - (b i : F)‖ ≤ ρ
    rw [b.constr_basis]
    exact (ha i).le
  have hU : ‖U‖ ≤ δ := by
    calc
      ‖U‖ ≤ C * ρ := hbound hρ.le hUb
      _ = δ := by
        dsimp only [ρ]
        exact mul_div_cancel₀ δ (ne_of_gt hC)
  refine ⟨T, ?_⟩
  intro v
  change ‖U v‖ ≤ δ * ‖v‖
  exact (U.le_opNorm v).trans (mul_le_mul_of_nonneg_right hU (norm_nonneg v))

end MarkovSuperreflexivity

end OAI
