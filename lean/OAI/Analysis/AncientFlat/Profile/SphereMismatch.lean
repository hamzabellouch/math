import OAI.Analysis.AncientFlat.Profile.SphereErrorBounds
import OAI.Analysis.AncientFlat.Profile.SphereScaling

namespace OAI
noncomputable section
open scoped ContDiff Laplacian
namespace CompactCore
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
theorem compact_mismatch_bound :
    ∃ K : ℝ, 0<K ∧ ∀ (f : V → ℂ), ContDiff ℝ ∞ f →
      ∀ q : ℝ, 0≤q → q≤1 → ∀ x : V, ‖x‖≤1 →
      ∀ M : ℝ, 0≤M →
      (∀ j : ℕ, j≤4 → ‖iteratedFDeriv ℝ j (fun y => f (q • y)) x‖≤M) →
      ‖(q:ℂ)^4*compactOp f (q • x)-flatOp (fun y => f (q • y)) x‖≤K*q^2*M := by
  refine ⟨310*(Module.finrank ℝ V:ℝ)+13392,by positivity,?_⟩
  intro f hf q hq hq1 x hx M hM hb
  have hs : ContDiff ℝ ∞ (fun y => f (q • y)) := hf.comp (by fun_prop)
  obtain ⟨h2,h4⟩ := error_norm_bounds _ hs x hx M hM hb
  have hq2 : q^2≤1 := by nlinarith
  have hq4 : q^4≤q^2 := by nlinarith [sq_nonneg q]
  rw [compact_scaled f hf q x]
  calc
    _ ≤ ‖(q:ℂ)^2/16*errorTwo (fun y => f (q • y)) x‖+
        ‖(q:ℂ)^4/16*errorFour (fun y => f (q • y)) x‖ := norm_add_le _ _
    _ = q^2/16*‖errorTwo (fun y => f (q • y)) x‖+
        q^4/16*‖errorFour (fun y => f (q • y)) x‖ := by
      simp only [norm_mul,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hq]
      norm_num
    _ ≤ q^2/16*(310*(Module.finrank ℝ V:ℝ)*M)+q^4/16*(13392*M) :=
      add_le_add (mul_le_mul_of_nonneg_left h2 (by positivity))
        (mul_le_mul_of_nonneg_left h4 (by positivity))
    _ ≤ q^2*(310*(Module.finrank ℝ V:ℝ)*M)+q^2*(13392*M) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg q]) (by positivity)
      · exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg q]) (by positivity)
    _ = _ := by ring
end CompactCore

end

end OAI
