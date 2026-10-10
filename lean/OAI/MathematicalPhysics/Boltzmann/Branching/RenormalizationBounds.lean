import OAI.MathematicalPhysics.Boltzmann.Admissibility
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! # The manuscript's renormalizations have uniform Lipschitz bounds -/

noncomputable section

open Set
open scoped NNReal

namespace BoltzmannNonuniqueness.Renormalization

theorem exists_lipschitz (β : Renormalization) :
    ∃ C : ℝ≥0, LipschitzOnWith C β.toFun (Ici 0) := by
  obtain ⟨C,hC,hb⟩ := β.derivative_bound
  refine ⟨⟨C,hC⟩,(convex_Ici (0:ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun x hx => (β.regular.differentiableOn (by norm_num) x hx).hasDerivWithinAt) ?_⟩
  intro x hx
  have h : |derivWithin β.toFun (Ici 0) x| ≤ C :=
    (hb x hx).trans (div_le_self hC (by linarith only [show 0 ≤ x from hx]))
  exact_mod_cast h

theorem weighted_lipschitz {β : Renormalization} {C : ℝ≥0}
    (hβ : LipschitzOnWith C β.toFun (Ici 0)) {m u v : ℝ}
    (hm : 0 < m) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |m*β.toFun (u/m)-m*β.toFun (v/m)| ≤ (C:ℝ)*|u-v| := by
  have h := hβ.dist_le_mul (u/m) (div_nonneg hu hm.le) (v/m) (div_nonneg hv hm.le)
  simp only [Real.dist_eq] at h
  calc
    _ = m*|β.toFun (u/m)-β.toFun (v/m)| := by
      rw [← mul_sub,abs_mul,abs_of_pos hm]
    _ ≤ m*((C:ℝ)*|u/m-v/m|) := mul_le_mul_of_nonneg_left h hm.le
    _ = _ := by
      rw [← sub_div,abs_div,abs_of_pos hm]
      field_simp

theorem weighted_abs_bound {β : Renormalization} {C : ℝ≥0}
    (hβ : LipschitzOnWith C β.toFun (Ici 0)) {m u : ℝ} (hm : 0 < m) (hu : 0 ≤ u) :
    |m*β.toFun (u/m)| ≤ (C:ℝ)*u := by
  simpa only [zero_div,β.at_zero,mul_zero,sub_zero,abs_of_nonneg hu] using
    weighted_lipschitz hβ hm hu (le_refl (0:ℝ))

end BoltzmannNonuniqueness.Renormalization

end

end OAI
