import OAI.NumberTheory.CubicMoment.Transform.MetaplecticLongDyads
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticRetainedPowers

namespace OAI

/-! The actual finite inverse-completion dyad count is a subpower of
the finite completion cutoff. -/
noncomputable section
namespace CubicFirstMoment

theorem metaplecticLongDyads_small_power {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ C F : ℝ, 1 ≤ F →
      ((metaplecticLongDyads C F).card:ℝ) ≤ K*F^ε := by
  obtain ⟨K,hK,hbound⟩ := metaplectic_dyad_count_small_power (half_pos hε)
  refine ⟨K,hK,?_⟩
  intro C F hF
  have hF0 : 0 ≤ F := le_trans zero_le_one hF
  have hcard : (metaplecticLongDyads C F).card ≤ Nat.log 2 ⌊3*F^2⌋₊+1 := by
    apply (metaplecticLongDyads_card hF0).trans
    apply Nat.add_le_add_right
    apply Nat.log_mono_right
    apply Nat.floor_mono
    nlinarith [sq_nonneg F]
  calc
    _ ≤ ((Nat.log 2 ⌊3*(F^2)⌋₊+1:ℕ):ℝ) := Nat.cast_le.mpr hcard
    _ ≤ K*(F^2)^(ε/2) := hbound (F^2) (one_le_pow₀ hF)
    _ = _ := by
      rw [←Real.rpow_natCast F 2,←Real.rpow_mul hF0]
      congr 2
      ring

end CubicFirstMoment

end

end OAI
