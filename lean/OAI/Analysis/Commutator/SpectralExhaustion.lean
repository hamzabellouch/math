import Mathlib
import OAI.Analysis.Commutator.ProjectionStrong
import OAI.Analysis.Commutator.SpectralThresholdBounds

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PositiveWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem threshold_exhaustion (M : VonNeumannAlgebra H) {B : H →L[ℂ] H}
    (hBM : B∈M) (hB : 0≤B) (hi : Function.Injective B) :
    Monotone (fun n : ℕ => threshold B (1/((n:ℝ)+1))) ∧
      ∀ x,Tendsto (fun n : ℕ => threshold B (1/((n:ℝ)+1)) x) atTop (𝓝 x) := by
  let P (n : ℕ) := threshold B (1/((n:ℝ)+1))
  have hP (n : ℕ) : IsStarProjection (P n) := threshold_projection B _
  have hPM (n : ℕ) : P n∈M := threshold_mem M hBM _
  have hmono : Monotone P := by
    intro n m hnm
    apply threshold_antitone (IsSelfAdjoint.of_nonneg hB)
    apply one_div_le_one_div_of_le (by positivity : (0:ℝ)<(n:ℝ)+1)
    exact_mod_cast Nat.add_le_add_right hnm 1
  obtain ⟨W,hWM,hW,hPW,ht,hleast⟩ := ProjectionChains.exists_strong_sup M P hP hPM hmono
  have hnorm (n : ℕ) : ‖B*(1-W)‖≤1/((n:ℝ)+1) := by
    have he : P n*W=P n := ((hP n).le_iff_mul_eq_left hW).mp (hPW n)
    have hid : B*(1-W)=(B*(1-P n))*(1-W) := by noncomm_ring [he]
    rw [hid]
    calc
      _≤‖B*(1-P n)‖*‖1-W‖ := norm_mul_le _ _
      _≤(1/((n:ℝ)+1))*1 := mul_le_mul
        (threshold_remainder_norm hB (by positivity)) (hW.one_sub.norm_le _)
        (norm_nonneg _) (by positivity)
      _=1/((n:ℝ)+1) := mul_one _
  have hz : B*(1-W)=0 := norm_eq_zero.mp (le_antisymm
    (ge_of_tendsto (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)) (Eventually.of_forall hnorm))
    (norm_nonneg _))
  have he : W=1 := by
    ext x
    have hh : B ((1-W) x)=B 0 := by
      rw [map_zero]
      exact congrArg (fun T : H →L[ℂ] H => T x) hz
    have hx := hi hh
    change x-W x=0 at hx
    exact (sub_eq_zero.mp hx).symm
  refine ⟨hmono,?_⟩
  intro x
  simpa only [he,one_apply_eq_self] using ht x

end Kadison.PositiveWOT

end

end
end

end OAI
