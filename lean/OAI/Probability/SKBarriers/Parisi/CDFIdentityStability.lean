import Mathlib
import OAI.Probability.SKBarriers.Parisi.CDFConditionalStability

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDF_susceptibility_square_le_one (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (h1 : α 1=1) {r u : ℝ}
    (hr : 0≤r) (hru : r<u) (hu : u≤1)
    (hΓ : ∀ s∈Icc r u,scalarCDFOverlap β α s=s) :
    β^2*scalarCDFSusceptibilitySquareAverage β α r≤1 := by
  let d (n : ℕ) : ℝ := (u-r)/((n:ℝ)+1)
  have hd (n : ℕ) : 0<d n := div_pos (sub_pos.mpr hru) (by positivity)
  have hdle (n : ℕ) : d n≤u-r := by
    dsimp [d]
    apply div_le_self (sub_nonneg.mpr hru.le)
    linarith [Nat.cast_nonneg (α:=ℝ) n]
  have H (n : ℕ) : β^2*scalarCDFSusceptibilitySquareAverage β α r≤1+2*(β^2*d n) := by
    have hqin : r+d n∈Icc r u := ⟨by linarith [hd n],by linarith [hdle n]⟩
    have G := scalarCDF_conditional_stability β α ha h1 hr hqin.1 (hqin.2.trans hu)
    rw [hΓ (r+d n) hqin,hΓ r ⟨le_rfl,hru.le⟩] at G
    have G' : d n*(β^2*scalarCDFSusceptibilitySquareAverage β α r)≤d n*(1+2*(β^2*d n)) := by
      nlinarith [G]
    exact (mul_le_mul_iff_right₀ (hd n)).mp (by simpa only [mul_comm] using G')
  have ht : Tendsto d atTop (𝓝 0) := by
    simpa only [d,mul_zero,mul_one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul (u-r)
  have Hlim : Tendsto (fun n => 1+2*(β^2*d n)) atTop (𝓝 1) := by
    simpa only [mul_zero,add_zero] using ((ht.const_mul (β^2)).const_mul 2).const_add 1
  exact ge_of_tendsto Hlim (Eventually.of_forall H)

end SK.Analytic

end
end

end OAI
