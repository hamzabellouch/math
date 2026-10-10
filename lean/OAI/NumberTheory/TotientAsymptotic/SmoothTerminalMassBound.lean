import OAI.NumberTheory.TotientAsymptotic.SmoothTotientMass
import OAI.NumberTheory.TotientAsymptotic.CofactorMass

namespace OAI

/-! A single all-endpoint smooth residual mass bound for terminal slices. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem smooth_terminal_mass_bound : ∃ C : ℝ,0 < C ∧ ∀ t : ℝ,0 ≤ t →
    ∀ Q : Finset ℕ,(∀ v ∈ Q,IsTotient v ∧
      (largestPrimeFactor v:ℝ) ≤ Real.exp (Real.exp (t+1))) →
    (∑ v ∈ Q,(v:ℝ)⁻¹) ≤ C*Real.exp (10*(Real.log (t+5))^2) := by
  obtain ⟨C,hC,hmass⟩ := smooth_totient_reciprocal_mass
  have hB : Tendsto (fun y : ℕ => B y) atTop atTop := B_tendsto.comp tendsto_natCast_atTop_atTop
  obtain ⟨K,hK⟩ := eventually_atTop.mp
    (hmass.and ((hB.eventually (eventually_ge_atTop (1:ℝ))).and (eventually_ge_atTop (2:ℕ))))
  let D := primeEulerProduct K
  have hD : 0 < D := primeEulerProduct_pos K
  refine ⟨C+D,by positivity,?_⟩
  intro t ht Q hQ
  let y := ⌊Real.exp (Real.exp (t+1))⌋₊
  have hyQ (v) (hv : v ∈ Q) : largestPrimeFactor v ≤ y := Nat.le_floor (hQ v hv).2
  have he : 1 ≤ Real.exp (10*(Real.log (t+5))^2) := Real.one_le_exp (by positivity)
  by_cases hy : K ≤ y
  · obtain ⟨hmass,hBy,hy2⟩ := hK y hy
    have hypos : (0:ℝ) < y := by exact_mod_cast (show 0 < y by omega)
    have hlogy : 0 < Real.log (y:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
    have hyl : (y:ℝ) ≤ Real.exp (Real.exp (t+1)) := Nat.floor_le (Real.exp_pos _).le
    have hByupper : B y ≤ t+1 := by
      apply (Real.log_le_iff_le_exp hlogy).mpr
      exact (Real.log_le_iff_le_exp hypos).mpr hyl
    have hloglower : 0 ≤ Real.log (B y) := Real.log_nonneg hBy
    have hlogupper : Real.log (B y) ≤ Real.log (t+5) :=
      Real.log_le_log (zero_lt_one.trans_le hBy) (by linarith only [hByupper])
    have hs := hmass Q (fun v hv => ⟨(hQ v hv).1,hyQ v hv⟩)
    have hexp : Real.exp (10*(Real.log (B y))^2) ≤ Real.exp (10*(Real.log (t+5))^2) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [hloglower,hlogupper]
    exact (hs.trans (mul_le_mul_of_nonneg_left hexp hC.le)).trans
      (mul_le_mul_of_nonneg_right (by linarith only [hD]) (Real.exp_pos _).le)
  · have hs : (∑ v ∈ Q,(v:ℝ)⁻¹) ≤ D := by
      apply smooth_residual_reciprocal_mass
      intro v hv
      exact ⟨isTotient_pos (hQ v hv).1,(hyQ v hv).trans (by omega)⟩
    calc
      _ ≤ D := hs
      _ ≤ D*Real.exp (10*(Real.log (t+5))^2) := by nlinarith only [he,hD]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hC]) (Real.exp_pos _).le

end TotientAsymptotic

end

end OAI
