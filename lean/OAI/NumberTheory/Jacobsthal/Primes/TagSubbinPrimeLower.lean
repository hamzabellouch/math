import OAI.NumberTheory.Jacobsthal.Paths.TagCutoffSeparation

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosStoppedTagSieve

open _root_.Filter
open scoped Topology
open Erdos970Dependency.SiegelWalfisz
open ErdosPrimeInputs.PrimeCountAbel (logarithmicIntegral)

lemma subbin_geometry (Cs xi w R V : ℝ) (hCs : 0 ≤ Cs) (hxi : 0 < xi) (hw : 3 ≤ w)
    (hR : Real.exp (w^((1:ℝ)/4)*Real.log w) ≤ R)
    (hlo : xi/(16*w^(2*Cs+10)) ≤ V/R) (hhi : V/R ≤ w^(-(2*Cs+10))) :
    0 < R ∧ 0 < V ∧ V ≤ R := by
  have hR0 : 0 < R := (Real.exp_pos _).trans_le hR
  have hw0 : 0 < w := by linarith
  have hlow : (xi/(16*w^(2*Cs+10)))*R ≤ V := (le_div_iff₀ hR0).mp hlo
  have hlow0 : 0 < (xi/(16*w^(2*Cs+10)))*R := by positivity
  have hwle : w^(-(2*Cs+10)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hvup := (div_le_iff₀ hR0).mp hhi
  exact ⟨hR0,hlow0.trans_le hlow,hvup.trans ((mul_le_mul_of_nonneg_right hwle hR0.le).trans_eq (one_mul R))⟩

theorem moving_subbin_prime_lower (Cs xi : ℝ) (hCs : 0 ≤ Cs) (hxi : 0 < xi) :
    ∃ w₀ : ℝ,3 ≤ w₀ ∧ ∀ w R V : ℝ,w₀ ≤ w →
      Real.exp (w^((1:ℝ)/4)*Real.log w) ≤ R →
      xi/(16*w^(2*Cs+10)) ≤ V/R → V/R ≤ w^(-(2*Cs+10)) →
      0 < R ∧ 0 < V ∧ V ≤ R ∧
      V/(4*Real.log R) ≤ ((intervalPrimes R V 1 0).card:ℝ) ∧
      0 < ((intervalPrimes R V 1 0).card:ℝ) := by
  obtain ⟨c,C,X₀,hc,hC,hX₀,hAP⟩ := interval_AP_li_error
  have hRate := eventually_moving_error (2*Cs+10) 0 0 c 1 (xi/(64*C))
    (by linarith) (by norm_num) (by norm_num) hc (by norm_num) (by positivity)
  obtain ⟨W,hW⟩ := eventually_atTop.mp hRate
  refine ⟨max 3 (max W X₀),le_max_left _ _,?_⟩
  intro w R V hw hR hlo hhi
  have hw3 : 3 ≤ w := (le_max_left _ _).trans hw
  have hwW : W ≤ w := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hw
  have hwX : X₀ ≤ w := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hw
  have hw0 : 0 < w := by linarith
  obtain ⟨hR0,hV0,hVR⟩ := subbin_geometry Cs xi w R V hCs hxi hw3 hR hlo hhi
  have hRw : w ≤ R := (moving_lower_ge_self (by linarith)).trans hR
  have hR3 : 3 ≤ R := hw3.trans hRw
  have hL : 0 < Real.log R := Real.log_pos (by linarith)
  have hp : 0 < w^(2*Cs+10) := Real.rpow_pos_of_pos hw0 _
  have hsmall := (hW w hwW).2 1 R (by norm_num) (by simp) hR
  simp only [Real.one_rpow,mul_one,one_mul] at hsmall
  have hmul := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 4*C*R/(w^(2*Cs+10)) by positivity)
  have hleft : (4*C*R/(w^(2*Cs+10)))*(w^(2*Cs+10)*Real.log R*Real.exp (-c*cubeHeight R))=
      4*C*R*Real.log R*Real.exp (-c*cubeHeight R) := by field_simp
  have hright : (4*C*R/(w^(2*Cs+10)))*(xi/(64*C))=(xi/(16*w^(2*Cs+10)))*R := by
    field_simp
    ring
  rw [hleft,hright] at hmul
  have hlow := (le_div_iff₀ hR0).mp hlo
  have herror : C*R*Real.exp (-c*cubeHeight R) ≤ V/(4*Real.log R) := by
    apply (le_div_iff₀ (show 0 < 4*Real.log R by positivity)).mpr
    convert hmul.trans hlow using 1
    ring
  have hmod1 : ((1:ℕ):ℝ) ≤ Real.exp (c*cubeHeight R) := by
    simpa only [Nat.cast_one] using Real.one_le_exp_iff.mpr (mul_nonneg hc.le (cubeHeight_pos (X := R) (by linarith)).le)
  have hErr := hAP R V (hwX.trans hRw) hV0.le hVR 1 0 (by norm_num) (by norm_num) hmod1
  simp only [Nat.totient_one,Nat.cast_one,div_one] at hErr
  have hMain : V/Real.log (R+V) ≤ logarithmicIntegral (R+V)-logarithmicIntegral R := by
    simpa only [add_sub_cancel_left] using logarithmicIntegral_sub_lower (by linarith : 2 ≤ R) (show R ≤ R+V by linarith)
  have hLog : Real.log (R+V) ≤ 2*Real.log R := by
    have he := Real.log_le_log (show 0 < R+V by linarith) (show R+V ≤ R^2 by nlinarith)
    simpa only [Real.log_pow,Nat.cast_ofNat] using he
  have hLogPos : 0 < Real.log (R+V) := Real.log_pos (by linarith)
  have hLI : V/(2*Real.log R) ≤ logarithmicIntegral (R+V)-logarithmicIntegral R :=
    (div_le_div_of_nonneg_left hV0.le hLogPos hLog).trans hMain
  have hsplit : V/(2*Real.log R)=V/(4*Real.log R)+V/(4*Real.log R) := by ring
  rw [hsplit] at hLI
  have hlower := (abs_le.mp hErr).1
  have hN : V/(4*Real.log R) ≤ ((intervalPrimes R V 1 0).card:ℝ) := by linarith
  exact ⟨hR0,hV0,hVR,hN,(by positivity : 0 < V/(4*Real.log R)).trans_le hN⟩

end ErdosStoppedTagSieve


end Erdos970

end OAI
