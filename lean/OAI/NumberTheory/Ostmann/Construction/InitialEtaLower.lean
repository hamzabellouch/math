import OAI.NumberTheory.Ostmann.Construction.InitialEtaCRTSelected
import OAI.NumberTheory.Ostmann.Construction.InitialEtaRepeatedError

namespace OAI

open Erdos970

noncomputable section
open Filter
namespace Ostmann.Construction.InitialEta

theorem amplitude_lower_of_statistic {S X m : ℝ} {η e : ℂ}
    (hX : 0<X) (hm : 1 ≤ m)
    (hS : Real.sqrt X*Real.exp (-27*m)≤S)
    (heq : (S:ℂ)/(Real.sqrt X:ℂ)=η+e)
    (he : ‖e‖≤(1/2)*Real.exp (-27*m)) : Real.exp (-28*m)≤‖η‖ := by
  have hsqrt : 0<Real.sqrt X := Real.sqrt_pos.mpr hX
  have hSn : 0≤S := (mul_nonneg hsqrt.le (Real.exp_pos _).le).trans hS
  have hSdiv : Real.exp (-27*m)≤S/Real.sqrt X := (le_div_iff₀ hsqrt).mpr (by nlinarith)
  have hnorm := norm_add_le η e
  rw [← heq,norm_div,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,
    Real.norm_eq_abs,abs_of_nonneg hSn,abs_of_pos hsqrt] at hnorm
  have heta : (1/2)*Real.exp (-27*m)≤‖η‖ := by linarith
  have hexp : 2≤Real.exp m := by linarith [Real.add_one_le_exp m]
  have hsmall : Real.exp (-m)≤(1/2:ℝ) := by
    rw [Real.exp_neg]
    exact (inv_le_comm₀ (Real.exp_pos _) (by norm_num)).mpr (by norm_num at *; exact hexp)
  calc
    _ = Real.exp (-27*m)*Real.exp (-m) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-27*m)*(1/2) := mul_le_mul_of_nonneg_left hsmall (Real.exp_pos _).le
    _ ≤ ‖η‖ := by nlinarith

theorem initial_amplitude_lower_eventually (d : Decomposition)
    (Bs BD Bz : ℝ) (hBs : 200≤Bs) {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀ (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p) (hZ : 0<harmonicPrimeMass P),
      L/5000≤harmonicPrimeMass P →
      (∀p∈P,Real.exp ((1/2000:ℝ)*L)≤Real.log (p:ℝ) ∧
        Real.log (p:ℝ)≤Real.exp ((1/1000:ℝ)*L)) →
      Real.sqrt C.scale*Real.exp (-27*(Conclusion.bulkSize k L:ℝ))≤
        C.statistic (harmonicPrimeSource P hP hZ) →
      ∀G:ℝ,Real.exp (-28*(Conclusion.bulkSize k L:ℝ))≤
        ‖decompositionAmplitude d C.favorable C.sources (Conclusion.frequencyBound Bs BD Bz k L)
          C.giant (harmonicPrimeSource P hP hZ) C.scale G
          (Conclusion.bulkSize k L/2) (Conclusion.bulkSize k L/2) k C.bulkBin C.spectatorBin 0‖ := by
  filter_upwards [initial_repeatedContribution_error_eventually d Bs BD Bz hBs hk,
    eventually_initial_statistic_eq_amplitude_add_repeated Bs BD Bz (by linarith) hk,
    (Conclusion.bulkSize_tendsto_atTop hk).eventually_ge_atTop 1] with L he herr hm
  intro E C hG hGu hcl hcu hb hd P hP hZ hPH hsupport hstat G
  exact amplitude_lower_of_statistic (by exact_mod_cast initial_scale_pos C) hm hstat
    (herr C (harmonicPrimeSource P hP hZ) G)
    (he E C hG hGu hcl hcu hb hd P hP hZ hPH hsupport)

end Ostmann.Construction.InitialEta

end

end OAI
