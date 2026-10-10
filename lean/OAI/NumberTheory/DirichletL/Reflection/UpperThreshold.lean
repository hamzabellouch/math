import OAI.NumberTheory.DirichletL.Reflection.AnnularExponent

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CompletedDyadic CompletedGauss ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ : Type*} [Fintype φ] {a c : Eis} {mode : Bool}

theorem actual_kernel_upper_threshold (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (m : ℕ) (Z T QK QP Qn Qb kK kP kn kb : ℝ)
    (hT : 0<T) (hK : 0<QK) (hP : 0<QP) (hn : 0<Qn) (hb : 0<Qb)
    (hkK : 0<kK) (hkP : 0<kP) (hkn : 0<kn) (hkb : 0<kb) :
    Real.logb Z (kn*Qn/Ideal.absNorm (frozenExtracted F jF e 1))+
      3*Real.logb Z (kb*Qb/Ideal.absNorm (frozenExtracted F jF e 2))+
      3*Real.logb Z (ramifiedScale 1 completedRamifiedStep m)-
      Real.logb Z (kernelCenter (actualKernelCoefficient F s m T) QK QP Qn Qb) =
    InverseTerminalWidths.terminalDualWidth Z (Real.logb Z (kK*QK)) (Real.logb Z (kP*QP)) (Real.logb Z T)
      F.ideal jF e +
    Real.logb Z (27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2*kn*kb^3/(kK^2*kP^2)) := by
  rw [actual_kernel_terminal_threshold F jF e s hc m Z T QK QP Qn Qb kn kb hT hK hP hn hb hkn hkb]
  have hcn : (0:ℝ)<Ideal.absNorm (Ideal.span {c}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hc))
  have htau := sourceCuspScale_pos s.index
  unfold InverseTerminalWidths.terminalDualWidth
  rw [Real.logb_div (by positivity) (by positivity),Real.logb_mul hkK.ne' hK.ne',
    Real.logb_mul hkP.ne' hP.ne',Real.logb_mul (pow_ne_zero _ hkK.ne') (pow_ne_zero _ hkP.ne'),
    Real.logb_pow,Real.logb_pow]
  norm_num only [Nat.cast_ofNat]
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI
