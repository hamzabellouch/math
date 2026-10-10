import OAI.NumberTheory.DirichletL.Reflection.AnnularNormalization

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CompletedDyadic CompletedGauss ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ : Type*} [Fintype φ] {a c : Eis} {mode : Bool}

lemma frozenExtracted_eq_ideal (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3) (v : Fin 3) :
    frozenExtracted F jF e v = reflectionExtractedDivisor F.ideal jF e v := by
  simp only [frozenExtracted,PrimeFamily.generator_span]

theorem actual_kernel_terminal_threshold (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (m : ℕ) (Z T QK QP Qn Qb kn kb : ℝ)
    (hT : 0<T) (hK : 0<QK) (hP : 0<QP) (hn : 0<Qn) (hb : 0<Qb)
    (hkn : 0<kn) (hkb : 0<kb) :
    Real.logb Z (kn*Qn/Ideal.absNorm (frozenExtracted F jF e 1))+
      3*Real.logb Z (kb*Qb/Ideal.absNorm (frozenExtracted F jF e 2))+
      3*Real.logb Z (ramifiedScale 1 completedRamifiedStep m)-
      Real.logb Z (kernelCenter (actualKernelCoefficient F s m T) QK QP Qn Qb) =
    InverseTerminalWidths.terminalDualWidth Z (Real.logb Z QK) (Real.logb Z QP) (Real.logb Z T)
      F.ideal jF e +
    Real.logb Z (27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2*kn*kb^3) := by
  have hr : 0<ramifiedScale 1 completedRamifiedStep m := ramifiedScale_pos _ _
    (by norm_num) (lt_trans zero_lt_one completedRamifiedStep_gt_one) _
  have htau := sourceCuspScale_pos s.index
  have hp (I : Ideal Eis) (hI : I≠0) : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hcn := hp (Ideal.span {c}) (Ideal.span_singleton_eq_bot.not.mpr hc)
  have hfn := hp (∏ i, F.ideal i) (Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (F.ideal i)))
  have hd (v : Fin 3) := hp (frozenExtracted F jF e v) (frozenExtracted_ne_zero F jF e v)
  have hcc : actualKernelCoefficient F s m T =
      T/(27*(sourceCuspScale s.index)^2*
        ((Ideal.absNorm (Ideal.span {c}):ℝ)*(Ideal.absNorm (∏ i,F.ideal i):ℝ))^2)*
      (ramifiedScale 1 completedRamifiedStep m)^3 := by
    simp only [actualKernelCoefficient,fixedKernelCoefficient,map_one,Nat.cast_one,one_pow,mul_one,map_mul,Nat.cast_mul]
  rw [hcc,annular_kernel_threshold Z T (sourceCuspScale s.index)
    ((Ideal.absNorm (Ideal.span {c}):ℝ)*(Ideal.absNorm (∏ i,F.ideal i):ℝ))
    _ QK QP Qn Qb kn kb _ _ hT htau (mul_pos hcn hfn) hr hK hP hn hb hkn hkb (hd 1) (hd 2)]
  unfold InverseTerminalWidths.terminalDualWidth InverseTerminalWidths.normWidth
  rw [← frozenExtracted_eq_ideal F jF e 1,← frozenExtracted_eq_ideal F jF e 2]
  have hd1 := hd 1
  have hd2 := hd 2
  simp (disch := positivity) only [Real.logb_div,Real.logb_mul,Real.logb_pow]
  norm_num only [Nat.cast_ofNat]
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI
