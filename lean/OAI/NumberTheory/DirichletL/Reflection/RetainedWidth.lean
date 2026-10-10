import OAI.NumberTheory.DirichletL.Reflection.FamilyTail
import OAI.NumberTheory.DirichletL.Reflection.UpperThreshold

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CompletedDyadic CompletedGauss ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u
variable {a c : Eis} {mode : Bool}

lemma family_center_eq_kernel {φ : Type u} [Fintype φ] (F : PrimeFamily φ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (X QK QP : ℝ) (i : ℕ×ℕ×ℕ) :
    rawDyadicCenter (familyRawScale F s X QK QP) i=
      kernelCenter (actualKernelCoefficient F s i.1 X) QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) := by
  unfold rawDyadicCenter familyRawScale kernelCenter actualKernelCoefficient fixedKernelCoefficient
  simp only [map_one,Nat.cast_one,one_pow,mul_one,ramifiedScale,pow_zero,one_mul]
  ring

theorem actual_retained_width_uniform
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (kK kP kn kb η : ℝ) (hkK : 0<kK) (hkP : 0<kP) (hkn : 0<kn) (hkb : 0<kb) (hη : 0<η) :
    ∃ Z₀ : ℝ, 1<Z₀ ∧ ∀ {φ : Type u} [Fintype φ],
    ∀ (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3) (Z X QK QP δ : ℝ) (i : ℕ×ℕ×ℕ),
      Z₀≤Z → 0<X → 0<QK → 0<QP →
      i∈retainedDyads (familyRawScale F s X QK QP) (16*Z^δ) →
      Real.logb Z (kn*((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted F jF e 1))+
        3*Real.logb Z (kb*((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted F jF e 2))+
        InverseTerminalWidths.ramifiedWidth Z i.1 ≤
      InverseTerminalWidths.terminalDualWidth Z (Real.logb Z (kK*QK)) (Real.logb Z (kP*QP)) (Real.logb Z X)
        F.ideal jF e + δ+η := by
  let Cf := 27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2*kn*kb^3/(kK^2*kP^2)
  have hcn : (0:ℝ)<Ideal.absNorm (Ideal.span {c}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hc))
  have htau := sourceCuspScale_pos s.index
  have hCf : 0<Cf := by dsimp only [Cf]; positivity
  obtain ⟨Z₀,hZ₀,hlog⟩ := InverseTerminalWidths.constant_log_error (16*Cf) η (by positivity) hη
  refine ⟨Z₀,hZ₀,?_⟩
  intro φ _ F jF e Z X QK QP δ i hZ hX hQK hQP hi
  have hz : 1<Z := lt_of_lt_of_le hZ₀ hZ
  have hs := familyRawScale_pos F s hc X QK QP hX hQK hQP
  have hret := (mem_retainedDyads _ _ hs i).mp hi
  rw [family_center_eq_kernel] at hret
  have hR : 0<kernelCenter (actualKernelCoefficient F s i.1 X) QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) := by
    have hcoef := actualKernelCoefficient_pos F s hc i.1 X hX
    unfold kernelCenter
    positivity
  have hrl := Real.logb_le_logb_of_le hz hR hret
  rw [Real.logb_mul (by norm_num : (16:ℝ)≠0) (Real.rpow_pos_of_pos (lt_trans zero_lt_one hz) δ).ne',
    Real.logb_rpow (lt_trans zero_lt_one hz) (ne_of_gt hz)] at hrl
  have he := actual_kernel_upper_threshold F jF e s hc i.1 Z X QK QP
    ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) kK kP kn kb hX hQK hQP (by positivity) (by positivity) hkK hkP hkn hkb
  rw [literal_ramified_width_offset] at he
  have hl : Real.logb Z 16+Real.logb Z Cf≤η := by
    rw [←Real.logb_mul (by norm_num : (16:ℝ)≠0) hCf.ne']
    exact hlog Z hZ
  have hoff : 0≤4*Real.logb Z 3 := mul_nonneg (by norm_num) (Real.logb_nonneg hz (by norm_num))
  change _ = _+Real.logb Z Cf at he
  linarith
end
end SevenEighths.InverseReflectedPhase

end OAI
