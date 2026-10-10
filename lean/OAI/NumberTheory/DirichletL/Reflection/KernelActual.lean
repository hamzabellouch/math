import OAI.NumberTheory.DirichletL.Reflection.KernelSource
import OAI.NumberTheory.DirichletL.Descent.ReflectedDual

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CompletedDyadic ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

lemma fixedKernelCoefficient_pos (X tau r : ℝ) (C D1 D2 : Ideal Eis)
    (hX : 0<X) (htau : 0<tau) (hr : 0<r) (hC : C≠0) (hD1 : D1≠0) (hD2 : D2≠0) :
    0<fixedKernelCoefficient X tau r C D1 D2 := by
  have hn (I : Ideal Eis) (hI : I≠0) : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hCn := hn C hC
  have h1 := hn D1 hD1
  have h2 := hn D2 hD2
  unfold fixedKernelCoefficient
  positivity

def actualKernelCoefficient (F : PrimeFamily φ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (m : ℕ) (X : ℝ) : ℝ :=
  fixedKernelCoefficient X (sourceCuspScale s.index) (ramifiedScale 1 completedRamifiedStep m)
    (Ideal.span {c}*(∏ i, F.ideal i)) 1 1

lemma actualKernelCoefficient_pos (F : PrimeFamily φ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c≠0) (m : ℕ) (X : ℝ) (hX : 0<X) : 0<actualKernelCoefficient F s m X := by
  apply fixedKernelCoefficient_pos _ _ _ _ _ _ hX (sourceCuspScale_pos _)
    (ramifiedScale_pos _ _ (by norm_num) (lt_trans zero_lt_one completedRamifiedStep_gt_one) _) _ one_ne_zero one_ne_zero
  apply mul_ne_zero
  · exact Ideal.span_singleton_eq_bot.not.mpr hc
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (F.ideal i))

theorem actual_theta_kernel_argument (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (m : ℕ) (X : ℝ) (n b : Ideal Eis) :
    (X/(27*(sourceCuspScale s.index)^2*
      (Ideal.absNorm (Ideal.span {c*∏ i, (F.reflected K hK S).generator i}):ℝ)^2))*
      (ramifiedScale 1 completedRamifiedStep m)^3*(Ideal.absNorm n:ℝ)*(Ideal.absNorm b:ℝ)^3 =
    actualKernelCoefficient F s m X*(Ideal.absNorm n:ℝ)*(Ideal.absNorm b:ℝ)^3/
      ((Ideal.absNorm K:ℝ)^2*(Ideal.absNorm (∏ i, S.ideal i):ℝ)^2) := by
  simpa only [one_mul,actualKernelCoefficient] using source_kernel_argument_factor F K hK S c
    X (sourceCuspScale s.index) (ramifiedScale 1 completedRamifiedStep m) 1 1 n b

def actualKernelSourceTerm (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ→ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) (windows : Fin 4→ℝ→ℂ)
    (QK QP Qn Qb : ℝ) (W : ℝ→ℂ) (θ X : ℝ) : ℂ :=
  actualMixedCoefficient F K hK S jF D s hc u m n b *
    ((∏ i, windows i (kernelLogCoordinates QK QP Qn Qb (Ideal.absNorm K:ℝ)
      (Ideal.absNorm (∏ i, S.ideal i):ℝ) (Ideal.absNorm n:ℝ) (Ideal.absNorm b:ℝ) i)) /
      ((ramifiedScale 1 completedRamifiedStep m*Real.sqrt (Ideal.absNorm n:ℝ)*(Ideal.absNorm b:ℝ):ℝ):ℂ) *
      CubicReflectionKernel.paperKernel (Vstar (CompletedHeight.normTwistedSource W θ))
        ((X/(27*(sourceCuspScale s.index)^2*
          (Ideal.absNorm (Ideal.span {c*∏ i, (F.reflected K hK S).generator i}):ℝ)^2))*
          (ramifiedScale 1 completedRamifiedStep m)^3*(Ideal.absNorm n:ℝ)*(Ideal.absNorm b:ℝ)^3))

theorem actualKernelSourceTerm_numeric (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ→ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) (windows : Fin 4→ℝ→ℂ)
    (QK QP Qn Qb : ℝ) (W : ℝ→ℂ) (θ X : ℝ) :
    actualKernelSourceTerm F K hK S jF D s hc u m n b windows QK QP Qn Qb W θ X =
    actualMixedCoefficient F K hK S jF D s hc u m n b *
      ((∏ i, windows i (kernelLogCoordinates QK QP Qn Qb (Ideal.absNorm K:ℝ)
        (Ideal.absNorm (∏ i, S.ideal i):ℝ) (Ideal.absNorm n:ℝ) (Ideal.absNorm b:ℝ) i)) /
        ((ramifiedScale 1 completedRamifiedStep m*Real.sqrt (Ideal.absNorm n:ℝ)*(Ideal.absNorm b:ℝ):ℝ):ℂ) *
        CubicReflectionKernel.paperKernel (Vstar (CompletedHeight.normTwistedSource W θ))
          (actualKernelCoefficient F s m X*(Ideal.absNorm n:ℝ)*(Ideal.absNorm b:ℝ)^3/
            ((Ideal.absNorm K:ℝ)^2*(Ideal.absNorm (∏ i, S.ideal i):ℝ)^2))) := by
  unfold actualKernelSourceTerm
  rw [actual_theta_kernel_argument]

end
end SevenEighths.InverseReflectedPhase

end OAI
