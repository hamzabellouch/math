import OAI.NumberTheory.Ostmann.QuadraticCenter.KernelCoefficientActual
import OAI.NumberTheory.Ostmann.QuadraticCenter.KernelFiberSelection
import OAI.NumberTheory.Ostmann.QuadraticSieveSigned

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Ostmann.QuadraticSieve Filter
open scoped BigOperators

theorem canonicalKernelImage_subset_signedSquarefree {S : Finset ℤ} {m U : ℕ} {h : ℤ}
    (hnz : ∀x∈S,(m:ℤ)*x-h≠0) (hbound : ∀x∈S,((m:ℤ)*x-h).natAbs≤U) :
    canonicalKernelImage S m h ⊆ signedSquarefreeUpTo U := by
  intro u hu
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hu
  exact mem_signedSquarefreeUpTo_iff_natAbs.mpr
    ⟨(canonicalSignedKernel_abs_le _).trans (hbound x hx),
      canonicalSignedKernel_ne_zero (hnz x hx),
      Int.squarefree_natAbs.mpr (canonicalSignedKernel_squarefree (hnz x hx))⟩

theorem canonicalKernelImage_card_mul_le_energy {S : Finset ℤ} {m U : ℕ} {h : ℤ}
    (hnz : ∀x∈S,(m:ℤ)*x-h≠0) (hbound : ∀x∈S,((m:ℤ)*x-h).natAbs≤U)
    (V : Finset ℕ) (b : ℕ → ℂ) {a : ℝ} (ha : 0≤a)
    (hlarge : ∀u∈canonicalKernelImage S m h,a≤‖∑s∈V,b s*(jacobiSym u s:ℂ)‖) :
    a^2*((canonicalKernelImage S m h).card:ℝ) ≤ signedJacobiEnergy U V b := by
  classical
  calc
    _ = ∑_u∈canonicalKernelImage S m h,a^2 := by simp [mul_comm]
    _ ≤ ∑u∈canonicalKernelImage S m h,‖∑s∈V,b s*(jacobiSym u s:ℂ)‖^2 := by
      apply Finset.sum_le_sum
      intro u hu
      exact pow_le_pow_left₀ ha (hlarge u hu) 2
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (canonicalKernelImage_subset_signedSquarefree hnz hbound) (fun _ _ _ => sq_nonneg _)

theorem actual_kernel_sieve_count_inputs_eventually (c : ℝ) (hc : 0<c) :
    ∀ᶠ T : ℝ in atTop, ∀ (Z : ℕ) (P : Finset ℕ),
      T/2≤Real.log Z → commonCenterCutoff Z≤P.card →
      (∀p∈P,Nat.Prime p) → (∀p∈P,Odd p) →
      ∀ H : ℕ,(∀p∈P,p≤H) → ∀ ε : ℕ → ℤ,(∀p∈P,ε p = -1 ∨ ε p = 1) →
      ∀ (S : Finset ℤ) (m U : ℕ) (h : ℤ),
      (∀x∈S,(m:ℤ)*x-h≠0) → (∀x∈S,((m:ℤ)*x-h).natAbs≤U) →
      (∀x∈S,c≤|signedJacobiAverage P ε (canonicalSignedKernel ((m:ℤ)*x-h))|) →
      let k := evenMomentParameter (parameterX T) Z
      (∑s∈kernelCoefficientInterval (H^k),‖kernelCoefficient P ε k s‖^2)≤
        (k.factorial:ℝ)/(P.card:ℝ)^k ∧
      (c^k/2)^2*((canonicalKernelImage S m h).card:ℝ)≤
        signedJacobiEnergy U (kernelCoefficientInterval (H^k)) (kernelCoefficient P ε k) := by
  filter_upwards [kernelCoefficient_actual_package_eventually c hc] with T hT
  intro Z P hZ hPJ hP ho H hH ε hε S m U h hnz hbound hbias
  have hp := hT Z P hZ hPJ hP ho H hH ε hε
  refine ⟨hp.2.1,?_⟩
  apply canonicalKernelImage_card_mul_le_energy hnz hbound _ _ (by positivity)
  intro u hu
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hu
  apply hp.2.2
  simpa only [signAverage,signedJacobiAverage] using hbias x hx

end Ostmann.QuadraticCenter

end

end OAI
