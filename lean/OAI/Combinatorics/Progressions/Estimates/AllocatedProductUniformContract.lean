import OAI.Combinatorics.Progressions.Estimates.AllocatedFixedCommonCover

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq

variable {m dim : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {Psp E e p₁ : ℝ}

local notation "maskLog" => allocatedSiteKernelMaskLog m Psp
local notation "profileLog" => allocatedIdealProfileLog m p₁ e
local notation "accuracy" => allocatedOriginalCoverAccuracy Psp (E + 1)
local notation "tolerance" => allocatedSitePrimitiveTolerance m p₁ maskLog profileLog accuracy
local notation "cutoff" => allocatedRefinedPeriodCutoff m Psp

theorem allocatedProductUniformSourceContract_of_sampling
    (hPsp : 0 ≤ Psp) (hE : 0 ≤ E) (he : 0 ≤ e) (hp₁ : 0 ≤ p₁)
    (hmP : ((m + 1 : ℕ) : ℝ) ≤ Psp) (hdimSp : ((dim + 1 : ℕ) : ℝ) ≤ Psp)
    (hGsp : (Fintype.card G : ℝ) ≤ Psp) (hdimSmall : dim ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p₁)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p₁) (hn : ∀ j, (n j : ℝ) ≤ p₁)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p₁)
    (hcutoff : (cutoff : ℝ) ≤ Real.exp p₁) (hS : (S.value : ℝ) ≤ Real.exp p₁)
    (hEbudget : accuracy + 4 ≤ p₁)
    (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
      (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
      AllocatedFullGridResidueWitness (dim := dim) B U b S (q.val : ℕ) r.val)
    (hWitness : ∀ q r, AllocatedFullGridResidueSampling.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S (q.val : ℕ) (witnesses q r) tolerance) :
    AllocatedProductUniformSourceContract.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S Psp E e p₁ hPsp witnesses := by
  unfold AllocatedProductUniformSourceContract
  intro o X _ _ M modulus hM hmodulus hX hmodulusPos stride hs hstride index _ _
  have hperiodSp : (modulus : ℝ) ≤ Real.exp (Psp ^ 2) := by
    calc
      _ ≤ (M : ℝ) ^ (m + 1) := by exact_mod_cast hmodulus
      _ ≤ (Real.exp Psp) ^ (m + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hM _
      _ = Real.exp ((m + 1 : ℕ) * Psp) := (Real.exp_nat_mul Psp (m + 1)).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hmP hPsp])
  have hqM : residueRefinedPeriod modulus stride ≤ cutoff ^ (m + 1) :=
    allocatedRefinedPeriodIndex_power m hPsp index
  exact allocatedProductSourceContract_of_sampling B U b hR hσ S stride hs modulus tolerance
    (witnesses index) (hWitness index) hp₁ (allocatedSiteKernelMaskLog_nonneg m hPsp)
    (allocatedIdealProfileLog_nonneg m hp₁ he) he hE hPsp hdimSp hGsp hX hperiodSp hdimSmall
    hvars hI hn hJ cutoff hqM hcutoff hS le_rfl hEbudget le_rfl le_rfl o

end Erdos3.VectorPolynomial

end

end OAI
