import OAI.Analysis.Mahler.ExteriorPower
import OAI.Analysis.Mahler.NormSquareForm

namespace OAI

open Complex
open scoped BigOperators

namespace Mahler

lemma alternatingMap_sum_apply {T : Type*} [AddCommGroup T] [Module ℝ T]
    {ι J : Type*} (s : Finset J) (a : J → T [⋀^ι]→ₗ[ℝ] ℂ) (v : ι → T) :
    (∑ j ∈ s, a j) v = ∑ j ∈ s, a j v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; rfl
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    change a j v + (∑ i ∈ s, a i) v = _
    rw [ih]

noncomputable def realCoordinate {n : ℕ} (j : Fin n) : ComplexEuclidean n →ₗ[ℝ] ℂ :=
  (Complex.ofRealCLM.comp (Complex.reCLM.comp ((EuclideanSpace.proj (𝕜 := ℂ) j).restrictScalars ℝ))).toLinearMap
noncomputable def imagCoordinate {n : ℕ} (j : Fin n) : ComplexEuclidean n →ₗ[ℝ] ℂ :=
  (Complex.ofRealCLM.comp (Complex.imCLM.comp ((EuclideanSpace.proj (𝕜 := ℂ) j).restrictScalars ℝ))).toLinearMap

@[simp] lemma realCoordinate_apply {n : ℕ} (j : Fin n) (v : ComplexEuclidean n) :
    realCoordinate j v = ((v j).re : ℂ) := rfl
@[simp] lemma imagCoordinate_apply {n : ℕ} (j : Fin n) (v : ComplexEuclidean n) :
    imagCoordinate j v = ((v j).im : ℂ) := rfl

noncomputable def coordinatePair {n : ℕ} (j : Fin n) : Fin 2 → ComplexEuclidean n →ₗ[ℝ] ℂ :=
  ![realCoordinate j, imagCoordinate j]

/-- The actual positive coordinate volume form, ordered dx_1,dy_1,... . -/
noncomputable def interleavedVolume (n : ℕ) :
    ComplexEuclidean n [⋀^WedgePowerSlots n]→ₗ[ℝ] ℂ :=
  covectorVolume (pairedCovectors (coordinatePair (n := n)))

lemma extDeriv_normEnergy_covectors {n : ℕ} (x : ComplexEuclidean n) :
    (extDeriv (oneForm (dcLinear (normEnergy n))) x).toAlternatingMap =
      ∑ j : Fin n, covectorVolume (coordinatePair j) := by
  ext v
  have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  rw [alternatingMap_sum_apply]
  change extDeriv (oneForm (dcLinear (normEnergy n))) x v = _
  rw [hv, extDeriv_dc_normEnergy]
  simp only [covectorVolume_apply, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro coordinate hcoordinate
  simp only [Matrix.det_fin_two, Matrix.of_apply, coordinatePair,
    Matrix.cons_val_zero, Matrix.cons_val_one, realCoordinate_apply, imagCoordinate_apply,
    Complex.ofReal_sub, Complex.ofReal_mul]

/-- Full squared-norm exterior normalization, in arbitrary dimension, for the
actual exterior derivative and standard shuffle powers. -/
theorem extDeriv_normEnergy_top (n : ℕ) (x : ComplexEuclidean n) :
    wedgePower (extDeriv (oneForm (dcLinear (normEnergy n))) x).toAlternatingMap n =
      (n.factorial : ℂ) • interleavedVolume n := by
  rw [extDeriv_normEnergy_covectors, wedgePower_sum_pairs_top]
  rfl

/-- The positively ordered real coordinate basis, using the same recursive
slots as the exterior power. -/
noncomputable def interleavedBasis {n : ℕ} (s : WedgePowerSlots n) : ComplexEuclidean n :=
  EuclideanSpace.single (pairSlotEquiv n s).1 (if (pairSlotEquiv n s).2 = 0 then 1 else I)

/-- The normalization is positive on dx_1,dy_1,..., not just determined up
to an unspecified orientation sign. -/
theorem interleavedVolume_basis (n : ℕ) : interleavedVolume n interleavedBasis = 1 := by
  rw [interleavedVolume, covectorVolume_apply]
  have hm : Matrix.of (fun a b : WedgePowerSlots n =>
      pairedCovectors (coordinatePair (n := n)) b (interleavedBasis a)) =
      (1 : Matrix (WedgePowerSlots n) (WedgePowerSlots n) ℂ) := by
    ext a b
    obtain ⟨i,α,ha⟩ : ∃ i α, pairSlotEquiv n a = (i,α) := ⟨_,_,rfl⟩
    obtain ⟨j,β,hb⟩ : ∃ j β, pairSlotEquiv n b = (j,β) := ⟨_,_,rfl⟩
    have hab : a = b ↔ i = j ∧ α = β := by
      rw [← (pairSlotEquiv n).injective.eq_iff, ha, hb, Prod.mk.injEq]
    fin_cases α <;> fin_cases β <;>
      simp [pairedCovectors, interleavedBasis, ha, hb, coordinatePair,
        Matrix.of_apply, Matrix.one_apply, hab, eq_comm] <;> split_ifs <;> simp_all
  rw [hm, Matrix.det_one]

end Mahler

end OAI
