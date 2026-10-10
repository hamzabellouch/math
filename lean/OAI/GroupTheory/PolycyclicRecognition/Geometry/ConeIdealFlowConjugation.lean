import OAI.GroupTheory.PolycyclicRecognition.Geometry.ConeIdealFlowTiling
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConeIdealGroupConjugation
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConeProbeIntrinsicTiles

namespace OAI

/-! # The intrinsic tiling flow is ambient conjugation -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule LieAlgebra
open scoped Manifold

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ))
  {E I N A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace I] [ChartedSpace E I] [Group I]
  [LieGroup (𝓘(ℝ, E)) ⊤ I] [T2Space I] [Group N]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

variable
  (e : M.coneWordIdeal C ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) I)
  (ExpI : GroupLieAlgebra (𝓘(ℝ, E)) I → I) (hExpI : IsGroupExponential ExpI)
  (hbij : Function.Bijective ExpI)
  (chart : GroupLieAlgebra (𝓘(ℝ, E)) I ≃ₜ I) (hchart : ∀ x, chart x = ExpI x)
  (dynkin : NilpotentDynkinExpansionInput E I)
  (ι : I →* N) (ExpN : cartanRootIdeal H → N)
  (hcompat : ∀ v : M.coneWordIdeal C, ι (ExpI (e v)) = ExpN v)
  (j : cartanRootIdeal H →ₗ⁅ℝ⁆ A) (ρ : N →* Aˣ) (hρ : Function.Injective ρ)
  (hmatch : ∀ x, ρ (ExpN x) = algebraExpUnit (j x))

include hcompat hρ hmatch in
/-- The same integrated automorphism used to partition the intrinsic ideal
is conjugation by the actual ambient generator, after its inclusion in `N`. -/
theorem coneIdealLetterAutomorphism_conjugation (i : Fin M.letterCount) (t : ℝ)
    (z : I) :
    ι (M.coneIdealLetterAutomorphism C e ExpI hExpI hbij chart hchart dynkin i t z) =
      ExpN (t • M.letter i) * ι z * (ExpN (t • M.letter i))⁻¹ := by
  obtain ⟨v, rfl⟩ := (hbij.comp e.bijective).surjective z
  change ι (M.coneIdealLetterAutomorphism C e ExpI hExpI hbij chart hchart dynkin i t
    (ExpI (e v))) = ExpN (t • M.letter i) * ι (ExpI (e v)) * _
  rw [M.coneIdealLetterAutomorphism_apply_exp, hcompat, hcompat]
  exact M.coneIdealLetterFlow_exp_conjugation C ExpN j ρ hρ hmatch i t v

include hcompat hρ hmatch in
/-- The reverse-time flow in the anchor estimate is exactly the inverse of
the automorphism in the tile covering. -/
theorem coneIdealLetterAutomorphism_neg_apply (hι : Function.Injective ι)
    (i : Fin M.letterCount) (t : ℝ) (z : I) :
    M.coneIdealLetterAutomorphism C e ExpI hExpI hbij chart hchart dynkin i (-t) z =
      (M.coneIdealLetterAutomorphism C e ExpI hExpI hbij chart hchart dynkin i t).symm z := by
  have hneg : ExpN ((-t) • M.letter i) = (ExpN (t • M.letter i))⁻¹ := by
    apply hρ
    rw [map_inv, hmatch, hmatch, neg_smul, map_neg, algebraExpUnit_neg]
  apply hι
  rw [M.coneIdealLetterAutomorphism_conjugation C e ExpI hExpI hbij chart hchart
    dynkin ι ExpN hcompat j ρ hρ hmatch, hneg, inv_inv]
  exact intrinsic_probe_inverse_flow ι
    (M.coneIdealLetterAutomorphism C e ExpI hExpI hbij chart hchart dynkin i t).toMulEquiv
    (ExpN (t • M.letter i))
    (M.coneIdealLetterAutomorphism_conjugation C e ExpI hExpI hbij chart hchart
      dynkin ι ExpN hcompat j ρ hρ hmatch i t) z

end PolycyclicRecognition.CartanWordModel

end

end OAI
