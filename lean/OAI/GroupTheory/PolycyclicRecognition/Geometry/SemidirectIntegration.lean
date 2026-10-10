import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentSemidirectGroup
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialProduct

namespace OAI

/-! # Integrating a codimension-one semidirect product

An equivariant homomorphism on the ideal and the complementary exponential
curve give the required homomorphism, with its actual manifold derivative.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]
  (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G]
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
  (k : L →* G) (u : GroupLieAlgebra (𝓘(ℝ, E)) G)
  (hact : ∀ t x, k (nilpotentDerivationFlow D hD t x) =
    Exp (t • u) * k x * (Exp (t • u))⁻¹)

def derivationSemidirectHom :
    letI := derivationSemidirectGroup D hD
    letI : MulOneClass (L × ℝ) := (derivationSemidirectGroup D hD).toMulOneClass
    letI : One (L × ℝ) := (derivationSemidirectGroup D hD).toOne
    (L × ℝ) →* G := by
  letI := derivationSemidirectGroup D hD
  letI : MulOneClass (L × ℝ) := (derivationSemidirectGroup D hD).toMulOneClass
  letI : Mul (L × ℝ) := (derivationSemidirectGroup D hD).toMul
  letI : One (L × ℝ) := (derivationSemidirectGroup D hD).toOne
  refine { toFun := fun p => k p.1 * Exp (p.2 • u), map_one' := ?_, map_mul' := ?_ }
  · change k ((derivationSemidirectGroup D hD).one).1 *
      Exp (((derivationSemidirectGroup D hD).one).2 • u) = 1
    rw [derivationSemidirect_one]
    simp only [zero_smul, hExp.map_zero, mul_one]
    rw [← P.one_eq_zero, map_one]
  · intro x y
    change k ((derivationSemidirectGroup D hD).mul x y).1 *
      Exp (((derivationSemidirectGroup D hD).mul x y).2 • u) = _
    rw [derivationSemidirect_mul, map_mul, hact, hExp.map_add_smul]
    group

omit [LieGroup (𝓘(ℝ, E)) ⊤ G] in
@[simp] theorem derivationSemidirectHom_apply (p : L × ℝ) :
    derivationSemidirectHom D hD Exp hExp k u hact p = k p.1 * Exp (p.2 • u) := rfl

theorem contMDiff_derivationSemidirectHom
    (hk : ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, E)) ∞ k) :
    ContMDiff (𝓘(ℝ, L × ℝ)) (𝓘(ℝ, E)) ∞
      (derivationSemidirectHom D hD Exp hExp k u hact) :=
  (hk.comp contDiff_fst.contMDiff).mul
    ((hExp.contMDiff_curve u).comp contDiff_snd.contMDiff)

theorem hasMFDerivAt_derivationSemidirectHom
    (j : L →L[ℝ] E)
    (hk : HasMFDerivAt (𝓘(ℝ, L)) (𝓘(ℝ, E)) k (1 : L) j) :
    let d : (L × ℝ) →L[ℝ] E := j.comp (ContinuousLinearMap.fst ℝ L ℝ) +
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (M₂ := E) (u : E)).comp
        (ContinuousLinearMap.snd ℝ L ℝ)
    HasMFDerivAt (𝓘(ℝ, L × ℝ)) (𝓘(ℝ, E))
      (derivationSemidirectHom D hD Exp hExp k u hact) (0 : L × ℝ) d := by
  have hk0 : HasMFDerivAt (𝓘(ℝ, L)) (𝓘(ℝ, E)) k (0 : L) j := by
    rw [← P.one_eq_zero]
    exact hk
  exact HasMFDerivAt.mul_at_one
    (hk0.comp (f := fun p : L × ℝ => p.1) (0 : L × ℝ)
      (ContinuousLinearMap.fst ℝ L ℝ).hasFDerivAt.hasMFDerivAt)
    ((hExp.hasMFDerivAt_zero u).comp (f := fun p : L × ℝ => p.2) (0 : L × ℝ)
      (ContinuousLinearMap.snd ℝ L ℝ).hasFDerivAt.hasMFDerivAt)
    (by change k 0 = 1; rw [← P.one_eq_zero, map_one])
    (by change Exp (0 • u) = 1; rw [zero_smul, hExp.map_zero])

end PolycyclicRecognition

end

end OAI
