import OAI.GroupTheory.PolycyclicRecognition.Lattices.NilshadowRealAction
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorSystemPullback
import OAI.GroupTheory.PolycyclicRecognition.Geometry.InvariantGraphLieModel

namespace OAI

/-! # Embedding the finite-power extension in the real invariant graph -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff

def scaleRealHeight (n : ℕ) (a : ℝ) : AbelianRealSpace n →* Multiplicative (Fin n → ℝ) where
  toFun x := Multiplicative.ofAdd (a • x)
  map_one' := by
    apply Multiplicative.ext
    exact smul_zero a
  map_mul' x y := by
    apply Multiplicative.ext
    exact smul_add a x y

namespace IntegralNilshadowData
variable {L G : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [Group G] {n : ℕ}
  {E : GroupExtension L G (IntegralLatticeGroup n)} (D : IntegralNilshadowData E)

def inverseScaledHeight (m : ℕ) : D.completion.carrier →* Multiplicative (Fin n → ℝ) :=
  (scaleRealHeight n (-((m : ℝ)⁻¹))).comp D.height

theorem inverseScaledHeight_smooth (m : ℕ) :
    ContDiff ℝ ⊤ (fun x => (D.inverseScaledHeight m x).toAdd) := by
  have h : ContDiff ℝ ⊤ (fun x => -((m : ℝ)⁻¹) • D.heightLinear x) :=
    ((-((m : ℝ)⁻¹)) • D.heightLinear).toContinuousLinearMap.contDiff
  have hf : (fun x => (D.inverseScaledHeight m x).toAdd) =
      (fun x => -((m : ℝ)⁻¹) • D.heightLinear x) := by
    funext x
    exact congrArg (fun y => -((m : ℝ)⁻¹) • y) (D.heightLinear_apply x).symm
  rw [hf]
  exact h

def factorEmbedding : FactorExtension D.system →*
    (D.completion.carrier ⋊[D.completedAction] IntegralLatticeGroup n) :=
  D.completionSemidirectMap.comp
    (factorTwistGraph D.system D.removed D.commutes D.fixes)

def realPowerEmbedding (m : ℕ)
    (φ : Multiplicative (Fin n → ℝ) →* MulAut D.completion.carrier)
    (he : ∀ z x, D.completedAction (latticePowerHom n m z) x = φ (integerVectorHom n z) x) :
    FactorExtension (D.system.pullback (latticePowerHom n m)) →*
      (D.completion.carrier ⋊[φ] Multiplicative (Fin n → ℝ)) where
  toFun a := ⟨D.completion.embed ⟨a.left, latticePowerHom n m a.right⟩, integerVectorHom n a.right⟩
  map_one' := by
    apply SemidirectProduct.ext
    · change D.completion.embed (1 : FactorExtension D.twistedSystem) = 1
      exact map_one _
    · exact map_one _
  map_mul' a b := by
    apply SemidirectProduct.ext
    · have h := congrArg (fun x => x.left)
        ((D.factorEmbedding.comp (factorPullbackMap D.system (latticePowerHom n m))).map_mul a b)
      change D.completion.embed
          ⟨(a * b).left, latticePowerHom n m (a * b).right⟩ =
        D.completion.embed ⟨a.left, latticePowerHom n m a.right⟩ *
          D.completedAction (latticePowerHom n m a.right)
            (D.completion.embed ⟨b.left, latticePowerHom n m b.right⟩) at h
      rw [he] at h
      exact h
    · exact map_mul (integerVectorHom n) _ _

theorem realPowerEmbedding_injective (m : ℕ)
    (φ : Multiplicative (Fin n → ℝ) →* MulAut D.completion.carrier)
    (he : ∀ z x, D.completedAction (latticePowerHom n m z) x = φ (integerVectorHom n z) x) :
    Function.Injective (D.realPowerEmbedding m φ he) := by
  intro a b h
  apply FactorExtension.ext
  · have hx := D.completion.injective (congrArg (fun x => x.left) h)
    exact congrArg (fun z : FactorExtension D.twistedSystem => z.left) hx
  · exact integerVectorHom_injective n (congrArg (fun x => x.right) h)

theorem realPowerEmbedding_mem_graph {m : ℕ} (hm : 0 < m)
    (φ : Multiplicative (Fin n → ℝ) →* MulAut D.completion.carrier)
    (he : ∀ z x, D.completedAction (latticePowerHom n m z) x = φ (integerVectorHom n z) x)
    (hinv : ∀ v x, D.height (φ v x) = D.height x)
    (a : FactorExtension (D.system.pullback (latticePowerHom n m))) :
    D.realPowerEmbedding m φ he a ∈ rotationalTwist φ (D.inverseScaledHeight m)
      (fun v x => congrArg (scaleRealHeight n (-((m : ℝ)⁻¹))) (hinv v x)) := by
  change integerVectorHom n a.right =
    (D.inverseScaledHeight m (D.completion.embed ⟨a.left, latticePowerHom n m a.right⟩))⁻¹
  apply Multiplicative.ext
  change integerVectorMap n a.right.toAdd =
    -(-((m : ℝ)⁻¹) • D.height (D.completion.embed ⟨a.left, latticePowerHom n m a.right⟩))
  rw [D.height_embed]
  change integerVectorMap n a.right.toAdd =
    -(-((m : ℝ)⁻¹) • integralRealHeight (a.right ^ m))
  rw [map_pow]
  change integerVectorMap n a.right.toAdd =
    -(-((m : ℝ)⁻¹) • (m • integerVectorMap n a.right.toAdd))
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  simp [hm']

def powerGraphEmbedding {m : ℕ} (hm : 0 < m)
    (φ : Multiplicative (Fin n → ℝ) →* MulAut D.completion.carrier)
    (he : ∀ z x, D.completedAction (latticePowerHom n m z) x = φ (integerVectorHom n z) x)
    (hinv : ∀ v x, D.height (φ v x) = D.height x) :
    FactorExtension (D.system.pullback (latticePowerHom n m)) →*
      rotationalTwist φ (D.inverseScaledHeight m)
        (fun v x => congrArg (scaleRealHeight n (-((m : ℝ)⁻¹))) (hinv v x)) :=
  (D.realPowerEmbedding m φ he).codRestrict _ (D.realPowerEmbedding_mem_graph hm φ he hinv)

end IntegralNilshadowData
end PolycyclicRecognition

end

end OAI
