import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialExteriorDeterminant

namespace OAI

/-! # Exterior powers of a free polynomial orbit -/

noncomputable section
namespace PolycyclicRecognition
open scoped Polynomial
variable {K M : Type} [Field K] [AddCommGroup M] [Module K M]

def polynomialOrbitMap (T : Module.End K M) (v : M) : K[X] →ₗ[K] M where
  toFun p := Polynomial.aeval T p v
  map_add' p q := by simp only [map_add, LinearMap.add_apply]
  map_smul' c p := by simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply]

theorem polynomialOrbitMap_mul (T : Module.End K M) (v : M) (p q : K[X]) :
    polynomialOrbitMap T v (p * q) = Polynomial.aeval T p (polynomialOrbitMap T v q) := by
  change Polynomial.aeval T (p * q) v = _
  rw [map_mul]
  rfl

theorem polynomialOrbitMap_shift (T : Module.End K M) (v : M) (c : K) :
    (polynomialOrbitMap T v).comp (LinearMap.mulLeft K (Polynomial.X - Polynomial.C c)) =
      (T - c • LinearMap.id).comp (polynomialOrbitMap T v) := by
  apply LinearMap.ext
  intro p
  change polynomialOrbitMap T v ((Polynomial.X - Polynomial.C c) * p) = _
  rw [polynomialOrbitMap_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
  rfl

theorem polynomialOrbitMap_injective (T : Module.End K M) (v : M)
    (h : LinearIndependent K (fun i : ℕ => (T ^ i) v)) :
    Function.Injective (polynomialOrbitMap T v) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro p hp
  change Polynomial.aeval T p v = 0 at hp
  rw [Polynomial.aeval_endomorphism] at hp
  have hz := (linearIndependent_iff'.mp h) p.support (fun i => p.coeff i) hp
  apply Polynomial.ext
  intro i
  by_cases hi : i ∈ p.support
  · exact hz i hi
  · exact Polynomial.notMem_support_iff.mp hi

theorem polynomialOrbitExterior_shift (T : Module.End K M) (v : M) (n : ℕ) (c : K) :
    (exteriorPower.map n (polynomialOrbitMap T v)).comp
        (exteriorPower.map n (LinearMap.mulLeft K (Polynomial.X - Polynomial.C c))) =
      (exteriorPower.map n (T - c • LinearMap.id)).comp
        (exteriorPower.map n (polynomialOrbitMap T v)) := by
  rw [← exteriorPower.map_comp, polynomialOrbitMap_shift, exteriorPower.map_comp]

theorem polynomialOrbitExterior_injective (T : Module.End K M) (v : M) (n : ℕ)
    (h : LinearIndependent K (fun i : ℕ => (T ^ i) v)) :
    Function.Injective (exteriorPower.map n (polynomialOrbitMap T v)) :=
  exteriorPower.map_injective_field (n := n) (polynomialOrbitMap_injective T v h)

end PolycyclicRecognition

end

end OAI
