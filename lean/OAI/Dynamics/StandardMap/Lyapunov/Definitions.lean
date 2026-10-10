import OAI.Dynamics.StandardMap.EntropyEndpoint

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

noncomputable def tangentCoordinates : ℂ →L[ℝ] ℂ :=
  { toLinearMap :=
      { toFun := fun z => ⟨z.re, z.re-z.im⟩
        map_add' := by intro z w; apply Complex.ext <;> simp; ring
        map_smul' := by intro t z; apply Complex.ext <;> simp; ring }
    cont := Complex.equivRealProdCLM.symm.continuous.comp
      (Complex.continuous_re.prodMk (Complex.continuous_re.sub Complex.continuous_im)) }

local instance realTangentCompTriple :
    RingHomCompTriple (RingHom.id ℝ) (RingHom.id ℝ) (RingHom.id ℝ) := inferInstance

noncomputable def standardDerivative (k : ℝ) (z : Torus) : ℂ →L[ℝ] ℂ :=
  tangentCoordinates.comp ((transferStep (torusPotential k z.1)).comp tangentCoordinates)

noncomputable def standardDerivativeProduct (k : ℝ) (z : Torus) (n : ℕ) : ℂ →L[ℝ] ℂ :=
  Nat.rec (ContinuousLinearMap.id ℝ ℂ)
    (fun i A => (standardDerivative k ((standardMap k)^[i] z)).comp A) n

lemma standardDerivativeProduct_zero (k : ℝ) (z : Torus) :
    standardDerivativeProduct k z 0 = ContinuousLinearMap.id ℝ ℂ := rfl

lemma standardDerivativeProduct_succ (k : ℝ) (z : Torus) (n : ℕ) :
    standardDerivativeProduct k z (n + 1) =
      (standardDerivative k ((standardMap k)^[n] z)).comp
        (standardDerivativeProduct k z n) := rfl

noncomputable def standardInverseDerivative (k : ℝ) (z : Torus) : ℂ →L[ℝ] ℂ :=
  tangentCoordinates.comp
    ((transferStepInv (torusPotential k (inverseMap k z).1)).comp tangentCoordinates)

noncomputable def complexProjection (z : ℂ) : Torus := ((z.re : Circle), (z.im : Circle))
noncomputable def standardLift (k : ℝ) (z : ℂ) : ℂ :=
  ⟨z.re+z.im+k*Real.sin (2*Real.pi*z.re), z.im+k*Real.sin (2*Real.pi*z.re)⟩
noncomputable def standardInverseLift (k : ℝ) (z : ℂ) : ℂ :=
  ⟨z.re-z.im, z.im-k*Real.sin (2*Real.pi*(z.re-z.im))⟩

def VectorGrowth (k : ℝ) (z : Torus) (v : ℂ) (l : ℝ) : Prop :=
  v ≠ 0 ∧ Tendsto (fun n : ℕ => Real.log ‖standardDerivativeProduct k z n v‖ / (n : ℝ))
    atTop (𝓝 l)

def LyapunovSpectrumAt (k : ℝ) (z : Torus) (l : ℝ) : Prop :=
  0 ≤ l ∧ ((l = 0 ∧ ∀ v : ℂ, v ≠ 0 → VectorGrowth k z v 0) ∨
    (0 < l ∧ ∃ s : ℂ, s ≠ 0 ∧ ∀ v : ℂ, v ≠ 0 →
      VectorGrowth k z v (if wedge s v = 0 then -l else l)))

end StandardMapEntropy
end
end

end OAI
