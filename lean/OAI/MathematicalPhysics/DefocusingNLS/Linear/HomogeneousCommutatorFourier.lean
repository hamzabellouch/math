import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFourierProduct
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousCommutatorSymbol

namespace OAI

/-! # The actual ordered derivative commutator in Fourier variables

The kernel contains the difference of the two ordered symbols. Its derivative
gain is therefore the proved symbol gain, rather than an assumed commutator
estimate.
-/

open MeasureTheory
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def homogeneousOrderedCommutator (N : ℕ) (j : Fin N → Fin 12)
    (V f : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  homogeneousOrderedDerivative N j (SchwartzMap.smulLeftCLM ℂ V f) -
    SchwartzMap.smulLeftCLM ℂ V (homogeneousOrderedDerivative N j f)

theorem homogeneousOrderedCommutator_fourier (N : ℕ) (j : Fin N → Fin 12)
    (V f : 𝓢(E, ℂ)) (ξ : E) :
    radianFourierKernel (homogeneousOrderedCommutator N j V f) ξ =
      (((((2 * Real.pi) ^ (12 : ℕ))⁻¹ : ℝ) : ℂ) *
        ∫ η : E, (homogeneousOrderedSymbol N j ξ - homogeneousOrderedSymbol N j (ξ - η)) *
          radianFourierKernel V η * radianFourierKernel f (ξ - η)) := by
  have hi := schwartz_mul_sub_integrable (radianFourierKernel V)
    (radianFourierKernel f) ξ
  have hd := schwartz_mul_sub_integrable (radianFourierKernel V)
    (radianFourierKernel (homogeneousOrderedDerivative N j f)) ξ
  have hd' : Integrable (fun η : E => homogeneousOrderedSymbol N j (ξ - η) *
      (radianFourierKernel V η * radianFourierKernel f (ξ - η))) := by
    convert hd using 1
    funext η
    rw [homogeneousOrderedDerivative_fourier]
    change _ = _ * (homogeneousOrderedSymbol N j (ξ - η) * _)
    ring
  have he : (fun η : E =>
      (homogeneousOrderedSymbol N j ξ - homogeneousOrderedSymbol N j (ξ - η)) *
        radianFourierKernel V η * radianFourierKernel f (ξ - η)) =
      (fun η => homogeneousOrderedSymbol N j ξ *
        (radianFourierKernel V η * radianFourierKernel f (ξ - η))) -
      (fun η => homogeneousOrderedSymbol N j (ξ - η) *
        (radianFourierKernel V η * radianFourierKernel f (ξ - η))) := by
    funext η
    simp only [Pi.sub_apply]
    ring
  rw [he]
  change _ = _ * (∫ η : E, homogeneousOrderedSymbol N j ξ *
    (radianFourierKernel V η * radianFourierKernel f (ξ - η)) -
    homogeneousOrderedSymbol N j (ξ - η) *
    (radianFourierKernel V η * radianFourierKernel f (ξ - η)))
  rw [integral_sub (hi.const_mul _) hd', integral_const_mul]
  change radianFourierCLM
    (homogeneousOrderedDerivative N j (SchwartzMap.smulLeftCLM ℂ V f) -
      SchwartzMap.smulLeftCLM ℂ V (homogeneousOrderedDerivative N j f)) ξ = _
  rw [map_sub]
  simp only [sub_apply, radianFourierCLM_apply]
  rw [homogeneousOrderedDerivative_fourier,
    radianFourierKernel_schwartzProduct_apply, radianFourierKernel_schwartzProduct_apply]
  have hdint : (∫ η : E, radianFourierKernel V η *
      radianFourierKernel (homogeneousOrderedDerivative N j f) (ξ - η)) =
      ∫ η : E, homogeneousOrderedSymbol N j (ξ - η) *
        (radianFourierKernel V η * radianFourierKernel f (ξ - η)) := by
    apply integral_congr_ae
    filter_upwards [] with η
    rw [homogeneousOrderedDerivative_fourier]
    change _ * (homogeneousOrderedSymbol N j (ξ - η) * _) = _
    ring
  rw [hdint]
  change homogeneousOrderedSymbol N j ξ * (_ * _) - _ * _ = _
  ring

end DefocusingNLS

end OAI
