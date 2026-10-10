import Mathlib
import OAI.Analysis.WeakInfiniteness.CuntzComparison
import OAI.Analysis.WeakInfiniteness.RectangularPolar
import OAI.Analysis.WeakInfiniteness.SpectralCut

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped Topology CStarAlgebra

local instance matrixRealModuleCut {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {n : Type*} [Fintype n] :
    Module ℝ (CStarMatrix n n A) := Module.complexToReal _

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {m n : Type*} [Fintype m] [Fintype n]

omit [Fintype n] in
lemma rectangular_sqrt_initial (h : CStarMatrix m m A) (V : CStarMatrix m n A)
    (hh : 0 ≤ h) :
    (CFC.sqrt h*V).conjTranspose*(CFC.sqrt h*V) = V.conjTranspose*h*V := by
  rw [rectangular_star_mul, ← CStarMatrix.star_eq_conjTranspose,
    (CFC.sqrt_nonneg h).star_eq]
  calc
    (V.conjTranspose*CFC.sqrt h)*(CFC.sqrt h*V) =
        V.conjTranspose*(CFC.sqrt h*CFC.sqrt h)*V := by
      simp only [rectangular_mul_assoc]
    _ = V.conjTranspose*h*V := by rw [CFC.sqrt_mul_sqrt_self h hh]

lemma rectangular_sandwich_nonneg (h : CStarMatrix m m A) (V : CStarMatrix m n A)
    (hh : 0 ≤ h) : 0 ≤ V.conjTranspose*h*V := by
  rw [← rectangular_sqrt_initial h V hh]
  exact rectangular_initial_nonneg _

lemma CuntzSubequiv.exact_spectralRamp {x : CStarMatrix n n A}
    {h : CStarMatrix m m A} (hx : 0 ≤ x) (hh : 0 ≤ h) (hxh : CuntzSubequiv x h)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ R : CStarMatrix m n A,
      R.conjTranspose*R = cfcₙ (spectralRamp δ) x ∧
      R*R.conjTranspose ∈ hereditarySubalgebra h hh.isSelfAdjoint ∧ ‖R‖ ≤ 1 := by
  let θ := δ/2
  have hθ : 0 < θ := by dsimp only [θ]; positivity
  obtain ⟨V, hV⟩ := hxh (θ/2) (by positivity)
  let y := V.conjTranspose*h*V
  let z := cfcₙ (spectralRamp θ) x
  have hz : 0 ≤ z := cfcₙ_nonneg (fun s _ => spectralRamp_nonneg θ s)
  have hd : 0 ≤ cfcₙ (spectralRamp δ) x := cfcₙ_nonneg (fun s _ => spectralRamp_nonneg δ s)
  have hzero : ∀ s, s ≤ 2*θ → spectralRamp δ s = 0 := by
    intro s hs
    apply spectralRamp_eq_zero hδ
    dsimp only [θ] at hs
    linarith
  have hdom : cfcₙ (spectralRamp δ) x ≤ (2*1/θ) • (z*y*z) :=
    spectralRamp_domination x y hx (rectangular_sandwich_nonneg h V hh) hθ zero_le_one hV.le
      (spectralRamp δ) (continuous_spectralRamp δ) (spectralRamp_eq_zero hδ hδ.le)
      hzero (spectralRamp_le_one δ)
  have he : (CFC.sqrt h*(V*z)).conjTranspose*(CFC.sqrt h*(V*z)) = z*y*z := by
    rw [← rectangular_mul_assoc (CFC.sqrt h) V z, rectangular_initial_mul,
      rectangular_sqrt_initial h V hh, hz.star_eq]
  obtain ⟨R, hR, hRher⟩ := rectangular_exact_initial_hereditary h (V*z)
    (cfcₙ (spectralRamp δ) x) hh hd (show 0 ≤ 2*1/θ by positivity) (by rwa [he])
  refine ⟨R, hR, hRher, ?_⟩
  have hn : ‖cfcₙ (spectralRamp δ) x‖ ≤ 1 := by
    apply norm_cfcₙ_le
    intro s _
    rw [Real.norm_eq_abs, abs_of_nonneg (spectralRamp_nonneg δ s)]
    exact spectralRamp_le_one δ s
  rw [← hR, rectangular_norm_initial] at hn
  nlinarith [norm_nonneg R]

end

end WeakPureInfiniteness
end

end OAI
