import OAI.Analysis.KadisonKastler.NormalizerLimit
import OAI.Analysis.KadisonKastler.ConjugationComparison

namespace OAI

/-! # The strong-star smoothing limit gives an exact nearby normalizer -/

namespace KadisonKastler

open Filter
open scoped Topology CStarAlgebra

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*}

local instance smoothingFactorOrder (P : VonNeumannAlgebra H) :
    PartialOrder (Algebra P) := CStarAlgebra.spectralOrder _
local instance smoothingFactorStarOrder (P : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra P) := CStarAlgebra.spectralOrderedRing _

/-- Strong convergence of the adjoints already gives weak convergence of
the conjugated operators. No norm convergence of the smoothing is used. -/
theorem operatorConjugation_weak_tendsto {l : Filter ι}
    (Q : ι → (H →L[ℂ] H)) (W : H →L[ℂ] H)
    (hstar : ∀ x, Tendsto (fun i => star (Q i) x) l (𝓝 (star W x)))
    (a : H →L[ℂ] H) (x y : H) :
    Tendsto (fun i => inner ℂ y (operatorConjugationLinear (Q i) a x)) l
      (𝓝 (inner ℂ y (operatorConjugationLinear W a x))) := by
  have ht := (hstar y).inner (𝕜 := ℂ)
    (a.continuous.continuousAt.tendsto.comp (hstar x))
  have he (v : H →L[ℂ] H) :
      inner ℂ (star v y) (a (star v x)) =
        inner ℂ y (operatorConjugationLinear v a x) := by
    simpa only [ContinuousLinearMap.star_eq_adjoint, operatorConjugationLinear_apply,
      mul_apply_eq_comp] using v.adjoint_inner_left (a (star v x)) y
  have ht' : Tendsto (fun i => inner ℂ (star (Q i) y) (a (star (Q i) x))) l
      (𝓝 (inner ℂ (star W y) (a (star W x)))) := ht
  simpa only [he] using ht'

/-- A uniformly bounded strong-star approximation to a unitary, uniformly
close to exact normalizers, yields an actual normalizer with a universal
linear displacement estimate. This is the UCP limit step in Section 7. -/
theorem exists_normalizer_of_smoothed_approximation
    (P : VonNeumannAlgebra H) (W : unitary (H →L[ℂ] H))
    (hCorrection : PublishedMultiplicationCorrection (unitaryConjugateAlgebra W P))
    (hCommutant : PublishedBlockCommutantApproximation
      (Algebra (unitaryConjugateAlgebra W P)) H)
    (ω : Ultrafilter ι) (V : ι → unitary (H →L[ℂ] H))
    (hV : ∀ i, Conjugates (V i) P P) (Q : ι → H →L[ℂ] H)
    (hstar : ∀ x, Tendsto (fun i => star (Q i) x) (ω : Filter ι)
      (𝓝 (star (W : H →L[ℂ] H) x)))
    {C d g : ℝ} (hC : 0 ≤ C) (hd : 0 ≤ d)
    (hQ : ∀ i, ‖Q i‖ ≤ C) (hVQ : ∀ i, ‖(V i : H →L[ℂ] H) - Q i‖ ≤ d)
    (hsmall : (1 + C) * d < 1 / 1000) (hge : g + (1 + C) * d < 1)
    (hgap : kkDistance (unitaryConjugateAlgebra W P) P < g) :
    ∃ n : unitary (H →L[ℂ] H), Conjugates n P P ∧
      ‖(n : H →L[ℂ] H) - (W : H →L[ℂ] H)‖ ≤ 128 * ((1 + C) * d) := by
  let R (i : ι) : Algebra P →ₗ[ℂ] (H →L[ℂ] H) :=
    (operatorConjugationLinear (Q i)).comp (algebraInclusion P).toAlgHom.toLinearMap
  apply exists_normalizer_of_weak_comparison P W hCorrection hCommutant ω V hV R
    (fun a x y => operatorConjugation_weak_tendsto Q W hstar a x y)
    (mul_nonneg (by linarith) hd) hsmall hge hgap
  intro i
  have hcoef : (‖(V i : H →L[ℂ] H)‖ + ‖Q i‖) * ‖(V i : H →L[ℂ] H) - Q i‖ ≤
      (1 + C) * d := by
    have hnormV : ‖(V i : H →L[ℂ] H)‖ ≤ 1 := by
      nontriviality (H →L[ℂ] H)
      exact (CStarRing.norm_coe_unitary (V i)).le
    apply mul_le_mul
    · exact add_le_add hnormV (hQ i)
    · exact hVQ i
    · exact norm_nonneg _
    · linarith
  have hb := completelyBoundedBy_comp_completeIsometry _
    (algebraInclusion P).toAlgHom.toLinearMap
    (complete_operatorConjugation_sub (V i : H →L[ℂ] H) (Q i))
    (injective_starAlgHom_completelyIsometric (algebraInclusion P) Subtype.val_injective)
  intro p q X
  exact (hb p q X).trans (mul_le_mul_of_nonneg_right hcoef (norm_nonneg X))

end

end KadisonKastler

end OAI
