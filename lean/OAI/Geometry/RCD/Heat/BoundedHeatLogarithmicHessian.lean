import OAI.Geometry.RCD.Heat.BoundedHeatMixedGramBounds
import OAI.Geometry.RCD.Heat.LogarithmicSquareGram
import OAI.Geometry.RCD.Sobolev.HessianVelocityPolarization

namespace OAI

/-! # Logarithmic Hessian directions of the actual positive heat factors -/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  [(hausdorff n X).Regular] [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] (hn : 2 ≤ n) (p : X)

include hn p in
theorem bounded_heat_logarithmic_hessian
    (f g h : Lp ℝ 2 (hausdorff n X)) (A B C : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A)
    (hg : ∀ᵐ x ∂hausdorff n X, |g x| ≤ B)
    (hh : ∀ᵐ x ∂hausdorff n X, |h x| ≤ C)
    {s t a : ℝ} (hs : 0 < s) (ht : 0 < t) (ha : 0 < a)
    {Ω : Set X} (hΩ : IsCompact Ω)
    (hposf : ∀ x ∈ Ω, 0 < kernelHeat (hausdorff n X) hX.quadratic
      (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) s f x)
    (hposg : ∀ x ∈ Ω, 0 < kernelHeat (hausdorff n X) hX.quadratic
      (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) t g x) :
    let m := hausdorff n X
    let Q := hX.quadratic
    let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
    let u := heatSobolev m Q s hs f
    let v := heatSobolev m Q t ht g
    let w := heatSobolev m Q a ha h
    ∃ wu wv uv U V wU wV UU VV UV : SobolevSpace m Q,
      (SobolevSpace.toLp m Q wu =ᵐ[m] localGamma m Q w u) ∧
      (SobolevSpace.toLp m Q wv =ᵐ[m] localGamma m Q w v) ∧
      (SobolevSpace.toLp m Q uv =ᵐ[m] localGamma m Q u v) ∧
      (SobolevSpace.toLp m Q U =ᵐ[m.restrict Ω] fun x => Real.log (kernelHeat m Q hk s f x)) ∧
      (SobolevSpace.toLp m Q V =ᵐ[m.restrict Ω] fun x => Real.log (kernelHeat m Q hk t g x)) ∧
      (SobolevSpace.toLp m Q wU =ᵐ[m.restrict Ω] localGamma m Q w U) ∧
      (SobolevSpace.toLp m Q wV =ᵐ[m.restrict Ω] localGamma m Q w V) ∧
      (SobolevSpace.toLp m Q UU =ᵐ[m.restrict Ω] localGamma m Q U U) ∧
      (SobolevSpace.toLp m Q VV =ᵐ[m.restrict Ω] localGamma m Q V V) ∧
      (SobolevSpace.toLp m Q UV =ᵐ[m.restrict Ω] localGamma m Q U V) ∧
      (fun x => kernelHeat m Q hk s f x*kernelHeat m Q hk t g x*
        localHessianAction m Q w U V wU wV UV x) =ᵐ[m.restrict Ω]
        localHessianAction m Q w u v wu wv uv := by
  intro m Q hk u v w
  obtain ⟨wu,M,hwu,hwuB⟩ := hX.bounded_heat_mixed_gram_bound hn p h f C A hh hf ha hs
  obtain ⟨wv,N,hwv,hwvB⟩ := hX.bounded_heat_mixed_gram_bound hn p h g C B hh hg ha ht
  obtain ⟨uv,P,huv,huvB⟩ := hX.bounded_heat_mixed_gram_bound hn p f g A B hf hg hs ht
  obtain ⟨uu,M',huu,huuB⟩ := hX.bounded_heat_mixed_gram_bound hn p f f A A hf hf hs hs
  obtain ⟨vv,N',hvv,hvvB⟩ := hX.bounded_heat_mixed_gram_bound hn p g g B B hg hg ht ht
  obtain ⟨r,R,hr,hrR,hur⟩ := hX.bounded_heat_positive_range hn p f A hf hs hΩ hposf
  obtain ⟨q,Q',hq,hqQ,hvq⟩ := hX.bounded_heat_positive_range hn p g B hg ht hΩ hposg
  obtain ⟨U,V,wU,wV,UV,hU,hV,hwU,hwV,hUV,-,-,-,hH⟩ :=
    exists_local_hessian_log_directions m Q w u v wu wv uv M N P hwuB hwvB huvB
      (ae_restrict_of_ae hwu) (ae_restrict_of_ae hwv) (ae_restrict_of_ae huv)
      hr hrR hq hqQ hur hvq
  obtain ⟨UU,hUU,-⟩ := exists_local_log_square_gram m Q u U uu M'
    (ae_restrict_of_ae huu) huuB hr hrR hur hU
  obtain ⟨VV,hVV,-⟩ := exists_local_log_square_gram m Q v V vv N'
    (ae_restrict_of_ae hvv) hvvB hq hqQ hvq hV
  have hef := kernelHeat_represents_L2 m Q hk hs f
  have heg := kernelHeat_represents_L2 m Q hk ht g
  refine ⟨wu,wv,uv,U,V,wU,wV,UU,VV,UV,hwu,hwv,huv,?_,?_,hwU,hwV,hUU,hVV,hUV,?_⟩
  · filter_upwards [hU,ae_restrict_of_ae hef] with x hx he
    exact hx.trans (congrArg Real.log he.symm)
  · filter_upwards [hV,ae_restrict_of_ae heg] with x hx he
    exact hx.trans (congrArg Real.log he.symm)
  · filter_upwards [hH,ae_restrict_of_ae hef,ae_restrict_of_ae heg,
      ae_restrict_mem hΩ.measurableSet] with x hx he₁ he₂ hmem
    rw [hx]
    change _ * (_ / (heatAt m Q s f x*heatAt m Q t g x)) = _
    rw [← he₁,← he₂]
    exact mul_div_cancel₀ _ (mul_ne_zero (hposf x hmem).ne' (hposg x hmem).ne')

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
