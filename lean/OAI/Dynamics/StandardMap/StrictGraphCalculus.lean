import OAI.Dynamics.StandardMap.CompactRelabeling

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy

lemma hasStrictDerivAt_of_regular_level (F : ℝ × ℝ → ℝ) (b : ℝ → ℝ) (x s t : ℝ)
    (hD : HasStrictFDerivAt F
      (s • ContinuousLinearMap.fst ℝ ℝ ℝ+t • ContinuousLinearMap.snd ℝ ℝ ℝ) (x,b x))
    (ht : t ≠ 0) (hb : ContinuousAt b x)
    (hlevel : ∀ᶠ y in 𝓝 x, F (y,b y)=F (x,b x)) :
    HasStrictDerivAt b (-s/t) x := by
  let L : (ℝ × ℝ) →L[ℝ] ℝ := s • ContinuousLinearMap.fst ℝ ℝ ℝ+t • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hInv : (L.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)).IsInvertible := by
    apply ContinuousLinearMap.IsInvertible.of_inverse (g := t⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    · apply ContinuousLinearMap.ext; intro z; simp [L,ht]
    · apply ContinuousLinearMap.ext; intro z; simp [L,ht]
  let ψ := hD.implicitFunctionOfProdDomain hInv
  have he : ∀ᶠ y in 𝓝 x, ψ y=b y := by
    have hpair : Tendsto (fun y => (y,b y)) (𝓝 x) (𝓝 (x,b x)) :=
      tendsto_id.prodMk_nhds hb
    filter_upwards [hpair.eventually (hD.eventually_apply_eq_iff_implicitFunctionOfProdDomain hInv),hlevel] with y hy hy'
    exact hy.mp hy'
  have hd := (hD.hasStrictFDerivAt_implicitFunctionOfProdDomain hInv).hasStrictDerivAt
  have heq : (-(L.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)).inverse.comp
      (L.comp (ContinuousLinearMap.inl ℝ ℝ ℝ))) 1 = -s/t := by
    have hh : (L.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)).inverse
        ((L.comp (ContinuousLinearMap.inl ℝ ℝ ℝ)) 1)=s/t := by
      apply hInv.inverse_apply_eq.mpr
      simp only [L,ContinuousLinearMap.comp_apply,add_apply,smul_apply]
      change s*1+t*0=s*0+t*(s/t)
      field_simp
      ring
    change -(L.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)).inverse
      ((L.comp (ContinuousLinearMap.inl ℝ ℝ ℝ)) 1) = -s/t
    rw [hh,neg_div]
  change HasStrictDerivAt ψ _ x at hd
  rw [heq] at hd
  exact hd.congr_of_eventuallyEq he
end StandardMapEntropy

end OAI
