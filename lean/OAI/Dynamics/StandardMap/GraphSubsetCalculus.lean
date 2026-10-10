import OAI.Dynamics.StandardMap.GraphDistortion

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy

lemma hasFDerivWithinAt_of_regular_level {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (F : E × ℝ → ℝ) (b : E → ℝ) (s : Set E) (x : E)
    (A : E →L[ℝ] ℝ) (t : ℝ)
    (hD : HasStrictFDerivAt F
      (A.comp (ContinuousLinearMap.fst ℝ E ℝ)+t • ContinuousLinearMap.snd ℝ E ℝ) (x,b x))
    (ht : t ≠ 0) (hb : ContinuousWithinAt b s x)
    (hlevel : ∀ᶠ y in 𝓝[s] x, F (y,b y)=F (x,b x)) :
    HasFDerivWithinAt b ((-t⁻¹) • A) s x := by
  let L : (E × ℝ) →L[ℝ] ℝ :=
    A.comp (ContinuousLinearMap.fst ℝ E ℝ)+t • ContinuousLinearMap.snd ℝ E ℝ
  have hInv : (L.comp (ContinuousLinearMap.inr ℝ E ℝ)).IsInvertible := by
    apply ContinuousLinearMap.IsInvertible.of_inverse (g := t⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    · apply ContinuousLinearMap.ext; intro z; simp [L,ht]
    · apply ContinuousLinearMap.ext; intro z; simp [L,ht]
  let ψ := hD.implicitFunctionOfProdDomain hInv
  have he : ∀ᶠ y in 𝓝[s] x, ψ y=b y := by
    have hpair : Tendsto (fun y => (y,b y)) (𝓝[s] x) (𝓝 (x,b x)) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id |>.prodMk_nhds hb
    filter_upwards [hpair.eventually (hD.eventually_apply_eq_iff_implicitFunctionOfProdDomain hInv),hlevel] with y hy hy'
    exact hy.mp hy'
  have he0 : ψ x=b x := ((hD.eventually_apply_eq_iff_implicitFunctionOfProdDomain hInv).self_of_nhds).mp rfl
  have hd := (hD.hasStrictFDerivAt_implicitFunctionOfProdDomain hInv).hasFDerivAt.hasFDerivWithinAt (s := s)
  have heq : -(L.comp (ContinuousLinearMap.inr ℝ E ℝ)).inverse.comp
      (L.comp (ContinuousLinearMap.inl ℝ E ℝ)) = (-t⁻¹) • A := by
    apply ContinuousLinearMap.ext
    intro z
    have hh : (L.comp (ContinuousLinearMap.inr ℝ E ℝ)).inverse
        ((L.comp (ContinuousLinearMap.inl ℝ E ℝ)) z)=t⁻¹*A z := by
      apply hInv.inverse_apply_eq.mpr
      simp [L,ht]
    change -((L.comp (ContinuousLinearMap.inr ℝ E ℝ)).inverse
      ((L.comp (ContinuousLinearMap.inl ℝ E ℝ)) z))=(-t⁻¹)*A z
    rw [hh,neg_mul]
  change HasFDerivWithinAt ψ _ s x at hd
  rw [heq] at hd
  exact hd.congr_of_eventuallyEq (EventuallyEq.symm he) he0.symm
end StandardMapEntropy

end OAI
