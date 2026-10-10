import Mathlib
import OAI.Probability.SKValue.Equations.CoupledComparison

namespace OAI

section

open Set Filter
open scoped Topology ContDiff NNReal
namespace SKValue

lemma profile_backwardShape {M c : ℝ} (hM : 0<M) (hc : 0<c) (hcM : c≤M)
    {l : HeatProfile} (hl : l.Pairwise (fun p q ↦ p.2≤q.2))
    (hlow : ∀ p∈l,c≤(p.2:ℝ)) (hupp : ∀ p∈l,(p.2:ℝ)≤M) (t : ℝ) :
    BackwardShape c (profileValue (logCoshTerminal M) l t) := by
  induction l generalizing c t with
  | nil => exact logCoshTerminal_backwardShape hM hc hcM
  | cons p l ih =>
    obtain ⟨hp,hl⟩ := List.pairwise_cons.mp hl
    have hcp : c≤(p.2:ℝ) := hlow p (by simp)
    have hp0 : 0<(p.2:ℝ) := hc.trans_le hcp
    have hpM : (p.2:ℝ)≤M := hupp p (by simp)
    have hlo : ∀ q∈l,c≤(q.2:ℝ) := fun q hq ↦ hlow q (by simp [hq])
    have hup : ∀ q∈l,(q.2:ℝ)≤M := fun q hq ↦ hupp q (by simp [hq])
    change BackwardShape c (patchTime (p.1:ℝ) _ _ t)
    by_cases ht : t≤(p.1:ℝ)
    · rw [patchTime_left _ _ ht]
      have hs := ih hp0 hpM hl (fun q hq ↦ by exact_mod_cast hp q hq) hup 0
      have hψ := (logCoshTerminal_smoothTerminal hM).profile_evolution l
      have hsm := hψ.slices 0 ⟨le_rfl,profileTime_nonneg l⟩
      exact (hs.evolve hsm hp0 (sub_nonneg.mpr ht)).lower hp0 hc.le hcp
    · rw [patchTime_right _ _ (lt_of_not_ge ht)]
      exact ih hc hcM hl hlo hup _

end SKValue

end

section

open Set Filter
open scoped Topology
namespace SKValue
lemma moving_partial_deriv {f ft fx : ℝ → ℝ → ℝ} {p q : ℝ → ℝ} {p' q' t : ℝ}
    (hdt : ∀ᶠ z : ℝ×ℝ in 𝓝 (p t,q t), HasDerivAt (f · z.2) (ft z.1 z.2) z.1)
    (hdx : ∀ᶠ z : ℝ×ℝ in 𝓝 (p t,q t), HasDerivAt (f z.1) (fx z.1 z.2) z.2)
    (hct : ContinuousAt (fun z : ℝ×ℝ ↦ ft z.1 z.2) (p t,q t))
    (hcx : ContinuousAt (fun z : ℝ×ℝ ↦ fx z.1 z.2) (p t,q t))
    (hp : HasDerivAt p p' t) (hq : HasDerivAt q q' t) :
    HasDerivAt (fun s ↦ f (p s) (q s)) (ft (p t) (q t)*p'+fx (p t) (q t)*q') t := by
  have hd := hasStrictFDerivAt_uncurry_coprod
    (f₁ := fun a b ↦ ContinuousLinearMap.toSpanSingleton ℝ (ft a b))
    (f₂ := fun a b ↦ ContinuousLinearMap.toSpanSingleton ℝ (fx a b))
    (hdt.mono (fun z hz ↦ hz.hasFDerivAt))
    (hdx.mono (fun z hz ↦ hz.hasFDerivAt))
    (ContinuousLinearMap.toSpanSingletonCLE.continuous.continuousAt.comp hct)
    (ContinuousLinearMap.toSpanSingletonCLE.continuous.continuousAt.comp hcx)
  convert! hd.hasFDerivAt.comp_hasDerivAt t (hp.prodMk hq) using 1
  change ft (p t) (q t)*p'+fx (p t) (q t)*q'=p'*ft (p t) (q t)+q'*fx (p t) (q t)
  ring
end SKValue

end

end OAI
