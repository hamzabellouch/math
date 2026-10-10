import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.ParametricLowerSequence

namespace OAI


noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]

lemma parametric_short_gradient_tendsto {a : M} {ψ : P×Model n → ℝ}
    {p : P} {x : Model n} (L : ℝ≥0)
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).target) (hψ : ContDiffAt ℝ ∞ ψ (p,x))
    {pj : ℕ → P} {xj : ℕ → Model n} {tj : ℕ → ℝ} {f : ℕ → M → ℝ}
    (hp : Tendsto pj atTop (𝓝 p)) (hxx : Tendsto xj atTop (𝓝 x))
    (ht : Tendsto tj atTop (𝓝 0)) (htpos : ∀ᶠ i in atTop,0<tj i)
    (hlip : ∀ᶠ i in atTop,LipschitzWith L (f i))
    (hbelow : ∀ᶠ i in atTop,∀ w,ψ (pj i,w)≤f i ((extChartAt 𝓘(ℝ,Model n) a).symm w))
    (htouch : ∀ᶠ i in atTop,f i ((extChartAt 𝓘(ℝ,Model n) a).symm (xj i))=ψ (pj i,xj i))
    (hd : ∀ᶠ i in atTop,DifferentiableAt ℝ
      (fun w=>hopfLax (tj i) (f i) ((extChartAt 𝓘(ℝ,Model n) a).symm w))
        (parametricShortForward a ψ ((pj i,tj i),xj i))) :
    Tendsto (fun i=>fderiv ℝ
      (fun w=>hopfLax (tj i) (f i) ((extChartAt 𝓘(ℝ,Model n) a).symm w))
        (parametricShortForward a ψ ((pj i,tj i),xj i))) atTop
      (𝓝 (fderiv ℝ (fun w=>ψ (p,w)) x)) := by
  obtain ⟨U,hU,hD,_⟩ := exists_parametric_short_lower_sequence L hx hψ hp hxx ht htpos hlip hbelow htouch
  apply hD.congr'
  filter_upwards [hU,hd] with i hi hdi
  let z := parametricShortForward a ψ ((pj i,tj i),xj i)
  let F := fun w=>hopfLax (tj i) (f i) ((extChartAt 𝓘(ℝ,Model n) a).symm w)
  have hm : IsLocalMin (fun w=>F w-U i w) z := by
    filter_upwards [hi.2.2] with w hw
    change F z-U i z≤F w-U i w
    rw [hi.2.1]
    linarith only [hw]
  have he := hm.fderiv_eq_zero
  rw [fderiv_fun_sub hdi (hi.1.differentiableAt (by norm_num))] at he
  exact (sub_eq_zero.mp he).symm

end WeakMTWTransport

end

end OAI
