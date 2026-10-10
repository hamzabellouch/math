import Mathlib
import OAI.Geometry.WeakMTW.Variations.ActionBranch
import OAI.Geometry.WeakMTW.Support.ActiveSupports
import OAI.Geometry.WeakMTW.Coordinates.TangentScaling

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]
  {ι : Type*} [Fintype ι] [Nonempty ι]

 def scaledPoleValue (y : ι → M) (h : ι → ℝ) (s : ℝ) (p : TangentBundle (model n) M) : ℝ :=
  ‖s•p.2‖^2/2+s*finitePotential y h p.1

 theorem ActionBranch.eventually_source {x z : M} (B : ActionBranch (n := n) x z)
    {L : Filter ℕ} {p : ℕ → TangentBundle (model n) M} {p₀ : TangentBundle (model n) M}
    (hp : Tendsto p L (𝓝 p₀)) (hpS : p₀ ∈ (stateChart x).source)
    (hpB : stateChart x p₀ ∈ B.coord.source) :
    ∀ᶠ j in L, p j ∈ (stateChart x).source ∧ stateChart x (p j) ∈ B.coord.source := by
  have h₁ : ∀ᶠ j in L, p j ∈ (stateChart x).source := hp ((stateChart x).open_source.mem_nhds hpS)
  have h₂ : ∀ᶠ j in L, stateChart x (p j) ∈ B.coord.source :=
    (((stateChart x).continuousAt hpS).tendsto.comp hp) (B.coord.open_source.mem_nhds hpB)
  exact h₁.and h₂

omit [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M] in
 theorem base_chart_limit {p : ℕ → TangentBundle (model n) M} {p₀ : TangentBundle (model n) M}
    (hp : Tendsto p atTop (𝓝 p₀)) :
    Tendsto (fun j => chartAt (Model n) p₀.1 (p j).1) atTop (𝓝 (chartAt (Model n) p₀.1 p₀.1)) := by
  have hproj : Continuous (fun q : TangentBundle (model n) M => q.1) :=
    (contMDiff_proj (TangentSpace (model n)) (IB := model n) (n := ∞)).continuous
  exact ((chartAt (Model n) p₀.1).continuousAt (mem_chart_source (Model n) p₀.1)).tendsto.comp
    (hproj.continuousAt.tendsto.comp hp)

 theorem scaled_endpoint_chart_limit {p : ℕ → TangentBundle (model n) M} {p₀ : TangentBundle (model n) M}
    (hp : Tendsto p atTop (𝓝 p₀)) {sⱼ : ℕ → ℝ} {s : ℝ} (hs : Tendsto sⱼ atTop (𝓝 s)) :
    Tendsto (fun j => chartAt (Model n) (exp p₀.1 (s•p₀.2)) (exp (p j).1 (sⱼ j•(p j).2)))
      atTop (𝓝 (chartAt (Model n) (exp p₀.1 (s•p₀.2)) (exp p₀.1 (s•p₀.2)))) := by
  exact ((chartAt (Model n) (exp p₀.1 (s•p₀.2))).continuousAt (mem_chart_source (Model n) _)).tendsto.comp
    (scaledExp_continuous.continuousAt.tendsto.comp (hs.prodMk_nhds hp))

 theorem branch_support_inequality (y : ι → M) (h : ι → ℝ)
    {x z w : M} {p q : TangentBundle (model n) M} {s ℓ : ℝ}
    (hs : 0 ≤ s) (hℓ : 0 < ℓ) (hℓ₁ : ℓ < 1)
    {a : TangentSpace (model n) p.1} (ha : a ∈ activeVelocities y h p.1)
    (B : ActionBranch (n := n) x z) (C : ActionBranch (n := n) x w)
    (hpS : (mulState s p) ∈ (stateChart x).source)
    (hqS : (mulState s q) ∈ (stateChart x).source)
    (hpB : stateChart x (mulState s p) ∈ B.coord.source)
    (hqB : stateChart x (mulState s q) ∈ B.coord.source)
    (hcollision : exp p.1 (s•p.2) = exp q.1 (s•q.2))
    (hvalue : scaledPoleValue y h s q ≤ scaledPoleValue y h s p)
    (hCp : C.value (chartAt (Model n) x p.1,chartAt (Model n) w (exp p.1 (ℓ•a))) =
      cost p.1 (exp p.1 (ℓ•a)))
    (hCq : C.value (chartAt (Model n) x q.1,chartAt (Model n) w (exp p.1 (ℓ•a))) =
      cost q.1 (exp p.1 (ℓ•a))) :
    B.value (chartAt (Model n) x q.1,chartAt (Model n) z (exp p.1 (s•p.2))) -
      B.value (chartAt (Model n) x p.1,chartAt (Model n) z (exp p.1 (s•p.2))) -
      (s/ℓ)*(C.value (chartAt (Model n) x q.1,chartAt (Model n) w (exp p.1 (ℓ•a))) -
        C.value (chartAt (Model n) x p.1,chartAt (Model n) w (exp p.1 (ℓ•a)))) ≤ 0 := by
  have hpV := B.value_state (mulState s p) hpS hpB
  have hqV := B.value_state (mulState s q) hqS hqB
  change B.value (chartAt (Model n) x p.1,chartAt (Model n) z (exp p.1 (s•p.2))) = ‖s•p.2‖^2/2 at hpV
  change B.value (chartAt (Model n) x q.1,chartAt (Model n) z (exp q.1 (s•q.2))) = ‖s•q.2‖^2/2 at hqV
  rw [← hcollision] at hqV
  rw [hpV,hqV,hCp,hCq]
  have hsup := mul_le_mul_of_nonneg_left (activeSupport_le y h p.1 ha hℓ hℓ₁ q.1) hs
  unfold activeSupport at hsup
  unfold scaledPoleValue at hvalue
  have halg : (s/ℓ)*(cost q.1 (exp p.1 (ℓ•a))-cost p.1 (exp p.1 (ℓ•a))) =
      -(s*((cost p.1 (exp p.1 (ℓ•a))-cost q.1 (exp p.1 (ℓ•a)))/ℓ)) := by ring
  rw [halg]
  nlinarith

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
