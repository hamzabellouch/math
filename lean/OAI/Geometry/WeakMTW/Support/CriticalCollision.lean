import Mathlib
import OAI.Geometry.WeakMTW.Support.BranchCollisionLimits
import OAI.Geometry.WeakMTW.Support.CollisionStrictGap

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

 theorem critical_collision_sequence_false (y : ι → M) (h : ι → ℝ)
    (hMTW : HasWeakMTW (n := n) (M := M))
    {p q : ℕ → TangentBundle (model n) M} {p₀ : TangentBundle (model n) M}
    (hp : Tendsto p atTop (𝓝 p₀)) (hq : Tendsto (fun j => (q j).1) atTop (𝓝 p₀.1))
    {sⱼ : ℕ → ℝ} {s : ℝ} (hs : Tendsto sⱼ atTop (𝓝 s))
    (hqp : Tendsto (fun j => mulState (sⱼ j) (q j)) atTop (𝓝 (mulState s p₀)))
    (hpos : ∀ᶠ j in atTop, 0 < sⱼ j) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hg : ∀ j, p j ∈ activeHullGraph y h)
    (hne : ∀ᶠ j in atTop, p j ≠ q j)
    (hcollision : ∀ᶠ j in atTop, exp (p j).1 (sⱼ j•(p j).2) = exp (q j).1 (sⱼ j•(q j).2))
    (hvalue : ∀ᶠ j in atTop, scaledPoleValue y h (sⱼ j) (q j) ≤ scaledPoleValue y h (sⱼ j) (p j))
    (hbelow : ∀ r, 0 ≤ r → r < s → ∀ a ∈ activeHull (n := n) y h p₀.1, r•a ∈ injectivityDomain p₀.1)
    (hn : Nonconjugate p₀.1 (s•p₀.2)) : False := by
  classical
  let ℓ := (s+1)/2
  have hsℓ : s < ℓ := by dsimp [ℓ]; linarith
  have hℓ : 0 < ℓ := lt_of_le_of_lt hs0 hsℓ
  have hℓ₁ : ℓ < 1 := by dsimp [ℓ]; linarith
  obtain ⟨B,hB⟩ := ActionBranch.exists_of_nonconjugate hn
  have hpS : mulState s p₀ ∈ (stateChart p₀.1).source :=
    (stateChart_source p₀.1 _).mpr (mem_chart_source (Model n) p₀.1)
  have hpp := tangentScale_continuous.continuousAt.tendsto.comp (hs.prodMk_nhds hp)
  have hBp := B.eventually_source hpp hpS hB
  have hBq := B.eventually_source hqp hpS hB
  have hbasene : ∀ᶠ j in atTop,
      chartAt (Model n) p₀.1 (q j).1 ≠ chartAt (Model n) p₀.1 (p j).1 := by
    filter_upwards [hBp,hBq,hpos,hcollision,hne] with j hjp hjq hjs hjc hjn
    have hnb := branch_collision_base_ne B hjs.ne' hjp.1 hjq.1 hjp.2 hjq.2 hjc hjn
    intro he
    exact hnb ((chartAt (Model n) p₀.1).injOn
      ((stateChart_source p₀.1 _).mp hjp.1) ((stateChart_source p₀.1 _).mp hjq.1) he.symm)
  have hxq : Tendsto (fun j => chartAt (Model n) p₀.1 (q j).1) atTop (𝓝 (chartAt (Model n) p₀.1 p₀.1)) :=
    ((chartAt (Model n) p₀.1).continuousAt (mem_chart_source (Model n) p₀.1)).tendsto.comp hq
  obtain ⟨e,he,σ,hσ,hd⟩ := MovingTaylor.normalized_separation_subseq (base_chart_limit hp) hxq hbasene
  let R : ∀ j, ActiveRepresentation y h (p j) := fun j => Classical.choice (activeRepresentation_exists y h (hg j))
  obtain ⟨R₀,ρ,hρ,hθ,ha⟩ := activeRepresentation_subseq y h (hp.comp hσ.tendsto_atTop) (fun j => R (σ j))
  let τ := σ ∘ ρ
  have hτ : StrictMono τ := hσ.comp hρ
  have hCi (i : ActiveIndex n) : ℓ•R₀.a i ∈ injectivityDomain p₀.1 :=
    strict_radial_mem_injectivity (R₀.active i).1 hℓ.le hℓ₁
  choose C hC using fun i => ActionBranch.exists_of_nonconjugate (nonconjugate_of_mem_injectivity p₀.1 (hCi i))
  have hlim := branch_collision_limits y h (hp.comp hτ.tendsto_atTop) (hq.comp hτ.tendsto_atTop)
    (hs.comp hτ.tendsto_atTop) (hqp.comp hτ.tendsto_atTop)
    (hτ.tendsto_atTop hpos) hℓ hℓ₁ (hτ.tendsto_atTop hcollision) (hτ.tendsto_atTop hvalue)
    (fun j => R (τ j)) R₀ hθ ha B hB C hC (hd.comp hρ.tendsto_atTop) (hτ.tendsto_atTop hbasene)
  let T := tangentCoordinateEquiv p₀.1 p₀.1 (mem_chart_source (Model n) p₀.1)
  let ξ := T.symm e
  have heq : tangentChartLinear p₀.1 ξ = e := by
    rw [← tangentCoordinateEquiv_center]
    exact T.apply_symm_apply e
  have hξ : ξ ≠ 0 := by
    intro hz
    have he0 : e = 0 := by rw [← heq,hz,map_zero]
    rw [he0,norm_zero] at he
    norm_num at he
  rw [← heq] at hlim
  have hgap := collision_strict_gap y h hMTW R₀ hξ hs0 hsℓ hℓ₁ hbelow B hB C hC hlim.1
  exact (not_lt_of_ge hlim.2) hgap

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
