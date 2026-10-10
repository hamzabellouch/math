import OAI.Analysis.CircleDomains.Reflection.AnalyticJordanClosedExterior

namespace OAI

/-! The canonical closed-exterior extension has the actual target-circle
boundary values, forced by the interior conformal equivalence. -/
open Set Function Filter Metric Complex
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma analytic_jordan_closed_exterior_boundary_norm {H : ℂ ≃ₜ ℂ}
    (hH : IsAnalyticJordanCap H) {f : Sphere → Sphere} {d : ℂ} {s : ℝ}
    (hs : 0<s) (hf : IsConformalEquivalence f (closedTerminalCap H)ᶜ
      ((((↑) : ℂ → Sphere) '' closedBall d s)ᶜ))
    {x : ℂ} (hx : x∈frontier (jordanInterior H)) :
    ‖extendFrom (closure (jordanInterior H))ᶜ
      (fun z : ℂ => finiteCoord (exteriorDiskNormalization d s hs (f (z : Sphere)))) x‖=1 := by
  let A := (closure (jordanInterior H))ᶜ
  let g := fun z : ℂ => finiteCoord (exteriorDiskNormalization d s hs (f (z : Sphere)))
  have hxJ : x∈closure (jordanInterior H) ∧ x∉jordanInterior H := by
    simpa only [(jordanInterior_isOpen H).frontier_eq,Set.mem_sdiff] using hx
  have hxA : x∈closure A := by
    simpa only [A,closure_compl,interior_closure_jordanInterior,mem_compl_iff] using hxJ.2
  have : NeBot (𝓝[A] x) := mem_closure_iff_nhdsWithin_neBot.mp hxA
  obtain ⟨hc,he⟩ := analytic_jordan_closed_exterior_extension hH hs hf
  change ContinuousOn (extendFrom A g) (closure A) at hc
  change EqOn (extendFrom A g) g A at he
  have hge : Tendsto g (𝓝[A] x) (𝓝 (extendFrom A g x)) := by
    apply ((hc x hxA).mono (subset_closure : A⊆closure A)).congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact he hz
  have hco : Tendsto (fun z : ℂ => (z : Sphere)) (𝓝[A] x)
      (𝓝[(closedTerminalCap H)ᶜ] (x : Sphere)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨OnePoint.continuous_coe.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz
    rintro ⟨w,hw,he⟩
    exact hz (OnePoint.coe_injective he ▸ hw)
  have hout : (x : Sphere)∉(closedTerminalCap H)ᶜ := by
    intro h
    exact h ⟨x,hxJ.1,rfl⟩
  have hn := (hf.trans (isConformalEquivalence_exteriorDiskNormalization d hs)).tendsto_disk_boundary_modulus
    zero_lt_one hout
  have hgn : Tendsto (fun z => ‖g z‖) (𝓝[A] x) (𝓝 1) := by
    simpa only [g,Function.comp_def,sub_zero] using hn.comp hco
  exact tendsto_nhds_unique hge.norm hgn

end CircleDomainRigidity

end

end OAI
