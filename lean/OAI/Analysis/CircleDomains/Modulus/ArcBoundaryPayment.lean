import OAI.Analysis.CircleDomains.Probability.SimpleArcDomainDensity

namespace OAI

/-! Pass the actual path inequality to free boundary traces along a
simple arc. Only approximation by domain points is used. -/

open Set Function Filter
open scoped Topology
namespace CircleDomainRigidity

theorem trace_payment_of_domain_closure
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {S U : Set X} (hSU : S ⊆ U) {x y : X}
    (hx : x ∈ closure S) (hy : y ∈ closure S)
    (u : X → ℝ) {a b A : ℝ}
    (ha : Tendsto u (𝓝[U] x) (𝓝 a)) (hb : Tendsto u (𝓝[U] y) (𝓝 b))
    (hpay : ∀p ∈ S, ∀q ∈ S, |u p - u q| ≤ A) : |a - b| ≤ A := by
  obtain ⟨p, hp, hpx⟩ := mem_closure_iff_seq_limit.mp hx
  obtain ⟨q, hq, hqy⟩ := mem_closure_iff_seq_limit.mp hy
  have hpU : Tendsto p atTop (𝓝[U] x) :=
    tendsto_nhdsWithin_iff.mpr ⟨hpx, Eventually.of_forall (fun n => hSU (hp n))⟩
  have hqU : Tendsto q atTop (𝓝[U] y) :=
    tendsto_nhdsWithin_iff.mpr ⟨hqy, Eventually.of_forall (fun n => hSU (hq n))⟩
  have hlim : Tendsto (fun n => |u (p n) - u (q n)|) atTop (𝓝 |a - b|) :=
    ((ha.comp hpU).sub (hb.comp hqU)).abs
  exact le_of_tendsto hlim (Eventually.of_forall (fun n => hpay _ (hp n) _ (hq n)))

theorem simple_arc_boundary_payment
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {U B : Set X} (hB : IsTotallyDisconnected B) (hBU : Bᶜ ⊆ U)
    {x y : X} (γ : Path x y) (hinj : Injective γ)
    (u : X → ℝ) {a b A : ℝ}
    (ha : Tendsto u (𝓝[U] x) (𝓝 a)) (hb : Tendsto u (𝓝[U] y) (𝓝 b))
    (hpay : ∀p ∈ range γ ∩ U, ∀q ∈ range γ ∩ U, |u p - u q| ≤ A) :
    |a - b| ≤ A := by
  apply trace_payment_of_domain_closure inter_subset_right ?_ ?_ u ha hb hpay
  · simpa only [γ.source] using
      simple_arc_point_mem_closure_domain hB hBU γ γ.continuous hinj 0
  · simpa only [γ.target] using
      simple_arc_point_mem_closure_domain hB hBU γ γ.continuous hinj 1

end CircleDomainRigidity

end OAI
