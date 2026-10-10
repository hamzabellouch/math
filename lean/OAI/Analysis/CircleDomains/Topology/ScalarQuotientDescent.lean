import OAI.Analysis.CircleDomains.Topology.ClosedMapDescent

namespace OAI

/-! A continuous scalar constant on closed quotient fibers descends
continuously. An exact zero neighborhood also descends when its fiber
is a singleton. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem closed_map_scalar_descent_continuous
    {X Y : Type*} [Nonempty X] [TopologicalSpace X] [TopologicalSpace Y]
    {P : X → Y} (hP : IsClosedMap P) (hsurj : Surjective P)
    {a : X → ℝ} (ha : Continuous a)
    (hc : ∀ x y, P x = P y → a x = a y) :
    Continuous (fun y => a (invFun P y)) := by
  rw [continuous_iff_continuousAt]
  intro y
  exact (closed_map_section_continuousAt_of_fiber hP (invFun P)
    (rightInverse_invFun hsurj) (fun x _ => ha.continuousAt)
    (fun x hx => hc x (invFun P y) (hx.trans (rightInverse_invFun hsurj y).symm))).1

 theorem scalar_descent_on_projection
    {X Y : Type*} [Nonempty X] {P : X → Y} (hsurj : Surjective P) {a : X → ℝ}
    (hc : ∀ x y, P x = P y → a x = a y) (x : X) :
    a (invFun P (P x)) = a x := hc _ _ (rightInverse_invFun hsurj _)

 theorem closed_map_zero_neighborhood_descends
    {X Y : Type*} [Nonempty X] [TopologicalSpace X] [TopologicalSpace Y]
    {P : X → Y} (hP : IsClosedMap P) (hsurj : Surjective P)
    {p : X} (hfiber : P ⁻¹' {P p} = {p}) {a : X → ℝ}
    (ha : ∀ᶠ x in 𝓝 p, a x = 0) :
    ∀ᶠ y in 𝓝 (P p), a (invFun P y) = 0 := by
  obtain ⟨U, hUzero, hU, hpU⟩ := mem_nhds_iff.mp ha
  have hV : IsOpen (kernImage P U) := isClosedMap_iff_kernImage.mp hP hU
  have hpV : P p ∈ kernImage P U := by
    intro x hx
    have hxp : x = p := by
      have hh : x ∈ P ⁻¹' {P p} := hx
      simpa only [hfiber, mem_singleton_iff] using hh
    exact hxp ▸ hpU
  filter_upwards [hV.mem_nhds hpV] with y hy
  exact hUzero (hy (rightInverse_invFun hsurj y))

end CircleDomainRigidity

end

end OAI
