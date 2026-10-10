import OAI.Geometry.SurfaceImmersion.Primitive.CrossingNeighborhood

namespace OAI

/-! Construct the local normal change at one crossing with support in any
prescribed neighborhood. No normal path or cutoff is assumed. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem local_crossing_adjustment {U O : Set E} (hU : IsOpen U) (hO : IsOpen O)
    {n p q : E → Vec} (hn : ContDiffOn ℝ ∞ n U)
    (hp : ContDiffOn ℝ ∞ p U) (hq : ContDiffOn ℝ ∞ q U)
    (hunit : ∀ y ∈ U, n y ⬝ᵥ n y = 1) {x : E} (hx : x ∈ U) (hxO : x ∈ O)
    {w : Vec} (hnw : n x ⬝ᵥ w = 0) (hpw : 0 < p x ⬝ᵥ w)
    (hqw : 0 < q x ⬝ᵥ w) (hpq : 0 < p x ⬝ᵥ q x) :
    ∃ g : E → Vec, ContDiffOn ℝ ∞ g U ∧
      (∀ y ∈ U, g y ⬝ᵥ g y = 1) ∧
      (∀ y ∈ U, y ∉ O → g y = n y) ∧
      (∀ y ∈ U, n y ≠ -normalize (p y) → g y ≠ -normalize (p y)) ∧
      (∀ y ∈ U, n y ≠ -normalize (q y) → g y ≠ -normalize (q y)) ∧
      (∀ y ∈ U, ∀ v : Vec, v ⬝ᵥ n y = 0 → v ⬝ᵥ p y = 0 → v ⬝ᵥ g y = 0) ∧
      0 < p x ⬝ᵥ g x ∧ 0 < q x ⬝ᵥ g x := by
  obtain ⟨W,hW,hxW,hWU,m,_,hgeom⟩ :=
    crossing_halfplane_neighborhood hU hn hp hq hunit hx hnw hpw hqw hpq
  obtain ⟨χ,hχ,_,hχrange,hχsupport,hχone⟩ := CollarVelocity.compact_cutoff
    (isCompact_singleton : IsCompact ({x} : Set E)) (hW.inter hO)
    (by intro y hy; simpa only [mem_inter_iff,mem_singleton_iff.mp hy] using And.intro hxW hxO)
  have hs : tsupport χ ⊆ W := hχsupport.trans inter_subset_left
  obtain ⟨hg,hgu,hge,hga,hgpos,hgperp⟩ := supported_crossing_adjustment hU hW hWU
    hn (hp.mono hWU) hχ hχrange hs hunit hgeom
  let g : E → Vec := fun y => first (n y) (normalize (p y)) (χ y)
  have hpos := hgpos x hxW (hχone x (mem_singleton x))
  refine ⟨g,hg,hgu,?_,?_,?_,hgperp,hpos⟩
  · intro y hy hyO
    exact hge y hy (fun h => hyO (hχsupport h).2)
  · intro y hy hanti
    by_cases hyW : y ∈ W
    · exact (hga y hyW).1
    · exact fun he => hanti ((hge y hy (fun h => hyW (hs h))).symm.trans he)
  · intro y hy hanti
    by_cases hyW : y ∈ W
    · exact (hga y hyW).2
    · exact fun he => hanti ((hge y hy (fun h => hyW (hs h))).symm.trans he)

end ClosedSurfaceR4.VelocityFrame

end

end OAI
