import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.OneDimensionalCritical
import OAI.Probability.CriticalPercolation.GraphGeometry.GraphBalls
import OAI.Probability.CriticalPercolation.GraphGeometry.EquivariantCoordinates
import OAI.Probability.CriticalPercolation.GraphGeometry.FiniteKernelOrbits

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E Λ : Type*} (G : BondGraph V E) [Group Λ] [MulAction Λ V] [MulAction Λ E]

def PreservesEnds : Prop :=
  ∀ (g : Λ) (e : E), G.ends (g • e)=Sym2.map (fun v : V => g • v) (G.ends e)

def smulAut (h : G.PreservesEnds (Λ := Λ)) (g : Λ) : G.Aut where
  vertex := MulAction.toPerm g
  edge := MulAction.toPerm g
  preserves := h g

lemma quasiTransitive_of_action (h : G.PreservesEnds (Λ := Λ))
    (S : Set V) (hS : S.Finite) (hcover : ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s) :
    G.QuasiTransitive := by
  refine ⟨S,hS,?_⟩
  intro v
  obtain ⟨s,hs,g,hg⟩ := hcover v
  exact ⟨s,hs,G.smulAut h g,hg⟩

lemma bounded_coordinate_jumps {A : Type*} [NormedAddCommGroup A]
    (hl : G.LocallyFinite) (h : G.PreservesEnds (Λ := Λ))
    (S : Set V) (hS : S.Finite) (hcover : ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s)
    (a : Λ → A) (π : V → A) (hπ : ∀ g v, π (g • v)=a g+π v) :
    ∃ D : ℝ, 0≤D ∧ ∀ e x y, G.ends e=s(x,y) → ‖π x-π y‖≤D := by
  let F : Set (V×V) := ⋃ s∈S, (fun w => (s,w)) '' G.fullGraph.neighborSet s
  have hF : F.Finite := hS.biUnion fun s _ => (G.finite_neighbors hl s).image _
  obtain ⟨D,hD⟩ := (hF.image (fun z => ‖π z.1-π z.2‖)).bddAbove
  refine ⟨max D 0,le_max_right _ _,?_⟩
  intro e x y he
  by_cases hxy : x=y
  · subst y
    simpa only [sub_self,norm_zero] using le_max_right D 0
  · have hadj : G.fullGraph.Adj x y := (SimpleGraph.fromEdgeSet_adj _).mpr
      ⟨⟨e,Set.mem_univ _,he⟩,hxy⟩
    obtain ⟨s,hs,g,hgx⟩ := hcover x
    change g • s=x at hgx
    let w := g⁻¹ • y
    have hgw : g • w=y := smul_inv_smul g y
    have hsw : G.fullGraph.Adj s w := by
      apply (Aut.fullGraph_adj G (G.smulAut h g) s w).mp
      change G.fullGraph.Adj (g • s) (g • w)
      rwa [hgx,hgw]
    have hf : (s,w)∈F := Set.mem_iUnion₂.mpr ⟨s,hs,w,hsw,rfl⟩
    have hd : ‖π s-π w‖≤D := hD ⟨(s,w),hf,rfl⟩
    have hdiff : π x-π y=π s-π w := by
      rw [← hgx,← hgw,hπ,hπ]
      abel
    rw [hdiff]
    exact hd.trans (le_max_left _ _)

theorem finite_by_integer_critical_one {N : Type*} [Group N]
    (hl : G.LocallyFinite) (h : G.PreservesEnds (Λ := Λ))
    (S : Set V) (hS : S.Finite) (hcover : ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s)
    (ρ : Λ →* N) (hρ : Function.Surjective ρ)
    (φ : N →* Multiplicative ℤ) (hφ : Function.Surjective φ)
    (hf : (φ.ker : Set N).Finite)
    (hker : ∀ v : V, (MulAction.orbit ρ.ker v).Finite)
    (hstab : ∀ v : V, ((MulAction.stabilizer Λ v).map ρ : Set N).Finite) :
    G.criticalProbability=1 := by
  let a := φ.comp ρ
  obtain ⟨π,hπ⟩ := EquivariantCoordinates.exists_equivariant a
    (EquivariantCoordinates.stabilizer_killed ρ φ hstab)
  let πa : V → ℤ := fun v => (π v).toAdd
  have hπa : ∀ (g : Λ) (v : V), πa (g • v)=(a g).toAdd+πa v := by
    intro g v
    exact congrArg Multiplicative.toAdd (hπ g v)
  have hfib : ∀ t : ℤ, (πa ⁻¹' {t}).Finite := by
    intro t
    exact EquivariantCoordinates.finite_fibers a π hπ
      (EquivariantCoordinates.finite_composite_kernel_orbits ρ φ hf hker)
      S hS hcover (Multiplicative.ofAdd t)
  have htrans : ∀ t : ℤ, ∃ ψ : G.Aut, ∀ v, πa (ψ.vertex v)=πa v+t := by
    intro t
    obtain ⟨g,hg⟩ := hφ.comp hρ (Multiplicative.ofAdd t)
    refine ⟨G.smulAut h g,?_⟩
    intro v
    change πa (g • v)=πa v+t
    rw [hπa]
    rw [show a g=Multiplicative.ofAdd t from hg]
    exact add_comm _ _
  obtain ⟨D,hD,hjump⟩ := G.bounded_coordinate_jumps hl h S hS hcover
    (fun g => (a g).toAdd) πa hπa
  obtain ⟨J,hJ⟩ := exists_nat_gt D
  apply G.proper_integer_height_critical_one hl πa hfib J _ htrans
  intro e x y he
  have hh := (hjump e x y he).trans hJ.le
  rw [Int.norm_eq_abs,← Int.cast_abs] at hh
  exact_mod_cast hh

end CriticalPercolation.BondGraph
end
end
end

end OAI
