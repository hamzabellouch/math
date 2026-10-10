import OAI.Probability.ClassicalON.LatticeRadius

namespace OAI

universe uK

noncomputable section
open Set
open scoped Classical
namespace ClassicalON
variable {K : Type uK}

def SeparatedCenters (N : ℤ) (z : K → Site) : Prop := ∀ i j,i≠j → 4*N<siteRadius (z i) (z j)

def centerLabel (N : ℤ) (z : K → Site) (v : Site) : Option K :=
  if h : ∃ i,v∈annulusSites N (z i) then some h.choose else none

def centerPins (N : ℤ) (z : K → Site) : Set Site := {v | ∃ i,v∈annulusBoundary N (z i)}

theorem annulus_unique (N : ℤ) (z : K → Site) (hz : SeparatedCenters N z)
    (v : Site) {i j : K} (hi : v∈annulusSites N (z i)) (hj : v∈annulusSites N (z j)) : i=j := by
  by_contra h
  exact Set.disjoint_left.mp (annuli_disjoint (hz i j h)) hi hj

theorem centerLabel_some_iff (N : ℤ) (z : K → Site) (hz : SeparatedCenters N z) (v : Site) (i : K) :
    centerLabel N z v=some i ↔ v∈annulusSites N (z i) := by
  unfold centerLabel
  split_ifs with h
  · constructor
    · intro he
      have hi := Option.some.inj he
      exact hi ▸ h.choose_spec
    · intro hv
      congr 1
      exact annulus_unique N z hz v h.choose_spec hv
  · constructor
    · intro he; cases he
    · intro hv; exact False.elim (h ⟨i,hv⟩)

theorem centerLabel_none_iff (N : ℤ) (z : K → Site) (v : Site) :
    centerLabel N z v=none ↔ ∀ i,v∉annulusSites N (z i) := by
  simp only [centerLabel]
  split_ifs with h
  · constructor
    · intro he; cases he
    · intro hh; exact False.elim (hh h.choose h.choose_spec)
  · constructor
    · intro _ i hi; exact h ⟨i,hi⟩
    · intro _; rfl

theorem annulusBoundary_subset (N : ℤ) (hN : 0≤N) (z : Site) :
    annulusBoundary N z⊆annulusSites N z := by
  intro v hv
  change siteRadius z v=N ∨ siteRadius z v=2*N at hv
  change N≤ siteRadius z v ∧ siteRadius z v≤2*N
  omega

theorem local_centerPins_iff (N : ℤ) (hN : 0≤N) (z : K → Site) (hz : SeparatedCenters N z)
    (v : Site) (i : K) (hi : v∈annulusSites N (z i)) :
    v∈centerPins N z ↔ v∈annulusBoundary N (z i) := by
  constructor
  · rintro ⟨j,hj⟩
    have hij := annulus_unique N z hz v hi (annulusBoundary_subset N hN _ hj)
    exact hij ▸ hj
  · exact fun h => ⟨i,h⟩

namespace LatticeGraph

def annulusVertexLabel (G : LatticeGraph) (N : ℤ) (z : K → Site) : G.vertices → Option K :=
  fun v => centerLabel N z v.val

def annulusEdgeLabel (G : LatticeGraph) (N : ℤ) (z : K → Site) (e : G.edges) : Option K :=
  if h : ∃ i,e.val.1.val∈annulusSites N (z i) ∧ e.val.2.val∈annulusSites N (z i) then some h.choose else none

def allAnnulusPins (G : LatticeGraph) (N : ℤ) (z : K → Site) : Set G.vertices :=
  {v | v.val∈centerPins N z}

theorem annulusEdgeLabel_some_iff (G : LatticeGraph) (N : ℤ) (z : K → Site)
    (hz : SeparatedCenters N z) (e : G.edges) (i : K) :
    G.annulusEdgeLabel N z e=some i ↔
      e.val.1.val∈annulusSites N (z i) ∧ e.val.2.val∈annulusSites N (z i) := by
  unfold annulusEdgeLabel
  split_ifs with h
  · constructor
    · intro he
      exact Option.some.inj he ▸ h.choose_spec
    · intro hv
      congr 1
      exact annulus_unique N z hz _ h.choose_spec.1 hv.1
  · constructor
    · intro he; cases he
    · intro hv; exact False.elim (h ⟨i,hv⟩)

theorem annulus_vertex_edge_label (G : LatticeGraph) (N : ℤ) (_hN : 0≤N) (z : K → Site)
    (hz : SeparatedCenters N z) (e : G.edges) (v w : G.vertices)
    (he : (v=e.val.1 ∧ w=e.val.2) ∨ (v=e.val.2 ∧ w=e.val.1))
    (hv : v∉G.allAnnulusPins N z) : G.annulusVertexLabel N z v=G.annulusEdgeLabel N z e := by
  have hstep : PositiveNeighbor v.val w.val ∨ PositiveNeighbor w.val v.val := by
    rcases he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Or.inl (G.nearest e.val e.property)
    · exact Or.inr (G.nearest e.val e.property)
  have hvp : v.val∉centerPins N z := hv
  cases hl : G.annulusVertexLabel N z v with
  | none =>
    cases hel : G.annulusEdgeLabel N z e with
    | none => rfl
    | some i =>
      have hh := (G.annulusEdgeLabel_some_iff N z hz e i).mp hel
      have hh' : v.val∈annulusSites N (z i) := by rcases he with ⟨rfl,_⟩ | ⟨rfl,_⟩; exact hh.1; exact hh.2
      have := (centerLabel_some_iff N z hz v.val i).mpr hh'
      change G.annulusVertexLabel N z v=some i at this
      rw [hl] at this
      cases this
  | some i =>
    have hi := (centerLabel_some_iff N z hz v.val i).mp hl
    have hvi : v.val∈annulusInterior N (z i) :=
      (annulusSites_not_boundary N (z i) v.val).mp ⟨hi,fun h => hvp ⟨i,h⟩⟩
    have hwi := neighbor_in_annulus hvi hstep
    symm
    apply (G.annulusEdgeLabel_some_iff N z hz e i).mpr
    rcases he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨hi,hwi⟩
    · exact ⟨hwi,hi⟩

theorem annulus_left_label (G : LatticeGraph) (N : ℤ) (hN : 0≤N) (z : K → Site)
    (hz : SeparatedCenters N z) (e : G.edges) (hv : e.val.1∉G.allAnnulusPins N z) :
    G.annulusVertexLabel N z e.val.1=G.annulusEdgeLabel N z e :=
  G.annulus_vertex_edge_label N hN z hz e e.val.1 e.val.2 (Or.inl ⟨rfl,rfl⟩) hv

theorem annulus_right_label (G : LatticeGraph) (N : ℤ) (hN : 0≤N) (z : K → Site)
    (hz : SeparatedCenters N z) (e : G.edges) (hv : e.val.2∉G.allAnnulusPins N z) :
    G.annulusVertexLabel N z e.val.2=G.annulusEdgeLabel N z e :=
  G.annulus_vertex_edge_label N hN z hz e e.val.2 e.val.1 (Or.inr ⟨rfl,rfl⟩) hv

end LatticeGraph
end ClassicalON

end

end OAI
