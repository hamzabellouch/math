import OAI.Probability.ClassicalON.LatticeRestriction

namespace OAI

noncomputable section
open Set
open scoped Classical
namespace ClassicalON

def siteRadius (z v : Site) : ℤ := max |v.1-z.1| |v.2-z.2|

@[simp] theorem siteRadius_self (z : Site) : siteRadius z z=0 := by simp [siteRadius]

theorem siteRadius_nonneg (z v : Site) : 0≤ siteRadius z v := le_trans (abs_nonneg _) (le_max_left _ _)

theorem siteRadius_symm (z v : Site) : siteRadius z v=siteRadius v z := by
  simp only [siteRadius,abs_sub_comm]

theorem siteRadius_le_iff (z v : Site) (N : ℤ) :
    siteRadius z v≤N ↔ |v.1-z.1|≤N ∧ |v.2-z.2|≤N := max_le_iff

theorem siteRadius_triangle (x y z : Site) : siteRadius x z≤ siteRadius x y+siteRadius y z := by
  apply max_le
  · have h := abs_add_le (y.1-x.1) (z.1-y.1)
    have h1 : |y.1-x.1|≤ siteRadius x y := le_max_left _ _
    have h2 : |z.1-y.1|≤ siteRadius y z := le_max_left _ _
    have he : (y.1-x.1)+(z.1-y.1)=z.1-x.1 := by ring
    rw [he] at h
    omega
  · have h := abs_add_le (y.2-x.2) (z.2-y.2)
    have h1 : |y.2-x.2|≤ siteRadius x y := le_max_right _ _
    have h2 : |z.2-y.2|≤ siteRadius y z := le_max_right _ _
    have he : (y.2-x.2)+(z.2-y.2)=z.2-x.2 := by ring
    rw [he] at h
    omega

theorem siteRadius_neighbor {x y : Site} (h : PositiveNeighbor x y) : siteRadius x y=1 := by
  rcases h with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> simp [siteRadius,h1,h2]

theorem siteRadius_neighbor_step (z : Site) {x y : Site} (h : PositiveNeighbor x y ∨ PositiveNeighbor y x) :
    siteRadius z y≤ siteRadius z x+1 ∧ siteRadius z x≤ siteRadius z y+1 := by
  have hh : siteRadius x y=1 := by
    rcases h with h | h
    · exact siteRadius_neighbor h
    · rw [siteRadius_symm]; exact siteRadius_neighbor h
  constructor
  · simpa only [hh] using siteRadius_triangle z x y
  · have := siteRadius_triangle z y x
    rwa [siteRadius_symm y x,hh] at this

def annulusSites (N : ℤ) (z : Site) : Set Site := {v | N≤ siteRadius z v ∧ siteRadius z v≤2*N}

def annulusBoundary (N : ℤ) (z : Site) : Set Site := {v | siteRadius z v=N ∨ siteRadius z v=2*N}

def annulusInterior (N : ℤ) (z : Site) : Set Site := {v | N<siteRadius z v ∧ siteRadius z v<2*N}

theorem annulusSites_not_boundary (N : ℤ) (z v : Site) :
    v∈annulusSites N z ∧ v∉annulusBoundary N z ↔ v∈annulusInterior N z := by
  simp only [annulusSites,annulusBoundary,annulusInterior,mem_ofPred_eq]
  omega

theorem neighbor_in_annulus {N : ℤ} {z x y : Site} (hx : x∈annulusInterior N z)
    (hxy : PositiveNeighbor x y ∨ PositiveNeighbor y x) : y∈annulusSites N z := by
  have hh := siteRadius_neighbor_step z hxy
  change N<siteRadius z x ∧ siteRadius z x<2*N at hx
  change N≤ siteRadius z y ∧ siteRadius z y≤2*N
  omega

theorem annuli_disjoint {N : ℤ} {x y : Site} (hxy : 4*N<siteRadius x y) :
    Disjoint (annulusSites N x) (annulusSites N y) := by
  apply Set.disjoint_left.mpr
  intro z hx hy
  have ht := siteRadius_triangle x z y
  rw [siteRadius_symm z y] at ht
  change N≤ siteRadius x z ∧ siteRadius x z≤2*N at hx
  change N≤ siteRadius y z ∧ siteRadius y z≤2*N at hy
  omega

namespace LatticeGraph

def annulusGraph (G : LatticeGraph) (N : ℤ) (z : Site) := G.restrict (·∈annulusSites N z)

def annulusInner (G : LatticeGraph) (N : ℤ) (z : Site) : Set (G.annulusGraph N z).vertices :=
  {v | siteRadius z v.val=N}

def annulusOuter (G : LatticeGraph) (N : ℤ) (z : Site) : Set (G.annulusGraph N z).vertices :=
  {v | siteRadius z v.val=2*N}

def annulusPins (G : LatticeGraph) (N : ℤ) (z : Site) : Set (G.annulusGraph N z).vertices :=
  G.annulusInner N z∪G.annulusOuter N z

def annulusCoupling (G : LatticeGraph) (b : G.edges → ℝ) (N : ℤ) (z : Site) :
    (G.annulusGraph N z).edges → ℝ := fun e => b (G.restrictEdge _ e)

end LatticeGraph
end ClassicalON

end

end OAI
