import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.SparseColor
import OAI.Probability.LatticeSurface.Coercivity.SparseModel
import OAI.Probability.LatticeSurface.Coercivity.SparseParameters
import OAI.Probability.LatticeSurface.Convexity.BoundedBase
import OAI.Probability.LatticeSurface.Convexity.BrunnMinkowski
import OAI.Probability.LatticeSurface.Convexity.CubePrekopa
import OAI.Probability.LatticeSurface.Convexity.GradientWindows
import OAI.Probability.LatticeSurface.Convexity.QuantileTransport
import OAI.Probability.LatticeSurface.Convexity.WeightedPrekopa
import OAI.Probability.LatticeSurface.Dynamics.DisplacementInequality
import OAI.Probability.LatticeSurface.Geometry.BlockVolume
import OAI.Probability.LatticeSurface.Geometry.CapCentral
import OAI.Probability.LatticeSurface.Geometry.CapCompact
import OAI.Probability.LatticeSurface.Geometry.CapContract
import OAI.Probability.LatticeSurface.Geometry.CapCoordinates
import OAI.Probability.LatticeSurface.Geometry.CapMatching
import OAI.Probability.LatticeSurface.Geometry.CapOrient
import OAI.Probability.LatticeSurface.Geometry.CapReflection
import OAI.Probability.LatticeSurface.Geometry.CapSmall
import OAI.Probability.LatticeSurface.Geometry.CapSplit
import OAI.Probability.LatticeSurface.Geometry.CapUnpin
import OAI.Probability.LatticeSurface.Geometry.CapWeld
import OAI.Probability.LatticeSurface.Geometry.TriangularCover
import OAI.Probability.LatticeSurface.Geometry.TriangularGeometry
import OAI.Probability.LatticeSurface.Moments.ControlledGradients

namespace OAI

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

namespace FacetVolume

end FacetVolume

namespace ExtremalEdges

open scoped ENNReal

end ExtremalEdges

noncomputable section

open MeasureTheory Set

open scoped ENNReal

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V : Type*}

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V : Type*}

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V : Type*}

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V : Type*}

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V : Type*}

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V : Type*}

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V : Type*}

end ExtremalEdges

noncomputable section

namespace ExtremalEdges

open Finset

variable {V I : Type*} [Fintype V] [Fintype I]

attribute [local instance] Classical.propDecidable

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V I : Type*} [Fintype V] [Fintype I]

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

end ExtremalEdges

open MeasureTheory

open scoped ENNReal

noncomputable section

namespace TriangularLipschitz

end TriangularLipschitz

namespace SparseBlocks

attribute [local instance] Classical.propDecidable

end SparseBlocks

namespace SparseBlocks

attribute [local instance] Classical.propDecidable

end SparseBlocks

namespace SparseBlocks

attribute [local instance] Classical.propDecidable

def steps : Finset Vertex := {(1,0),(-1,0),(0,1),(0,-1),(1,-1),(-1,1)}

lemma steps_card : steps.card = 6 := by decide

lemma adj_iff_steps (x y : Vertex) : Adj x y ↔ y-x ∈ steps := by
  rcases x with ⟨a,b⟩; rcases y with ⟨c,d⟩
  simp only [Adj, steps, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq,
    Prod.sub_def]
  omega

lemma finiteGraph_degree (B : Finset Vertex) (x : B) : (finiteGraph B).degree x ≤ 6 := by
  classical
  rw [← (finiteGraph B).card_neighborFinset_eq_degree, ← steps_card]
  apply Finset.card_le_card_of_injOn (fun y : B => y.val-x.val)
  · intro y hy
    exact (adj_iff_steps _ _).mp ((finiteGraph B).mem_neighborFinset x y |>.mp hy)
  · intro y hy z hz he
    exact Subtype.ext (sub_left_injective he)

lemma adj_sub (x y a : Vertex) : Adj (x-a) (y-a) ↔ Adj x y := by
  rw [adj_iff_steps, adj_iff_steps]
  abel_nf

def largeBox (N : ℕ) : Finset Vertex :=
  Finset.Icc (-(N:ℤ)) N ×ˢ Finset.Icc (-(N:ℤ)) N

lemma largeBox_mem {N : ℕ} {x : Vertex} : x ∈ largeBox N ↔
    -(N:ℤ) ≤ x.1 ∧ x.1 ≤ N ∧ -(N:ℤ) ≤ x.2 ∧ x.2 ≤ N := by
  simp only [largeBox,Finset.mem_product,Finset.mem_Icc]
  tauto

def boxHom (N : ℕ) : TriangularLipschitz.boxGraph (2*N) →g finiteGraph (largeBox N) where
  toFun x := ⟨x.val-((N:ℤ),(N:ℤ)), by
    have hx := TriangularLipschitz.mem_box.mp x.property
    simp only [largeBox_mem,Prod.sub_def]
    constructor <;> omega⟩
  map_rel' := by
    intro x y hxy
    change Adj (x.val-((N:ℤ),(N:ℤ))) (y.val-((N:ℤ),(N:ℤ)))
    exact (adj_sub _ _ _).mpr hxy

lemma boxHom_surj (N : ℕ) : Function.Surjective (boxHom N) := by
  intro x
  have hx := largeBox_mem.mp x.property
  let y : TriangularLipschitz.BoxVertex (2*N) := ⟨x.val+((N:ℤ),(N:ℤ)), by
    simp only [TriangularLipschitz.mem_box,Prod.add_def]
    constructor <;> constructor <;> omega⟩
  exact ⟨y, Subtype.ext (by simp [boxHom,y])⟩

lemma largeBox_connected (N : ℕ) : (finiteGraph (largeBox N)).Connected :=
  (TriangularLipschitz.box_connected (2*N)).map (boxHom N) (boxHom_surj N)

lemma exists_ambient (V : Finset Vertex) : ∃ B : Finset Vertex,
    V ⊆ B ∧ (∀ x ∈ V, ∀ y, Adj x y → y ∈ B) ∧
    (finiteGraph B).Connected ∧ (fixed B V).Nonempty := by
  let R := V.sup (fun x => max x.1.natAbs x.2.natAbs)
  let N := R+2
  have hbound (x : Vertex) (hx : x ∈ V) :
      -(R:ℤ) ≤ x.1 ∧ x.1 ≤ R ∧ -(R:ℤ) ≤ x.2 ∧ x.2 ≤ R := by
    have hh : max x.1.natAbs x.2.natAbs ≤ R := Finset.le_sup (f := fun x : Vertex => max x.1.natAbs x.2.natAbs) hx
    have h1 : (|x.1| : ℤ) ≤ R := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast (le_max_left _ _).trans hh
    have h2 : (|x.2| : ℤ) ≤ R := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast (le_max_right _ _).trans hh
    exact ⟨(abs_le.mp h1).1,(abs_le.mp h1).2,(abs_le.mp h2).1,(abs_le.mp h2).2⟩
  refine ⟨largeBox N,?_,?_,largeBox_connected N,?_⟩
  · intro x hx
    have hh := hbound x hx
    apply largeBox_mem.mpr
    dsimp [N]
    omega
  · intro x hx y hxy
    have hh := hbound x hx
    apply largeBox_mem.mpr
    rcases x with ⟨a,b⟩; rcases y with ⟨c,d⟩
    simp only [Adj,Prod.mk.injEq] at hxy
    dsimp [N] at *
    omega
  · let x : largeBox N := ⟨((N:ℤ),(N:ℤ)), by simp [largeBox_mem]⟩
    refine ⟨x,?_⟩
    intro hx
    have hh := hbound x.val hx
    dsimp [x,N] at hh
    omega

end SparseBlocks

end
end
end
end

end OAI
