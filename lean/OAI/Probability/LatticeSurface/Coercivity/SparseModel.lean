import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.SparseColor
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

def Adj (x y : Vertex) : Prop :=
  y = (x.1+1,x.2) ∨ y = (x.1-1,x.2) ∨
  y = (x.1,x.2+1) ∨ y = (x.1,x.2-1) ∨
  y = (x.1+1,x.2-1) ∨ y = (x.1-1,x.2+1)

def latticeDist (x y : Vertex) : ℝ :=
  max (max |(x.1 : ℝ)-y.1| |(x.2 : ℝ)-y.2|)
    |((x.1 : ℝ)-y.1)+((x.2 : ℝ)-y.2)|

def height (V : Finset Vertex) (h : V → ℝ) (x : Vertex) : ℝ :=
  if hx : x ∈ V then h ⟨x,hx⟩ else 0

def body (V : Finset Vertex) : Set (V → ℝ) :=
  {h | ∀ x y, Adj x y → |height V h x-height V h y| ≤ 1}

def block (p : Parameters) (z : Vertex) : Set Vertex :=
  {x | (p.L:ℤ)*z.1 ≤ x.1 ∧ x.1 ≤ (p.L:ℤ)*(z.1+1) ∧
       (p.L:ℤ)*z.2 ≤ x.2 ∧ x.2 ≤ (p.L:ℤ)*(z.2+1)}

def enlarged (p : Parameters) (z : Vertex) : Set Vertex :=
  {x | (p.L:ℤ)*(z.1-1) ≤ x.1 ∧ x.1 ≤ (p.L:ℤ)*(z.1+2) ∧
       (p.L:ℤ)*(z.2-1) ≤ x.2 ∧ x.2 ≤ (p.L:ℤ)*(z.2+2)}

def face (p : Parameters) (z : Vertex) (i : Fin 4) : Vertex :=
  let a := (p.L:ℤ)*z.1; let b := (p.L:ℤ)*z.2; let n : ℤ := p.L/2
  if i = 0 then (a,b+n) else if i = 1 then (a+p.L,b+n)
  else if i = 2 then (a+n,b) else (a+n,b+p.L)

def neighbor (p : Parameters) (z : Vertex) (i : Fin 4) : Vertex :=
  let v := face p z i
  if i = 0 then (v.1,v.2+1) else if i = 1 then (v.1,v.2-1)
  else if i = 2 then (v.1+1,v.2) else (v.1-1,v.2)

def bad (p : Parameters) (V : Finset Vertex) (h : V → ℝ) (z : Vertex) : Prop :=
  enlarged p z ⊆ (V : Set Vertex) ∧
  ((∃ x ∈ block p z, ∃ y ∈ block p z, Adj x y ∧
      1-p.δ < |height V h x-height V h y|) ∨
   (∃ x ∈ enlarged p z, ∃ y ∈ enlarged p z, p.k₀ ≤ latticeDist x y ∧
      (1-p.δ₀)*latticeDist x y < |height V h x-height V h y|) ∨
   (∃ i : Fin 4, |height V h (neighbor p z i)-height V h (face p z i)| < p.s₀))

def thickBad (p : Parameters) (V : Finset Vertex) (h : V → ℝ)
    (m : ℕ) (z : Vertex) : Prop :=
  ∃ w, |w.1-z.1| ≤ m ∧ |w.2-z.2| ≤ m ∧ bad p V h w

end SparseBlocks

namespace SparseBlocks

attribute [local instance] Classical.propDecidable

lemma adj_symm {x y : Vertex} (h : Adj x y) : Adj y x :=
  TriangularLipschitz.adj_symm h

lemma adj_ne {x y : Vertex} (h : Adj x y) : x ≠ y :=
  TriangularLipschitz.adj_ne h

def finiteGraph (B : Finset Vertex) : SimpleGraph B :=
  TriangularLipschitz.latticeGraph.induce (B : Set Vertex)

def fixed (B V : Finset Vertex) : Set B := {x | x.val ∉ V}

def indexEquiv (B V : Finset Vertex) (hVB : V ⊆ B) : V ≃ ExtremalEdges.Free (fixed B V) where
  toFun x := ⟨⟨x,hVB x.property⟩, by simp [fixed]⟩
  invFun x := ⟨x.val.val, by simpa [fixed] using x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def coordinates (B V : Finset Vertex) (hVB : V ⊆ B) :
    (V → ℝ) ≃ᵐ (ExtremalEdges.Free (fixed B V) → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : ExtremalEdges.Free (fixed B V) => ℝ) (indexEquiv B V hVB)

lemma preserving_coordinates (B V : Finset Vertex) (hVB : V ⊆ B) :
    MeasurePreserving (coordinates B V hVB) :=
  volume_measurePreserving_piCongrLeft _ (indexEquiv B V hVB)

lemma coordinates_height (B V : Finset Vertex) (hVB : V ⊆ B)
    (h : V → ℝ) (x : B) :
    ExtremalEdges.height (fixed B V) (coordinates B V hVB h) x = height V h x.val := by
  by_cases hx : x.val ∈ V
  · have hxp : x ∉ fixed B V := by intro hxp; exact hxp hx
    rw [ExtremalEdges.height, dite_eq_right hxp, height, dite_eq_left hx]
    change (Equiv.piCongrLeft (fun _ : ExtremalEdges.Free (fixed B V) => ℝ)
      (indexEquiv B V hVB)) h ⟨x, by simpa [fixed] using hx⟩ = h ⟨x.val,hx⟩
    rw [Equiv.piCongrLeft_apply_eq_cast]
    rfl
  · simp [ExtremalEdges.height, fixed, height, hx]

lemma body_coordinates (B V : Finset Vertex) (hVB : V ⊆ B)
    (hcollar : ∀ x ∈ V, ∀ y, Adj x y → y ∈ B) :
    (coordinates B V hVB) ⁻¹' ExtremalEdges.body (finiteGraph B) (fixed B V) = body V := by
  ext h
  constructor
  · intro hh x y hxy
    by_cases hx : x ∈ V
    · have hyB := hcollar x hx y hxy
      have hb := hh ⟨x,hVB hx⟩ ⟨y,hyB⟩ (show (finiteGraph B).Adj _ _ from hxy)
      simpa only [coordinates_height] using hb
    · by_cases hy : y ∈ V
      · have hxB := hcollar y hy x (adj_symm hxy)
        have hb := hh ⟨x,hxB⟩ ⟨y,hVB hy⟩ (show (finiteGraph B).Adj _ _ from hxy)
        simpa only [coordinates_height] using hb
      · simp [height,hx,hy]
  · intro hh x y hxy
    simpa only [coordinates_height] using hh x.val y.val hxy

lemma continuous_height (V : Finset Vertex) (x : Vertex) :
    Continuous (fun h : V → ℝ => height V h x) := by
  unfold height
  split_ifs with hx
  · exact continuous_apply (⟨x,hx⟩ : V)
  · exact continuous_const

lemma closed_body (V : Finset Vertex) : IsClosed (body V) := by
  simp only [body, Set.ofPred_forall]
  exact isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun _ =>
    isClosed_le ((continuous_height V x).sub (continuous_height V y)).abs continuous_const

lemma volume_body_coordinates (B V : Finset Vertex) (hVB : V ⊆ B)
    (hcollar : ∀ x ∈ V, ∀ y, Adj x y → y ∈ B) :
    volume (ExtremalEdges.body (finiteGraph B) (fixed B V)) = volume (body V) := by
  rw [← body_coordinates B V hVB hcollar]
  exact ((preserving_coordinates B V hVB).measure_preimage
    (ExtremalEdges.closed_conditionalBody (finiteGraph B) (fixed B V) (fun _ => 0)).measurableSet.nullMeasurableSet).symm

end SparseBlocks

end
end
end
end

end OAI
