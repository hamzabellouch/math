import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.SparseAmbient
import OAI.Probability.LatticeSurface.Coercivity.SparseColor
import OAI.Probability.LatticeSurface.Coercivity.SparseEntropy
import OAI.Probability.LatticeSurface.Coercivity.SparseGeodesic
import OAI.Probability.LatticeSurface.Coercivity.SparseGeometry
import OAI.Probability.LatticeSurface.Coercivity.SparseGradients
import OAI.Probability.LatticeSurface.Coercivity.SparseModel
import OAI.Probability.LatticeSurface.Coercivity.SparseParameters
import OAI.Probability.LatticeSurface.Coercivity.SparsePaths
import OAI.Probability.LatticeSurface.Coercivity.SparseProb
import OAI.Probability.LatticeSurface.Coercivity.SparseSeparated
import OAI.Probability.LatticeSurface.Coercivity.SparseWitnessModel
import OAI.Probability.LatticeSurface.Coercivity.ZeroPinnedSparse
import OAI.Probability.LatticeSurface.Convexity.BoundedBase
import OAI.Probability.LatticeSurface.Convexity.BrunnMinkowski
import OAI.Probability.LatticeSurface.Convexity.CubePrekopa
import OAI.Probability.LatticeSurface.Convexity.GradientWindows
import OAI.Probability.LatticeSurface.Convexity.ProductVolume
import OAI.Probability.LatticeSurface.Convexity.QuantileTransport
import OAI.Probability.LatticeSurface.Convexity.RetainedBody
import OAI.Probability.LatticeSurface.Convexity.RetainedCoordinates
import OAI.Probability.LatticeSurface.Convexity.RetainedShell
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
import OAI.Probability.LatticeSurface.Moments.OrderedGradients

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

end SparseBlocks

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

end ExtremalEdges

namespace SparseBlocks

attribute [local instance] Classical.propDecidable

end SparseBlocks

namespace SparseBlocks

attribute [local instance] Classical.propDecidable

end SparseBlocks

noncomputable section

open scoped BigOperators

namespace SparsePaths

attribute [local instance] Classical.propDecidable

end SparsePaths

noncomputable section

open scoped BigOperators

namespace SparseWitness

attribute [local instance] Classical.propDecidable

end SparseWitness

noncomputable section

open Set MeasureTheory

open scoped BigOperators

namespace SparseWitness

attribute [local instance] Classical.propDecidable

end SparseWitness

namespace SparseBlocks

attribute [local instance] Classical.propDecidable

end SparseBlocks

namespace SparseBlocks

attribute [local instance] Classical.propDecidable

end SparseBlocks

namespace SparseBlocks

open Filter

open scoped Topology

end SparseBlocks

namespace SparseBlocks

attribute [local instance] Classical.propDecidable

end SparseBlocks

namespace SparseBlocks

attribute [local instance] Classical.propDecidable

end SparseBlocks

namespace SparseBlocks

attribute [local instance] Classical.propDecidable

end SparseBlocks

namespace RetainedShell

open TriangularLipschitz

attribute [local instance] Classical.propDecidable

end RetainedShell

namespace RetainedShell

open TriangularLipschitz

attribute [local instance] Classical.propDecidable

end RetainedShell

namespace RetainedShell

open TriangularLipschitz

end RetainedShell

namespace ProductVolume

universe u v

variable {ι : Type u} [Fintype ι] {J : ι → Type v} [∀ i, Fintype (J i)]

end ProductVolume

namespace RetainedShell

open TriangularLipschitz

attribute [local instance] Classical.propDecidable

end RetainedShell

namespace SparseBlocks

end SparseBlocks

namespace RetainedShell

open TriangularLipschitz

attribute [local instance] Classical.propDecidable

end RetainedShell

namespace RetainedShell

open TriangularLipschitz

attribute [local instance] Classical.propDecidable

lemma retainedHeight_add (L : ℕ) (V J : Finset Vertex) (s t : retained L V J → ℝ) (x : Vertex) :
    retainedHeight L V J (s+t) x=retainedHeight L V J s x+retainedHeight L V J t x := by
  by_cases hx : x∈retained L V J <;> simp [retainedHeight,hx]

lemma retainedHeight_sub (L : ℕ) (V J : Finset Vertex) (s t : retained L V J → ℝ) (x : Vertex) :
    retainedHeight L V J (s-t) x=retainedHeight L V J s x-retainedHeight L V J t x := by
  by_cases hx : x∈retained L V J <;> simp [retainedHeight,hx]

lemma fillingPolytope_congr_shell {L : ℕ} {s t : Vertex → ℝ}
    (h : ∀ x∈box L,x∉interior L → s x=t x) : fillingPolytope L s=fillingPolytope L t := by
  have he (a : Filling L) (x : Vertex) (hx : x∈box L) : filledHeight L s a x=filledHeight L t a x := by
    by_cases hi : x∈interior L
    · simp [filledHeight,hi]
    · simp [filledHeight,hi,h x hx hi]
  ext a
  constructor
  · intro ha x hx y hy hxy
    rw [← he a x hx,← he a y hy]
    exact ha x hx y hy hxy
  · intro ha x hx y hy hxy
    rw [he a x hx,he a y hy]
    exact ha x hx y hy hxy

lemma fillingVolume_congr_shell {L : ℕ} {s t : Vertex → ℝ}
    (h : ∀ x∈box L,x∉interior L → s x=t x) : fillingVolume L s=fillingVolume L t := by
  unfold fillingVolume;rw [fillingPolytope_congr_shell h]

lemma height_retained {L : ℕ} (hL : 0<L) (V J : Finset Vertex)
    (hf : ∀ z∈J,∀ x∈box L,base L z+x∈V) (h : V → ℝ) {x : Vertex} (hx : x∉bulk L J) :
    SparseBlocks.height V h x=retainedHeight L V J (split hL V J hf h).1 x := by
  by_cases hv : x∈V
  · have hr : x∈retained L V J := Finset.mem_sdiff.mpr ⟨hv,hx⟩
    simp [SparseBlocks.height,retainedHeight,hv,hr,split_fst]
  · have hr : x∉retained L V J := fun hr => hv (Finset.mem_sdiff.mp hr).1
    simp [SparseBlocks.height,retainedHeight,hv,hr]

end RetainedShell

namespace RetainedShell

open TriangularLipschitz

theorem feasible_shift_extension {L : ℕ} (_hL : 0<L) (V J : Finset Vertex)
    (hf : ∀ z∈J,∀ x∈box L,base L z+x∈V) (s χ : retained L V J → ℝ)
    (hp : 0<shellDensity L V J (s+χ)) (hm : 0<shellDensity L V J (s-χ)) :
    ∃ ψ : Vertex → ℝ,(∀ x y,Adj x y → |ψ x-ψ y|≤1) ∧
      (∀ x,x∉V → ψ x=0) ∧
      (∀ x,x∉bulk L J → ψ x=retainedHeight L V J χ x) := by
  obtain ⟨a,ha⟩ := nonempty_of_measure_ne_zero hp.ne'
  obtain ⟨b,hb⟩ := nonempty_of_measure_ne_zero hm.ne'
  let u := assembled L V J (s+χ) a
  let v := assembled L V J (s-χ) b
  let ψ : Vertex → ℝ := fun x => (u x-v x)/2
  refine ⟨ψ,?_,?_,?_⟩
  · intro x y hxy
    have hu : |u x-u y|≤1 := ha x y hxy
    have hv : |v x-v y|≤1 := hb x y hxy
    have he : ψ x-ψ y=((u x-u y)-(v x-v y))/2 := by dsimp [ψ];ring
    rw [he,abs_div,show |(2:ℝ)|=2 from abs_of_pos (by norm_num)]
    apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    exact (abs_sub _ _).trans (by linarith)
  · intro x hx
    dsimp [ψ,u,v]
    rw [assembled_zero_exterior L V J hf _ _ hx,assembled_zero_exterior L V J hf _ _ hx]
    norm_num
  · intro x hx
    dsimp [ψ,u,v]
    rw [assembled_remaining L V J _ _ hx,assembled_remaining L V J _ _ hx,
      retainedHeight_add,retainedHeight_sub]
    ring

end RetainedShell

end
end
end
end
end
end
end

end OAI
