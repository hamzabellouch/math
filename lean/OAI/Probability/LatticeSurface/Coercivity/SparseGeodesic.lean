import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.SparseAmbient
import OAI.Probability.LatticeSurface.Coercivity.SparseColor
import OAI.Probability.LatticeSurface.Coercivity.SparseEntropy
import OAI.Probability.LatticeSurface.Coercivity.SparseGeometry
import OAI.Probability.LatticeSurface.Coercivity.SparseGradients
import OAI.Probability.LatticeSurface.Coercivity.SparseModel
import OAI.Probability.LatticeSurface.Coercivity.SparseParameters
import OAI.Probability.LatticeSurface.Coercivity.SparsePaths
import OAI.Probability.LatticeSurface.Coercivity.SparseProb
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

local instance (sort : Sort*) : DecidableEq sort := Classical.typeDecidableEq sort

def geodesic (L : ℕ) (x y : TriangularLipschitz.BoxVertex (3*L)) :
    (TriangularLipschitz.boxGraph (3*L)).Walk x y :=
  Classical.choose ((TriangularLipschitz.box_connected (3*L)).exists_path_of_dist x y)

lemma geodesic_isPath (L : ℕ) (x y : TriangularLipschitz.BoxVertex (3*L)) :
    (geodesic L x y).IsPath :=
  (Classical.choose_spec ((TriangularLipschitz.box_connected (3*L)).exists_path_of_dist x y)).1

lemma geodesic_length (L : ℕ) (x y : TriangularLipschitz.BoxVertex (3*L)) :
    ((geodesic L x y).length : ℝ) = TriangularLipschitz.latticeDist x.val y.val := by
  unfold geodesic
  rw [(Classical.choose_spec ((TriangularLipschitz.box_connected (3*L)).exists_path_of_dist x y)).2,
    TriangularLipschitz.box_dist]

def pathEdges (L : ℕ) (z : Vertex) (xy : TriangularLipschitz.BoxVertex (3*L) ×
    TriangularLipschitz.BoxVertex (3*L)) : Finset (Vertex × Vertex) :=
  SparsePaths.edges (translate L z) (geodesic L xy.1 xy.2)

lemma pathEdges_card (L : ℕ) (z : Vertex) (xy : TriangularLipschitz.BoxVertex (3*L) ×
    TriangularLipschitz.BoxVertex (3*L)) :
    ((pathEdges L z xy).card : ℝ) = latticeDist (translate L z xy.1) (translate L z xy.2) := by
  rw [pathEdges,SparsePaths.card_edges _ (translate_injective L z) _ (geodesic_isPath _ _ _),
    geodesic_length,translate_dist]

lemma pathEdges_mem (L : ℕ) (z : Vertex) (xy : TriangularLipschitz.BoxVertex (3*L) ×
    TriangularLipschitz.BoxVertex (3*L)) (e : Vertex × Vertex) (he : e ∈ pathEdges L z xy) :
    e.1 ∈ sites L z ∧ e.2 ∈ sites L z ∧ Adj e.1 e.2 := by
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp he)
  exact ⟨translate_mem _ _ _,translate_mem _ _ _,(translate_adj _ _ _ _).mpr d.adj⟩

lemma pathEdges_sum (L : ℕ) (z : Vertex) (xy : TriangularLipschitz.BoxVertex (3*L) ×
    TriangularLipschitz.BoxVertex (3*L)) (h : Vertex → ℝ) :
    |h (translate L z xy.1)-h (translate L z xy.2)| ≤
      ∑ e ∈ pathEdges L z xy, |h e.1-h e.2| :=
  SparsePaths.sum_edges _ (translate_injective L z) _ (geodesic_isPath _ _ _) h

lemma box_card (L : ℕ) : Fintype.card (TriangularLipschitz.BoxVertex L) = (L+1)^2 := by
  change Fintype.card (↥(TriangularLipschitz.box L)) = _
  rw [Fintype.card_coe]
  simp [TriangularLipschitz.box,Int.card_Icc,pow_two]

def safeEvent (V : Finset Vertex) (b : Bool) (u : ℝ) (e : Vertex × Vertex) : Set (V → ℝ) :=
  {h | Adj e.1 e.2 ∧ e.1 ∈ V ∧ e.2 ∈ V ∧ h ∈ edgeEvent V b u e}

lemma joint_safe_gradients (V : Finset Vertex) (b : Bool) (u : ℝ)
    (hu : 0 < u) (hu8 : u ≤ 1/8) (F : Finset (Vertex × Vertex)) :
    (law V).real {h | ∀ e ∈ F, h ∈ safeEvent V b u e} ≤
      ((ExtremalEdges.gradientConstant 6*u)^(1/ExtremalEdges.gradientConstant 6))^F.card := by
  by_cases hv : ∀ e ∈ F, Adj e.1 e.2 ∧ e.1 ∈ V ∧ e.2 ∈ V
  · calc
      _ ≤ (law V).real (gradientEvent V b u F) := by
        apply measureReal_mono _ (measure_ne_top _ _)
        intro h hh e he
        exact (hh e he).2.2.2
      _ ≤ _ := joint_gradients V F (fun e he => (hv e he).1)
        (fun e he => (hv e he).2) b u hu hu8
  · have hempty : {h : V → ℝ | ∀ e ∈ F, h ∈ safeEvent V b u e} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro h hh
      exact hv (fun e he => ⟨(hh e he).1,(hh e he).2.1,(hh e he).2.2.1⟩)
    rw [hempty,measureReal_empty]
    exact pow_nonneg (Real.rpow_nonneg (mul_nonneg (ExtremalEdges.gradientConstant_pos 6).le hu.le) _) _

end SparseBlocks

end
end
end
end
end
end
end

end OAI
