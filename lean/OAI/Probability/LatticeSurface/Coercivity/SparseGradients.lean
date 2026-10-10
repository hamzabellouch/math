import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.SparseAmbient
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

lemma volume_body_positive (V : Finset Vertex) : 0 < volume (body V) := by
  obtain ⟨B,hVB,hcollar,hc,hp⟩ := exists_ambient V
  rw [← volume_body_coordinates B V hVB hcollar]
  exact ExtremalEdges.volume_zeroBody_pos _ _

lemma volume_body_finite (V : Finset Vertex) : volume (body V) ≠ ⊤ := by
  obtain ⟨B,hVB,hcollar,hc,hp⟩ := exists_ambient V
  rw [← volume_body_coordinates B V hVB hcollar]
  exact (ExtremalEdges.compact_zeroBody _ hc _ hp).measure_ne_top

def law (V : Finset Vertex) : Measure (V → ℝ) :=
  (volume (body V))⁻¹ • volume.restrict (body V)

instance law_probability (V : Finset Vertex) : IsProbabilityMeasure (law V) := by
  constructor
  simp only [law, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ne_of_gt (volume_body_positive V)) (volume_body_finite V)

lemma law_real (V : Finset Vertex) (S : Set (V → ℝ)) (hS : MeasurableSet S) :
    (law V).real S = (volume (body V ∩ S)).toReal / (volume (body V)).toReal := by
  simp only [Measure.real,law,Measure.smul_apply,Measure.restrict_apply hS,
    smul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_inv]
  rw [Set.inter_comm,div_eq_mul_inv,mul_comm]

def window (b : Bool) (u t : ℝ) : Prop := if b then 1-u ≤ |t| else |t| ≤ u

def edgeEvent (V : Finset Vertex) (b : Bool) (u : ℝ) (e : Vertex × Vertex) : Set (V → ℝ) :=
  {h | window b u (height V h e.1-height V h e.2)}

def gradientEvent (V : Finset Vertex) (b : Bool) (u : ℝ)
    (F : Finset (Vertex × Vertex)) : Set (V → ℝ) :=
  {h | ∀ e ∈ F, h ∈ edgeEvent V b u e}

lemma closed_edgeEvent (V : Finset Vertex) (b : Bool) (u : ℝ) (e : Vertex × Vertex) :
    IsClosed (edgeEvent V b u e) := by
  cases b
  · exact isClosed_le ((continuous_height V e.1).sub (continuous_height V e.2)).abs continuous_const
  · exact isClosed_le continuous_const ((continuous_height V e.1).sub (continuous_height V e.2)).abs

lemma closed_gradientEvent (V : Finset Vertex) (b : Bool) (u : ℝ) (F : Finset (Vertex × Vertex)) :
    IsClosed (gradientEvent V b u F) := by
  simp only [gradientEvent,Set.ofPred_forall]
  exact isClosed_iInter fun e => isClosed_iInter fun _ => closed_edgeEvent V b u e

theorem joint_gradients (V : Finset Vertex) (F : Finset (Vertex × Vertex))
    (he : ∀ e ∈ F, Adj e.1 e.2) (hf : ∀ e ∈ F, e.1 ∈ V ∧ e.2 ∈ V)
    (b : Bool) (u : ℝ) (hu : 0 < u) (hu8 : u ≤ 1/8) :
    (law V).real (gradientEvent V b u F) ≤
      ((ExtremalEdges.gradientConstant 6*u)^(1/ExtremalEdges.gradientConstant 6))^F.card := by
  classical
  obtain ⟨B,hVB,hcollar,hc,hp⟩ := exists_ambient V
  let ee : Fin F.card → F := (Finset.equivFin F).symm
  let e : Fin F.card → B × B := fun i =>
    (⟨(ee i).val.1,hVB (hf _ (ee i).property).1⟩,⟨(ee i).val.2,hVB (hf _ (ee i).property).2⟩)
  have hei : Function.Injective e := by
    intro i j hij
    have hh : ee i = ee j := Subtype.ext (Prod.ext
      (congrArg (fun p : B × B => p.1.val) hij) (congrArg (fun p : B × B => p.2.val) hij))
    exact (Finset.equivFin F).symm.injective hh
  have heG : ∀ i, (finiteGraph B).Adj (e i).1 (e i).2 := fun i => he _ (ee i).property
  have hfree : ∀ i, ¬ ((e i).1 ∈ fixed B V ∧ (e i).2 ∈ fixed B V) := by
    intro i hh
    exact hh.1 (hf _ (ee i).property).1
  let S : Set (ExtremalEdges.Free (fixed B V) → ℝ) :=
    {h | ∀ i, window b u (ExtremalEdges.height (fixed B V) h (e i).1-
      ExtremalEdges.height (fixed B V) h (e i).2)}
  have hS : IsClosed S := by
    simp only [S,Set.ofPred_forall]
    apply isClosed_iInter
    intro i
    have hh := ((ExtremalEdges.continuous_restore (fixed B V) (fun _ => 0) (e i).1).sub
      (ExtremalEdges.continuous_restore (fixed B V) (fun _ => 0) (e i).2)).abs
    cases b
    · exact isClosed_le hh continuous_const
    · exact isClosed_le continuous_const hh
  have hpre : (coordinates B V hVB) ⁻¹' S = gradientEvent V b u F := by
    ext h
    simp only [Set.mem_preimage, S, Set.mem_ofPred_eq, coordinates_height, gradientEvent, edgeEvent]
    constructor
    · intro hh z hz
      have hh' := hh ((Finset.equivFin F) ⟨z,hz⟩)
      simpa only [e,ee,Equiv.symm_apply_apply] using hh'
    · intro hh i
      exact hh _ (ee i).property
  have hvol : volume (ExtremalEdges.body (finiteGraph B) (fixed B V) ∩ S) =
      volume (body V ∩ gradientEvent V b u F) := by
    rw [← body_coordinates B V hVB hcollar, ← hpre, ← Set.preimage_inter]
    exact ((preserving_coordinates B V hVB).measure_preimage
      ((ExtremalEdges.closed_conditionalBody (finiteGraph B) (fixed B V) (fun _ => 0)).inter hS).measurableSet.nullMeasurableSet).symm
  have hb : (volume (ExtremalEdges.body (finiteGraph B) (fixed B V) ∩ S)).toReal /
      (volume (ExtremalEdges.body (finiteGraph B) (fixed B V))).toReal ≤
      (ExtremalEdges.gradientConstant 6*u)^((F.card:ℝ)/ExtremalEdges.gradientConstant 6) := by
    cases b
    · exact ExtremalEdges.near_zero_gradients_ordered 6 (finiteGraph B) hc (finiteGraph_degree B)
        (fixed B V) hp F.card e heG hei hfree u hu
    · exact ExtremalEdges.controlled_gradients_ordered 6 (finiteGraph B) hc (finiteGraph_degree B)
        (fixed B V) hp F.card e heG hei u hu hu8
  rw [hvol,volume_body_coordinates B V hVB hcollar,← law_real V _ (closed_gradientEvent V b u F).measurableSet] at hb
  convert hb using 1
  rw [← Real.rpow_mul_natCast (mul_pos (ExtremalEdges.gradientConstant_pos 6) hu).le]
  congr 1
  ring

end SparseBlocks

end
end
end
end

end OAI
