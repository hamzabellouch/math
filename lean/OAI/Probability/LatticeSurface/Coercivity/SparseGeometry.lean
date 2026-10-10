import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.SparseAmbient
import OAI.Probability.LatticeSurface.Coercivity.SparseColor
import OAI.Probability.LatticeSurface.Coercivity.SparseGradients
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

end SparseBlocks

namespace SparseBlocks

attribute [local instance] Classical.propDecidable

local instance (sort : Sort*) : DecidableEq sort := Classical.typeDecidableEq sort

def sites (L : ℕ) (z : Vertex) : Finset Vertex :=
  Finset.Icc ((L:ℤ)*(z.1-1)) ((L:ℤ)*(z.1+2)) ×ˢ
    Finset.Icc ((L:ℤ)*(z.2-1)) ((L:ℤ)*(z.2+2))

@[simp] lemma mem_sites (L : ℕ) (z x : Vertex) : x ∈ sites L z ↔
    (L:ℤ)*(z.1-1) ≤ x.1 ∧ x.1 ≤ (L:ℤ)*(z.1+2) ∧
    (L:ℤ)*(z.2-1) ≤ x.2 ∧ x.2 ≤ (L:ℤ)*(z.2+2) := by
  simp only [sites,Finset.mem_product,Finset.mem_Icc]
  tauto

lemma mem_enlarged (p : Parameters) (z x : Vertex) :
    x ∈ enlarged p z ↔ x ∈ sites p.L z := (mem_sites p.L z x).symm

def origin (L : ℕ) (z : Vertex) : Vertex := ((L:ℤ)*(z.1-1),(L:ℤ)*(z.2-1))

def translate (L : ℕ) (z : Vertex) (x : TriangularLipschitz.BoxVertex (3*L)) : Vertex :=
  x.val + origin L z

lemma translate_injective (L : ℕ) (z : Vertex) : Function.Injective (translate L z) := by
  intro x y hxy
  exact Subtype.ext (add_right_cancel hxy)

lemma translate_mem (L : ℕ) (z : Vertex) (x : TriangularLipschitz.BoxVertex (3*L)) :
    translate L z x ∈ sites L z := by
  have hx := TriangularLipschitz.mem_box.mp x.property
  simp only [translate,origin,mem_sites,Prod.add_def]
  push_cast at hx
  simp only [mul_sub,mul_add,mul_one,mul_two]
  constructor <;> omega

lemma translate_surj (L : ℕ) (z : Vertex) (x : Vertex) (hx : x ∈ sites L z) :
    ∃ y, translate L z y = x := by
  have hx' := (mem_sites L z x).mp hx
  let y : TriangularLipschitz.BoxVertex (3*L) := ⟨x-origin L z,by
    simp only [TriangularLipschitz.mem_box,origin,Prod.sub_def]
    push_cast
    simp only [mul_sub,mul_add,mul_one,mul_two] at hx' ⊢
    constructor <;> constructor <;> omega⟩
  refine ⟨y,?_⟩
  simp [translate,y]

lemma translate_adj (L : ℕ) (z : Vertex) (x y : TriangularLipschitz.BoxVertex (3*L)) :
    Adj (translate L z x) (translate L z y) ↔ TriangularLipschitz.Adj x.val y.val := by
  have hh := adj_sub (translate L z x) (translate L z y) (origin L z)
  simpa only [Adj,TriangularLipschitz.Adj] using (show Adj (translate L z x) (translate L z y) ↔ Adj x.val y.val from by simpa only [translate,add_sub_cancel_right] using hh.symm)

lemma translate_dist (L : ℕ) (z : Vertex) (x y : TriangularLipschitz.BoxVertex (3*L)) :
    latticeDist (translate L z x) (translate L z y) =
      TriangularLipschitz.latticeDist x.val y.val := by
  simp only [latticeDist,TriangularLipschitz.latticeDist,translate,Prod.add_def,
    Int.cast_add,add_sub_add_right_eq_sub]

lemma card_sites (L : ℕ) (z : Vertex) : (sites L z).card = (3*L+1)^2 := by
  simp only [sites,Finset.card_product,Int.card_Icc]
  have hh (a : ℤ) : ((L:ℤ)*(a+2)+1-(L:ℤ)*(a-1)).toNat = 3*L+1 := by
    have he : (L:ℤ)*(a+2)+1-(L:ℤ)*(a-1) = (3*L+1 : ℕ) := by push_cast;ring
    rw [he,Int.toNat_natCast]
  rw [hh,hh,pow_two]

lemma sites_disjoint {L : ℕ} (hL : 0 < L) {z w : Vertex}
    (hzw : 3 < |z.1-w.1| ∨ 3 < |z.2-w.2|) : Disjoint (sites L z) (sites L w) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hx' := (mem_sites L z x).mp hx
  have hy' := (mem_sites L w x).mp hy
  have hL' : (0:ℤ) < L := by exact_mod_cast hL
  rcases hzw with h | h
  all_goals simp only [abs_eq_max_neg] at h
  · have hh : z.1-w.1 > 3 ∨ w.1-z.1 > 3 := by omega
    rcases hh with hh | hh
    · have := mul_lt_mul_of_pos_left (show w.1+2 < z.1-1 by omega) hL'
      omega
    · have := mul_lt_mul_of_pos_left (show z.1+2 < w.1-1 by omega) hL'
      omega
  · have hh : z.2-w.2 > 3 ∨ w.2-z.2 > 3 := by omega
    rcases hh with hh | hh
    · have := mul_lt_mul_of_pos_left (show w.2+2 < z.2-1 by omega) hL'
      omega
    · have := mul_lt_mul_of_pos_left (show z.2+2 < w.2-1 by omega) hL'
      omega

lemma L_pos (p : Parameters) : 0 < p.L := by
  have hδ : 0 < p.δ₀ := p.δpos.trans_le p.δle
  have hk : (0:ℝ) < (p.k₀:ℝ)+2 := by positivity
  have hh := (div_pos (mul_pos (by norm_num) hk) hδ).trans_le p.Llarge
  exact_mod_cast hh

lemma block_subset_sites (p : Parameters) (z : Vertex) : block p z ⊆ (sites p.L z : Set Vertex) := by
  intro x hx
  have hL : (0:ℤ) ≤ p.L := Int.natCast_nonneg _
  change _ ∧ _ ∧ _ ∧ _ at hx
  apply (mem_sites p.L z x).mpr
  have h1 := mul_le_mul_of_nonneg_left (show z.1-1 ≤ z.1 by omega) hL
  have h2 := mul_le_mul_of_nonneg_left (show z.1+1 ≤ z.1+2 by omega) hL
  have h3 := mul_le_mul_of_nonneg_left (show z.2-1 ≤ z.2 by omega) hL
  have h4 := mul_le_mul_of_nonneg_left (show z.2+1 ≤ z.2+2 by omega) hL
  omega

lemma face_neighbor_sites (p : Parameters) (z : Vertex) (i : Fin 4) :
    face p z i ∈ sites p.L z ∧ neighbor p z i ∈ sites p.L z ∧
      Adj (neighbor p z i) (face p z i) := by
  have hL : (0:ℤ) < p.L := by exact_mod_cast L_pos p
  have hhalf : (0:ℤ) ≤ (p.L:ℤ)/2 ∧ (p.L:ℤ)/2 ≤ p.L := by omega
  fin_cases i <;>
    norm_num [face,neighbor,mem_sites,Adj,Prod.mk.injEq,Fin.ext_iff,mul_add,mul_sub,mul_one,mul_two] <;>
    omega

end SparseBlocks

end
end
end
end

end OAI
