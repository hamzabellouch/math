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
attribute [local instance_reducible, local instance] Classical.typeDecidableEq

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable
attribute [local instance_reducible, local instance] Classical.typeDecidableEq

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
attribute [local instance_reducible, local instance] Classical.typeDecidableEq

end SparseBlocks

noncomputable section

open scoped BigOperators

namespace SparsePaths

attribute [local instance] Classical.propDecidable
attribute [local instance_reducible, local instance] Classical.typeDecidableEq

end SparsePaths

noncomputable section

open scoped BigOperators

namespace SparseWitness

attribute [local instance] Classical.propDecidable
attribute [local instance_reducible, local instance] Classical.typeDecidableEq

end SparseWitness

noncomputable section

open Set MeasureTheory

open scoped BigOperators

namespace SparseWitness

attribute [local instance] Classical.propDecidable
attribute [local instance_reducible, local instance] Classical.typeDecidableEq

end SparseWitness

namespace SparseBlocks

attribute [local instance] Classical.propDecidable
attribute [local instance_reducible, local instance] Classical.typeDecidableEq

end SparseBlocks

namespace SparseBlocks

attribute [local instance] Classical.propDecidable
attribute [local instance_reducible, local instance] Classical.typeDecidableEq

end SparseBlocks

namespace SparseBlocks

open Filter

open scoped Topology

end SparseBlocks

namespace SparseBlocks

attribute [local instance] Classical.propDecidable
attribute [local instance_reducible, local instance] Classical.typeDecidableEq

end SparseBlocks

namespace SparseBlocks

attribute [local instance] Classical.propDecidable
attribute [local instance_reducible, local instance] Classical.typeDecidableEq

end SparseBlocks

namespace SparseBlocks

attribute [local instance] Classical.propDecidable
attribute [local instance_reducible, local instance] Classical.typeDecidableEq

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

noncomputable def ordinary (p : SparseBlocks.Parameters) (V : Finset Vertex) : Finset Vertex :=
  (V.image (fun x => (x.1/(p.L:ℤ),x.2/(p.L:ℤ)))).filter (fun z => SparseBlocks.enlarged p z ⊆ (V:Set Vertex))

end RetainedShell

namespace TriangularLipschitz

lemma global_lipschitz (h : Vertex → ℝ) (he : ∀ x y,Adj x y → |h x-h y|≤1)
    (x y : Vertex) : |h x-h y|≤latticeDist x y := by
  suffices ∀ n x y,(intDist x y).toNat=n → |h x-h y|≤latticeDist x y from this _ x y rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x y hn
    by_cases hxy : x=y
    · subst y;simp [latticeDist]
    obtain ⟨z,hxz,hz1,hz2,hd⟩ := geodesic_step hxy
    have hlt : (intDist z y).toNat<n := by
      have := intDist_nonneg z y
      have := intDist_nonneg x y
      omega
    have hz := ih _ hlt z y rfl
    have hr : latticeDist z y+1=latticeDist x y := by
      simp only [← intDist_cast]
      exact_mod_cast hd
    calc
      |h x-h y|≤|h x-h z|+|h z-h y| := abs_sub_le _ _ _
      _ ≤ 1+latticeDist z y := add_le_add (he x z hxz) hz
      _ = latticeDist x y := by linarith

lemma latticeDist_add_left (a x y : Vertex) : latticeDist (a+x) (a+y)=latticeDist x y := by
  simp only [latticeDist,Prod.fst_add,Prod.snd_add,Int.cast_add]
  congr 2 <;> ring_nf

end TriangularLipschitz

namespace RetainedShell

open TriangularLipschitz

attribute [local instance] Classical.propDecidable

lemma base_enlarged (p : SparseBlocks.Parameters) (z : Vertex) : base p.L z∈SparseBlocks.enlarged p z := by
  have hL : (0:ℤ)≤p.L := Int.natCast_nonneg _
  simp only [SparseBlocks.enlarged,Set.mem_ofPred_eq,base]
  refine ⟨?_,?_,?_,?_⟩ <;> nlinarith

lemma mem_ordinary (p : SparseBlocks.Parameters) (V : Finset Vertex) (z : Vertex) :
    z∈ordinary p V ↔ SparseBlocks.enlarged p z⊆(V:Set Vertex) := by
  classical
  constructor
  · intro hz;exact (Finset.mem_filter.mp hz).2
  · intro hz
    have hL : (p.L:ℤ)≠0 := by exact_mod_cast (SparseBlocks.L_pos p).ne'
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨base p.L z,hz (base_enlarged p z),?_⟩,hz⟩
    simp [base,Int.mul_ediv_cancel_left _ hL]

lemma block_enlarged (p : SparseBlocks.Parameters) (z : Vertex) {x : Vertex} (hx : x∈box p.L) :
    base p.L z+x∈SparseBlocks.enlarged p z := by
  have hL : (0:ℤ)≤p.L := Int.natCast_nonneg _
  have hx := mem_box.mp hx
  simp only [SparseBlocks.enlarged,Set.mem_ofPred_eq,base,Prod.fst_add,Prod.snd_add]
  refine ⟨?_,?_,?_,?_⟩ <;> nlinarith

lemma block_translate (p : SparseBlocks.Parameters) (z : Vertex) {x : Vertex} (hx : x∈box p.L) :
    base p.L z+x∈SparseBlocks.block p z := by
  have hx := mem_box.mp hx
  simp only [SparseBlocks.block,Set.mem_ofPred_eq,base,Prod.fst_add,Prod.snd_add]
  refine ⟨?_,?_,?_,?_⟩ <;> nlinarith

lemma ordinary_free (p : SparseBlocks.Parameters) (V : Finset Vertex) :
    ∀ z∈ordinary p V,∀ x∈box p.L,base p.L z+x∈V := by
  intro z hz x hx
  exact (mem_ordinary p V z).mp hz (block_enlarged p z hx)

lemma face_source (p : SparseBlocks.Parameters) (z : Vertex) (i : Fin 4) :
    base p.L z+faceCenter p.L i=SparseBlocks.face p z i := by
  fin_cases i <;> simp [base,faceCenter,SparseBlocks.face,Int.natCast_ediv]

lemma neighbor_source (p : SparseBlocks.Parameters) (z : Vertex) (i : Fin 4) :
    base p.L z+compressedNeighbor p.L i=SparseBlocks.neighbor p z i := by
  fin_cases i <;> simp [base,compressedNeighbor,SparseBlocks.neighbor,SparseBlocks.face,Int.natCast_ediv] <;> ring

lemma face_in_box (L : ℕ) (i : Fin 4) : faceCenter L i∈box L := by
  have he : L/2≤L := Nat.div_le_self _ _
  fin_cases i <;> simp [faceCenter,mem_box] <;> omega

end RetainedShell

namespace RetainedShell

open TriangularLipschitz

theorem pin_block_faces (p : SparseBlocks.Parameters) (V : Finset Vertex) (χ : Vertex → ℝ)
    (hlip : ∀ x y,Adj x y → |χ x-χ y|≤1)
    (hzero : ∀ x,x∉V → χ x=0) (z : Vertex) (hz : z∉ordinary p V) :
    ∀ i : Fin 4,|χ (base p.L z+faceCenter p.L i)|≤4*(p.L:ℝ) := by
  classical
  have hn : ¬ SparseBlocks.enlarged p z⊆(V:Set Vertex) := by
    exact fun h => hz ((mem_ordinary p V z).mpr h)
  obtain ⟨x,hxe,hxV⟩ := Set.not_subset.mp hn
  intro i
  have hd := global_lipschitz χ hlip (base p.L z+faceCenter p.L i) x
  rw [hzero x hxV,sub_zero] at hd
  apply hd.trans
  have hfb := mem_box.mp (face_in_box p.L i)
  have hxe : (p.L:ℤ)*(z.1-1)≤x.1 ∧ x.1≤(p.L:ℤ)*(z.1+2) ∧
      (p.L:ℤ)*(z.2-1)≤x.2 ∧ x.2≤(p.L:ℤ)*(z.2+2) := hxe
  have h1 : |((base p.L z+faceCenter p.L i).1:ℝ)-x.1|≤2*(p.L:ℝ) := by
    have hh : |(base p.L z+faceCenter p.L i).1-x.1|≤2*(p.L:ℤ) := by
      simp only [Prod.fst_add,base]
      rw [abs_le]
      constructor <;> nlinarith [hfb.1.1,hfb.1.2,hxe.1,hxe.2.1]
    exact_mod_cast hh
  have h2 : |((base p.L z+faceCenter p.L i).2:ℝ)-x.2|≤2*(p.L:ℝ) := by
    have hh : |(base p.L z+faceCenter p.L i).2-x.2|≤2*(p.L:ℤ) := by
      simp only [Prod.snd_add,base]
      rw [abs_le]
      constructor <;> nlinarith [hfb.2.1,hfb.2.2,hxe.2.2.1,hxe.2.2.2]
    exact_mod_cast hh
  apply max_le
  · exact max_le (by linarith) (by linarith)
  · exact (abs_add_le _ _).trans (by linarith)

theorem ordinary_good (p : SparseBlocks.Parameters) (V : Finset Vertex) (h : V → ℝ)
    (z : Vertex) (hz : z∈ordinary p V) (hb : ¬ SparseBlocks.bad p V h z) :
    ConvexGood p.L p.k₀ p.δ p.δ₀ p.s₀ (fun x => SparseBlocks.height V h (base p.L z+x)) := by
  have hf := (mem_ordinary p V z).mp hz
  refine ⟨?_,?_,?_⟩
  · intro x hx y hy hxy
    apply le_of_not_gt
    intro he
    apply hb
    exact ⟨hf,Or.inl ⟨base p.L z+x,block_translate p z hx,
      base p.L z+y,block_translate p z hy,(adj_translate p.L z x y).mpr hxy,he⟩⟩
  · intro x hx y hy hdist
    apply le_of_not_gt
    intro he
    apply hb
    refine ⟨hf,Or.inr (Or.inl ⟨base p.L z+x,block_enlarged p z hx,
      base p.L z+y,block_enlarged p z hy,?_,?_⟩)⟩
    · change (p.k₀:ℝ)≤TriangularLipschitz.latticeDist (base p.L z+x) (base p.L z+y)
      rwa [latticeDist_add_left]
    · change (1-p.δ₀)*TriangularLipschitz.latticeDist (base p.L z+x) (base p.L z+y)<_
      rwa [latticeDist_add_left]
  · intro i
    change p.s₀≤|SparseBlocks.height V h (base p.L z+compressedNeighbor p.L i)-
      SparseBlocks.height V h (base p.L z+faceCenter p.L i)|
    rw [face_source,neighbor_source]
    apply le_of_not_gt
    intro he
    exact hb ⟨hf,Or.inr (Or.inr ⟨i,he⟩)⟩

end RetainedShell

end
end
end
end
end
end
end

end OAI
