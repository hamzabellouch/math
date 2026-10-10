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

end SparseBlocks

namespace SparseBlocks

attribute [local instance] Classical.propDecidable

local instance (sort : Sort*) : DecidableEq sort := Classical.typeDecidableEq sort

lemma q_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ q u :=
  Real.rpow_nonneg (mul_nonneg (ExtremalEdges.gradientConstant_pos 6).le hu) _

lemma q_pos {u : ℝ} (hu : 0 < u) : 0 < q u :=
  Real.rpow_pos_of_pos (mul_pos (ExtremalEdges.gradientConstant_pos 6) hu) _

abbrev ShortChoice (L : ℕ) (z : Vertex) := ↥(sites L z) × ↥(sites L z)

def shortEdges {L : ℕ} {z : Vertex} (t : ShortChoice L z) : Finset (Vertex × Vertex) :=
  {(t.1.val,t.2.val)}

abbrev FarChoice (L : ℕ) (z : Vertex) (k : ℕ) :=
  Σ xy : TriangularLipschitz.BoxVertex (3*L) × TriangularLipschitz.BoxVertex (3*L),
    ↥(SparseWitness.pathSubsets k (pathEdges L z xy))

def farEdges {L : ℕ} {z : Vertex} {k : ℕ} (t : FarChoice L z k) : Finset (Vertex × Vertex) := t.2.val

def tieEdges (p : Parameters) (z : Vertex) (i : Fin 4) : Finset (Vertex × Vertex) :=
  {(neighbor p z i,face p z i)}

def shortTest (V : Finset Vertex) (p : Parameters) (z : Vertex) : Set (V → ℝ) :=
  {h | ∃ t : ShortChoice p.L z, ∀ e ∈ shortEdges t, h ∈ safeEvent V true p.δ e}

def farTest (V : Finset Vertex) (p : Parameters) (z : Vertex) : Set (V → ℝ) :=
  {h | ∃ t : FarChoice p.L z p.k₀, ∀ e ∈ farEdges t, h ∈ safeEvent V true (2*p.δ₀) e}

def tieTest (V : Finset Vertex) (p : Parameters) (z : Vertex) : Set (V → ℝ) :=
  {h | ∃ i : Fin 4, ∀ e ∈ tieEdges p z i, h ∈ safeEvent V false p.s₀ e}

def witnessTest (V : Finset Vertex) (p : Parameters) : Fin 3 → Vertex → Set (V → ℝ) :=
  ![shortTest V p,farTest V p,tieTest V p]

lemma bad_witness (V : Finset Vertex) (p : Parameters) (h : V → ℝ)
    (hh : h ∈ body V) (z : Vertex) (hz : bad p V h z) :
    ∃ j : Fin 3, h ∈ witnessTest V p j z := by
  rcases hz with ⟨hfree,hnear | hfar | htie⟩
  · obtain ⟨x,hx,y,hy,hxy,hcap⟩ := hnear
    refine ⟨0, (⟨⟨x,block_subset_sites p z hx⟩,⟨y,block_subset_sites p z hy⟩⟩ : ShortChoice p.L z),?_⟩
    intro e he
    have heq := Finset.mem_singleton.mp he
    subst e
    exact ⟨hxy,hfree ((mem_enlarged p z x).mpr (block_subset_sites p z hx)),
      hfree ((mem_enlarged p z y).mpr (block_subset_sites p z hy)),hcap.le⟩
  · obtain ⟨x,hx,y,hy,hk,hbad⟩ := hfar
    obtain ⟨xx,hxx⟩ := translate_surj p.L z x ((mem_enlarged p z x).mp hx)
    obtain ⟨yy,hyy⟩ := translate_surj p.L z y ((mem_enlarged p z y).mp hy)
    let F := pathEdges p.L z (xx,yy)
    let S := F.filter (fun e => 1-2*p.δ₀ ≤ |height V h e.1-height V h e.2|)
    have hε : 0 < 2*p.δ₀ := mul_pos (by norm_num) (p.δpos.trans_le p.δle)
    have hsum : (1-(2*p.δ₀)/2)*(F.card : ℝ) <
        ∑ e ∈ F, |height V h e.1-height V h e.2| := by
      rw [show (F.card : ℝ) = latticeDist x y by
        simpa only [F,hxx,hyy] using pathEdges_card p.L z (xx,yy)]
      calc
        _ = (1-p.δ₀)*latticeDist x y := by ring
        _ < |height V h x-height V h y| := hbad
        _ ≤ _ := by simpa only [F,hxx,hyy] using pathEdges_sum p.L z (xx,yy) (height V h)
    have hcount := SparsePaths.cap_count F (fun e => |height V h e.1-height V h e.2|)
      (2*p.δ₀) hε (fun e he => hh _ _ (pathEdges_mem _ _ _ e he).2.2) hsum
    have hS : S ∈ SparseWitness.pathSubsets p.k₀ F := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _),?_,?_⟩
      · have hh : (F.card : ℝ) ≤ 2*(S.card : ℝ) := by dsimp [S]; linarith
        exact_mod_cast hh
      · have hdist := pathEdges_card p.L z (xx,yy)
        rw [hxx,hyy] at hdist
        exact_mod_cast (hk.trans_eq hdist.symm)
    refine ⟨1, ⟨(xx,yy),⟨S,hS⟩⟩,?_⟩
    intro e he
    have he' : e ∈ S := he
    obtain ⟨heF,hecap⟩ := Finset.mem_filter.mp he'
    obtain ⟨he1,he2,heAdj⟩ := pathEdges_mem p.L z (xx,yy) e heF
    exact ⟨heAdj,hfree ((mem_enlarged p z e.1).mpr he1),
      hfree ((mem_enlarged p z e.2).mpr he2),hecap⟩
  · obtain ⟨i,hi⟩ := htie
    obtain ⟨hface,hneighbor,hadj⟩ := face_neighbor_sites p z i
    refine ⟨2,i,?_⟩
    intro e he
    have heq := Finset.mem_singleton.mp he
    subst e
    exact ⟨hadj,hfree ((mem_enlarged p z _).mpr hneighbor),
      hfree ((mem_enlarged p z _).mpr hface),hi.le⟩

lemma witness_family {I : Type*} [Fintype I] (V : Finset Vertex) (L : ℕ)
    (z : I → Vertex) (hz : ∀ i j, i ≠ j → Disjoint (sites L (z i)) (sites L (z j)))
    (b : Bool) (u : ℝ) (hu : 0 < u) (hu8 : u ≤ 1/8)
    {T : I → Type*} [∀ i, Fintype (T i)] (E : ∀ i, T i → Finset (Vertex × Vertex))
    (inside : ∀ i t e, e ∈ E i t → e.1 ∈ sites L (z i))
    (a : ℝ) (entropy : ∀ i, (∑ t, (q u)^(E i t).card) ≤ a) :
    (law V).real {h | ∀ i, ∃ t, ∀ e ∈ E i t, h ∈ safeEvent V b u e} ≤
      a^Fintype.card I := by
  have hbound := SparseWitness.joint_witness_bound (law V) (safeEvent V b u) E (q u)
    (q_nonneg hu.le) (joint_safe_gradients V b u hu hu8) (by
      intro i j hij s t
      apply Finset.disjoint_left.mpr
      intro e hei hej
      exact Finset.disjoint_left.mp (hz i j hij) (inside i s e hei) (inside j t e hej))
  calc
    _ ≤ ∏ i, ∑ t, (q u)^(E i t).card := hbound
    _ ≤ ∏ _i : I, a := Finset.prod_le_prod₀
      (fun i _ => Finset.sum_nonneg (fun t _ => pow_nonneg (q_nonneg hu.le) _))
      (fun i _ => entropy i)
    _ = _ := by simp

lemma short_entropy (L : ℕ) (z : Vertex) (u : ℝ) :
    (∑ t : ShortChoice L z, (q u)^(shortEdges t).card) = ((3*L+1:ℕ):ℝ)^4 * q u := by
  simp only [shortEdges,Finset.card_singleton,pow_one,Finset.sum_const,Finset.card_univ,
    Fintype.card_prod,Fintype.card_coe,card_sites,nsmul_eq_mul]
  push_cast
  ring

lemma far_entropy (L : ℕ) (z : Vertex) (k : ℕ) (u : ℝ) (hu : 0 ≤ u)
    (hsmall : q u ≤ 1/16) :
    (∑ t : FarChoice L z k, (q u)^(farEdges t).card) ≤
      ((3*L+1:ℕ):ℝ)^4 * (1/2:ℝ)^k := by
  rw [Fintype.sum_sigma]
  calc
    _ ≤ ∑ _xy : TriangularLipschitz.BoxVertex (3*L) × TriangularLipschitz.BoxVertex (3*L),
        (1/2:ℝ)^k := by
      apply Finset.sum_le_sum
      intro xy _
      change (∑ y : ↥(SparseWitness.pathSubsets k (pathEdges L z xy)), (q u)^y.val.card) ≤ _
      rw [Finset.sum_coe_sort (SparseWitness.pathSubsets k (pathEdges L z xy))
        (fun S : Finset (Vertex × Vertex) => (q u)^S.card)]
      exact SparseWitness.path_entropy k (pathEdges L z xy) (q u) (q_nonneg hu) hsmall
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,box_card,nsmul_eq_mul]
      push_cast
      ring

end SparseBlocks

end
end
end
end
end
end
end

end OAI
