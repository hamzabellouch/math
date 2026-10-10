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

def base (L : ℕ) (z : Vertex) : Vertex := ((L:ℤ)*z.1,(L:ℤ)*z.2)

def bulk (L : ℕ) (J : Finset Vertex) : Finset Vertex :=
  J.biUnion (fun z => (interior L).image (fun x => base L z+x))

def retained (L : ℕ) (V J : Finset Vertex) : Finset Vertex := V \ bulk L J

def retainedHeight (L : ℕ) (V J : Finset Vertex) (s : retained L V J → ℝ) (x : Vertex) : ℝ :=
  if hx : x∈retained L V J then s ⟨x,hx⟩ else 0

def patch (L : ℕ) (a : Filling L) (x : Vertex) : ℝ :=
  if hx : x∈interior L then a ⟨x,hx⟩ else 0

def assembled (L : ℕ) (V J : Finset Vertex) (s : retained L V J → ℝ)
    (a : J → Filling L) (x : Vertex) : ℝ :=
  retainedHeight L V J s x+∑ z:J,patch L (a z) (x-base L z)

def shellData (L : ℕ) (V J : Finset Vertex) (s : retained L V J → ℝ) (z : Vertex) : Vertex → ℝ :=
  fun x => retainedHeight L V J s (base L z+x)

def remaining (L : ℕ) (V J : Finset Vertex) : Set (retained L V J → ℝ) :=
  {s | ∀ x y,x∉bulk L J → y∉bulk L J → Adj x y →
    |retainedHeight L V J s x-retainedHeight L V J s y|≤1}

def fiber (L : ℕ) (V J : Finset Vertex) (s : retained L V J → ℝ) : Set (J → Filling L) :=
  {a | ∀ x y,Adj x y → |assembled L V J s a x-assembled L V J s a y|≤1}

def shellDensity (L : ℕ) (V J : Finset Vertex) (s : retained L V J → ℝ) : ENNReal := volume (fiber L V J s)

end RetainedShell

namespace RetainedShell

open TriangularLipschitz

attribute [local instance] Classical.propDecidable

lemma mem_bulk {L : ℕ} {J : Finset Vertex} {x : Vertex} :
    x∈bulk L J ↔ ∃ z∈J,x-base L z∈interior L := by
  simp only [bulk,Finset.mem_biUnion,Finset.mem_image]
  constructor
  · rintro ⟨z,hz,y,hy,rfl⟩
    exact ⟨z,hz,by simpa using hy⟩
  · rintro ⟨z,hz,hx⟩
    exact ⟨z,hz,x-base L z,hx,by simp⟩

lemma grid_coordinate_unique {n x z w : ℤ} (hn : 0<n)
    (hz : 1≤x-n*z ∧ x-n*z≤n-1) (hw : 0≤x-n*w ∧ x-n*w≤n) : z=w := by
  rcases lt_trichotomy z w with h|h|h
  · have hh := mul_le_mul_of_nonneg_left (show z+1≤w by omega) hn.le
    nlinarith
  · exact h
  · have hh := mul_le_mul_of_nonneg_left (show w+1≤z by omega) hn.le
    nlinarith

lemma block_unique {L : ℕ} (hL : 0<L) {x z w : Vertex}
    (hz : x-base L z∈interior L) (hw : x-base L w∈box L) : z=w := by
  simp only [TriangularLipschitz.interior,TriangularLipschitz.box,Finset.mem_product,Finset.mem_Icc,Prod.fst_sub,Prod.snd_sub,base] at hz hw
  exact Prod.ext (grid_coordinate_unique (by exact_mod_cast hL) hz.1 hw.1)
    (grid_coordinate_unique (by exact_mod_cast hL) hz.2 hw.2)

lemma block_shell_not_bulk {L : ℕ} (hL : 0<L) (J : Finset Vertex) (z : Vertex)
    {x : Vertex} (hx : x∈box L) (hn : x∉interior L) : base L z+x∉bulk L J := by
  intro hb
  obtain ⟨w,hw,hwi⟩ := mem_bulk.mp hb
  have he : w=z := block_unique hL hwi (by simpa using hx)
  subst w
  exact hn (by simpa using hwi)

lemma adj_translate (L : ℕ) (z x y : Vertex) : TriangularLipschitz.Adj (base L z+x) (base L z+y) ↔ TriangularLipschitz.Adj x y := by
  rcases x with ⟨x₁,x₂⟩;rcases y with ⟨y₁,y₂⟩
  rcases z with ⟨z₁,z₂⟩
  simp only [TriangularLipschitz.Adj,base,Prod.mk_add_mk,Prod.mk.injEq]
  omega

lemma interior_neighbor {L : ℕ} {x y : Vertex} (hx : x∈interior L) (hxy : TriangularLipschitz.Adj x y) : y∈box L := by
  simp only [TriangularLipschitz.interior,TriangularLipschitz.box,Finset.mem_product,Finset.mem_Icc] at hx ⊢
  rcases x with ⟨x₁,x₂⟩;rcases y with ⟨y₁,y₂⟩
  simp only [TriangularLipschitz.Adj,Prod.mk.injEq] at hxy
  omega

lemma bulk_subset {L : ℕ} {V J : Finset Vertex}
    (hf : ∀ z∈J,∀ x∈box L,base L z+x∈V) : bulk L J⊆V := by
  intro x hx
  obtain ⟨z,hz,hi⟩ := mem_bulk.mp hx
  have hh := hf z hz (x-base L z) (interior_subset_box L hi)
  simpa using hh

lemma patch_zero {L : ℕ} (a : Filling L) {x : Vertex} (hx : x∉interior L) : patch L a x=0 := by
  simp [patch,hx]

lemma assembled_remaining (L : ℕ) (V J : Finset Vertex) (s : retained L V J → ℝ)
    (a : J → Filling L) {x : Vertex} (hx : x∉bulk L J) : assembled L V J s a x=retainedHeight L V J s x := by
  unfold assembled
  have hz : ∀ z:J,patch L (a z) (x-base L z)=0 := by
    intro z;apply patch_zero;intro h;exact hx (mem_bulk.mpr ⟨z,z.2,h⟩)
  simp [hz]

lemma assembled_interior {L : ℕ} (hL : 0<L) (V J : Finset Vertex) (s : retained L V J → ℝ)
    (a : J → Filling L) (z : J) {x : Vertex} (hx : x-base L z∈interior L) :
    assembled L V J s a x=a z ⟨x-base L z,hx⟩ := by
  have hb : x∈bulk L J := mem_bulk.mpr ⟨z,z.2,hx⟩
  have hr : x∉retained L V J := by simp [retained,hb]
  have hsum : (∑ w:J,patch L (a w) (x-base L w))=patch L (a z) (x-base L z) := by
    apply Finset.sum_eq_single z
    · intro w hw hne
      apply patch_zero
      intro hw'
      exact hne (Subtype.ext (block_unique hL hw' (interior_subset_box L hx)))
    · simp
  change retainedHeight L V J s x+(∑ w:J,patch L (a w) (x-base L w))=_
  rw [hsum]
  simp [retainedHeight,hr,patch,hx]

lemma assembled_on_block {L : ℕ} (hL : 0<L) (V J : Finset Vertex) (s : retained L V J → ℝ)
    (a : J → Filling L) (z : J) {x : Vertex} (hx : x∈box L) :
    assembled L V J s a (base L z+x)=filledHeight L (shellData L V J s z) (a z) x := by
  by_cases hi : x∈interior L
  · simpa [filledHeight,hi] using assembled_interior hL V J s a z
      (x:=base L z+x) (by simpa using hi)
  · rw [assembled_remaining L V J s a (block_shell_not_bulk hL J z hx hi)]
    simp [filledHeight,hi,shellData]

lemma assembled_zero_exterior (L : ℕ) (V J : Finset Vertex)
    (hf : ∀ z∈J,∀ x∈box L,base L z+x∈V) (s : retained L V J → ℝ)
    (a : J → Filling L) {x : Vertex} (hx : x∉V) : assembled L V J s a x=0 := by
  have hb : x∉bulk L J := fun h => hx (bulk_subset hf h)
  rw [assembled_remaining L V J s a hb]
  have hr : x∉retained L V J := by simp [retained,hx]
  simp [retainedHeight,hr]

lemma fiber_iff {L : ℕ} (hL : 0<L) (V J : Finset Vertex)
    (s : retained L V J → ℝ) (a : J → Filling L) :
    a∈fiber L V J s ↔ s∈remaining L V J ∧
      ∀ z:J,a z∈fillingPolytope L (shellData L V J s z) := by
  constructor
  · intro ha
    constructor
    · intro x y hx hy hxy
      simpa only [assembled_remaining L V J s a hx,assembled_remaining L V J s a hy] using ha x y hxy
    · intro z x hx y hy hxy
      simpa only [assembled_on_block hL V J s a z hx,assembled_on_block hL V J s a z hy]
        using ha (base L z+x) (base L z+y) ((adj_translate L z x y).mpr hxy)
  · rintro ⟨hs,ha⟩ x y hxy
    have hone (x y : Vertex) (hx : x∈bulk L J) (hxy : TriangularLipschitz.Adj x y) :
        |assembled L V J s a x-assembled L V J s a y|≤1 := by
      obtain ⟨z,hz,hi⟩ := mem_bulk.mp hx
      have hxy' : TriangularLipschitz.Adj (x-base L z) (y-base L z) := by
        apply (adj_translate L z _ _).mp
        simpa only [add_sub_cancel] using hxy
      have hyb := interior_neighbor hi hxy'
      have hh := ha ⟨z,hz⟩ (x-base L z) (interior_subset_box L hi) (y-base L z) hyb hxy'
      rw [← assembled_on_block hL V J s a ⟨z,hz⟩ (interior_subset_box L hi),
        ← assembled_on_block hL V J s a ⟨z,hz⟩ hyb] at hh
      simpa only [add_sub_cancel] using hh
    by_cases hx : x∈bulk L J
    · exact hone x y hx hxy
    · by_cases hy : y∈bulk L J
      · simpa only [abs_sub_comm] using hone y x hy (adj_symm hxy)
      · rw [assembled_remaining L V J s a hx,assembled_remaining L V J s a hy]
        exact hs x y hx hy hxy

end RetainedShell

namespace RetainedShell

open TriangularLipschitz

theorem density_product (L : ℕ) (hL : 0<L) (V J : Finset Vertex)
    (_hfree : ∀ z∈J,∀ x∈box L,base L z+x∈V) (s : retained L V J → ℝ) :
    shellDensity L V J s =
      (remaining L V J).indicator (fun s => ∏ z:J,fillingVolume L (shellData L V J s z)) s := by
  classical
  unfold shellDensity
  by_cases hs : s∈remaining L V J
  · have he : fiber L V J s=Set.pi Set.univ (fun z:J => fillingPolytope L (shellData L V J s z)) := by
      ext a
      simp only [fiber_iff hL V J s a,hs,true_and,Set.mem_pi,Set.mem_univ,true_implies]
    rw [he,volume_pi_pi,Set.indicator_of_mem hs]
    rfl
  · have he : fiber L V J s=∅ := by
      ext a;simp [fiber_iff hL V J s a,hs]
    simp [he,hs]

end RetainedShell

end
end
end
end
end
end
end

end OAI
