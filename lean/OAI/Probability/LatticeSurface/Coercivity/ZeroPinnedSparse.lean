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

local instance zeroPinnedSparseDecidableEq (sort : Sort*) : DecidableEq sort :=
  Classical.typeDecidableEq sort

lemma law_real_all (V : Finset Vertex) (S : Set (V → ℝ)) :
    (law V).real S = (volume (body V ∩ S)).toReal / (volume (body V)).toReal := by
  simp only [Measure.real,law,Measure.smul_apply,
    Measure.restrict_apply' (closed_body V).measurableSet,smul_eq_mul,
    ENNReal.toReal_mul,ENNReal.toReal_inv]
  rw [Set.inter_comm,div_eq_mul_inv,mul_comm]

lemma law_real_of_subset (V : Finset Vertex) (S : Set (V → ℝ)) (hS : S ⊆ body V) :
    (law V).real S = (volume S).toReal / (volume (body V)).toReal := by
  rw [law_real_all,Set.inter_eq_right.mpr hS]

theorem zero_pinned_sparse (ρ : ℝ) (hρ : 0 < ρ) (m : ℕ) :
    ∃ p : Parameters, ∀ (V : Finset Vertex) (A : Finset Vertex),
    (volume {h : V → ℝ | h ∈ body V ∧ ∀ z ∈ A, thickBad p V h m z}).toReal /
       (volume (body V)).toReal ≤ ρ^A.card := by
  let P := 2*m+4
  have hP : 0 < P := by dsimp [P];omega
  let D : ℝ := (offsets m).card
  have hD : 0 < D := by dsimp [D];rw [offsets_card];positivity
  let β := min ρ 1
  have hβ : 0 < β := lt_min hρ (by norm_num)
  have hβ1 : β ≤ 1 := min_le_right _ _
  let θ := β^(P^2)/D
  have hθ : 0 < θ := div_pos (pow_pos hβ _) hD
  obtain ⟨p,hp⟩ := separated_parameters θ hθ
  refine ⟨p,?_⟩
  intro V A
  let f : A → Fin P × Fin P := fun z => color P hP z.val
  obtain ⟨c,hc⟩ := SparseWitness.large_fiber f
  let B : Finset A := Finset.univ.filter (fun i => f i = c)
  have hsize : A.card ≤ P^2*B.card := by
    simp only [Fintype.card_coe,Fintype.card_prod,Fintype.card_fin] at hc
    convert hc using 1; simp [B,pow_two]
    apply congrArg Finset.card
    ext i
    simp
  let z : B → Vertex := fun i => i.val.val
  have hcolor (i j : B) : color P hP (z i) = color P hP (z j) := by
    exact (Finset.mem_filter.mp i.property).2.trans (Finset.mem_filter.mp j.property).2.symm
  have hne (i j : B) (hij : i ≠ j) : z i ≠ z j := by
    intro hh
    exact hij (Subtype.ext (Subtype.ext hh))
  let S : Set (V → ℝ) := {h | h ∈ body V ∧ ∀ zz ∈ A, thickBad p V h m zz}
  let T : (B → offsets m) → Set (V → ℝ) := fun t =>
    {h | h ∈ body V ∧ ∀ i, bad p V h (z i+(t i).val)}
  have hsub : S ⊆ ⋃ t : B → offsets m, T t := by
    intro h hh
    have hw (i : B) : ∃ t : offsets m, bad p V h (z i+t.val) := by
      obtain ⟨w,hw1,hw2,hbad⟩ := hh.2 (z i) i.val.property
      let t : offsets m := ⟨w-z i,(offsets_mem m _).mpr ⟨hw1,hw2⟩⟩
      refine ⟨t,?_⟩
      simpa only [t,add_sub_cancel] using hbad
    choose t ht using hw
    exact Set.mem_iUnion.mpr ⟨t,hh.1,ht⟩
  have hbound (t : B → offsets m) : (law V).real (T t) ≤ θ^B.card := by
    have hdisj (i j : B) (hij : i ≠ j) :
        Disjoint (sites p.L (z i+(t i).val)) (sites p.L (z j+(t j).val)) := by
      apply sites_disjoint (L_pos p)
      exact perturbed_color_distance m (z i) (z j) (hne i j hij) (hcolor i j) (t i) (t j)
    simpa only [Fintype.card_coe] using hp V B (fun i => z i+(t i).val) hdisj
  have hprob : (law V).real S ≤ ρ^A.card := by
    calc
      _ ≤ (law V).real (⋃ t : B → offsets m, T t) := measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ ∑ t : B → offsets m, (law V).real (T t) := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _t : B → offsets m, θ^B.card := Finset.sum_le_sum (fun t _ => hbound t)
      _ = (D*θ)^B.card := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_coe,
          nsmul_eq_mul,Nat.cast_pow,mul_pow,D]
      _ = β^(P^2*B.card) := by
        rw [show D*θ = β^(P^2) by dsimp [θ];field_simp, pow_mul]
      _ ≤ β^A.card := pow_le_pow_of_le_one hβ.le hβ1 hsize
      _ ≤ ρ^A.card := pow_le_pow_left₀ hβ.le (min_le_left _ _) _
  change (volume S).toReal / (volume (body V)).toReal ≤ _
  rw [← law_real_of_subset V S (fun _ hh => hh.1)]
  exact hprob

end SparseBlocks

end
end
end
end
end
end
end

end OAI
