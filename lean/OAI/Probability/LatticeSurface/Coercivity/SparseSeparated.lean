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

local instance (sort : Sort*) : DecidableEq sort := Classical.typeDecidableEq sort

lemma family_test_bound {I : Type*} [Fintype I] (V : Finset Vertex) (p : Parameters)
    (z : I → Vertex) (hz : ∀ i j, i ≠ j → Disjoint (sites p.L (z i)) (sites p.L (z j)))
    (η : ℝ) (hε : q (2*p.δ₀) ≤ 1/16) (hs : p.s₀ ≤ 1/8)
    (hshort : ((3*p.L+1:ℕ):ℝ)^4*q p.δ ≤ η)
    (hfar : ((3*p.L+1:ℕ):ℝ)^4*(1/2:ℝ)^p.k₀ ≤ η)
    (htie : 4*q p.s₀ ≤ η) (j : Fin 3) :
    (law V).real {h | ∀ i, h ∈ witnessTest V p j (z i)} ≤ η^Fintype.card I := by
  have hδ8 : p.δ ≤ 1/8 := p.δle.trans (p.δ₀le.trans (by norm_num))
  have hδ₀ : 0 < p.δ₀ := p.δpos.trans_le p.δle
  have hεpos : 0 < 2*p.δ₀ := by positivity
  have hε8 : 2*p.δ₀ ≤ 1/8 := by linarith [p.δ₀le]
  fin_cases j
  · apply witness_family V p.L z hz true p.δ p.δpos hδ8 (fun i => @shortEdges p.L (z i))
    · intro i t e he
      have heq := Finset.mem_singleton.mp he
      subst e
      exact t.1.property
    · intro i
      rw [short_entropy]
      exact hshort
  · apply witness_family V p.L z hz true (2*p.δ₀) hεpos hε8
      (fun i => @farEdges p.L (z i) p.k₀)
    · intro i t e he
      have hsub : t.2.val ⊆ pathEdges p.L (z i) t.1 :=
        Finset.mem_powerset.mp (Finset.mem_filter.mp t.2.property).1
      exact (pathEdges_mem p.L (z i) t.1 e (hsub he)).1
    · intro i
      exact (far_entropy p.L (z i) p.k₀ (2*p.δ₀) hεpos.le hε).trans hfar
  · apply witness_family V p.L z hz false p.s₀ p.spos hs (fun i => tieEdges p (z i))
    · intro i t e he
      have heq := Finset.mem_singleton.mp he
      subst e
      exact (face_neighbor_sites p (z i) t).2.1
    · intro i
      simpa only [tieEdges,Finset.card_singleton,pow_one,Finset.sum_const,
        Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] using htie

lemma separated_bad_bound {I : Type*} [Fintype I] (V : Finset Vertex) (p : Parameters)
    (z : I → Vertex) (hz : ∀ i j, i ≠ j → Disjoint (sites p.L (z i)) (sites p.L (z j)))
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hε : q (2*p.δ₀) ≤ 1/16) (hs : p.s₀ ≤ 1/8)
    (hshort : ((3*p.L+1:ℕ):ℝ)^4*q p.δ ≤ η)
    (hfar : ((3*p.L+1:ℕ):ℝ)^4*(1/2:ℝ)^p.k₀ ≤ η)
    (htie : 4*q p.s₀ ≤ η) :
    (law V).real {h | h ∈ body V ∧ ∀ i, bad p V h (z i)} ≤
      (3*η^(1/3:ℝ))^Fintype.card I := by
  have hj (j : Fin 3) (A : Finset I) :
      (law V).real {h | ∀ i ∈ A, h ∈ witnessTest V p j (z i)} ≤ η^A.card := by
    have hh := family_test_bound V p (fun i : A => z i) (by
      intro i k hik
      exact hz i k (fun hh => hik (Subtype.ext hh))) η hε hs hshort hfar htie j
    simpa only [Fintype.card_coe,Subtype.forall] using hh
  have hb := SparseWitness.alternative_sparse_bound (law V)
    (fun j i => witnessTest V p j (z i)) η hη hη1 hj
  calc
    _ ≤ (law V).real {h | ∀ i, ∃ j, h ∈ witnessTest V p j (z i)} := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro h hh i
      exact bad_witness V p h hh.1 (z i) (hh.2 i)
    _ ≤ (3:ℝ)^Fintype.card I * η^((Fintype.card I:ℝ)/3) := by
      simpa only [Fintype.card_fin,Nat.cast_ofNat] using hb
    _ = _ := by
      rw [mul_pow,← Real.rpow_mul_natCast hη.le]
      congr 1
      congr 1
      ring

lemma separated_parameters (θ : ℝ) (hθ : 0 < θ) :
    ∃ p : Parameters, ∀ (V : Finset Vertex) (I : Type) [Fintype I]
      (z : I → Vertex),
      (∀ i j, i ≠ j → Disjoint (sites p.L (z i)) (sites p.L (z j))) →
      (law V).real {h | h ∈ body V ∧ ∀ i, bad p V h (z i)} ≤ θ^Fintype.card I := by
  let β := min θ 1
  have hβ : 0 < β := lt_min hθ (by norm_num)
  have hβ1 : β ≤ 1 := min_le_right _ _
  let η := (β/3)^3
  have hη : 0 < η := pow_pos (div_pos hβ (by norm_num)) _
  have hη1 : η ≤ 1 := by
    exact (pow_le_pow_left₀ (by positivity) (show β/3 ≤ 1 by linarith) 3).trans_eq (by norm_num)
  obtain ⟨p,hε,hs,hshort,hfar,htie⟩ := sparse_parameters η hη
  refine ⟨p,?_⟩
  intro V I _ z hz
  have hh := separated_bad_bound V p z hz η hη hη1 hε hs hshort hfar htie
  have heq : 3*η^(1/3:ℝ) = β := by
    dsimp [η]
    rw [← Real.rpow_natCast,← Real.rpow_mul (show 0 ≤ β/3 by positivity)]
    norm_num
    ring
  rw [heq] at hh
  exact hh.trans (pow_le_pow_left₀ hβ.le (min_le_left _ _) _)

end SparseBlocks

end
end
end
end
end
end
end

end OAI
