import Mathlib
import OAI.Analysis.WeakInfiniteness.ElementaryComparison
import OAI.Analysis.WeakInfiniteness.RectangularPolar

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped Topology CStarAlgebra

local instance matrixRealModuleComparison {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {n : Type*} [Fintype n] :
    Module ℝ (CStarMatrix n n A) := Module.complexToReal _

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]

lemma cuntzSubequiv_of_hereditary {h x : CStarMatrix n n A}
    (hh : 0 ≤ h) (hx : 0 ≤ x) (hm : x ∈ hereditarySubalgebra h hh.isSelfAdjoint) :
    CuntzSubequiv x h := by
  intro ε hε
  simpa only [CStarMatrix.star_eq_conjTranspose] using
    exists_comparison_of_hereditary h x hh hx hm ε hε

lemma cuntzSubequiv_of_le_smul {h x : CStarMatrix n n A}
    (hh : 0 ≤ h) (hx : 0 ≤ x) {c : ℝ} (hc : 0 ≤ c) (hxh : x ≤ c • h) :
    CuntzSubequiv x h :=
  cuntzSubequiv_of_hereditary hh hx (mem_hereditary_of_le_smul h x hh hx hc hxh)

lemma rectangular_initial_cuntz_range (u : CStarMatrix m n A) :
    CuntzSubequiv (u.conjTranspose*u) (u*u.conjTranspose) := by
  let t := u.conjTranspose*u
  have ht : 0 ≤ t := rectangular_initial_nonneg u
  have htt : 0 ≤ t*t := by simpa only [ht.star_eq] using star_mul_self_nonneg t
  have hm : t ∈ hereditarySubalgebra (t*t) htt.isSelfAdjoint := by
    have hs := sqrt_mem_hereditary (t*t) (t*t) htt.isSelfAdjoint
      (self_mem_hereditary (t*t) htt) htt
    rwa [CFC.sqrt_mul_self t ht] at hs
  intro ε hε
  obtain ⟨b,hb⟩ := cuntzSubequiv_of_hereditary htt ht hm ε hε
  refine ⟨u*b, ?_⟩
  have he : (u*b).conjTranspose*(u*u.conjTranspose)*(u*b) = b.conjTranspose*(t*t)*b := by
    rw [rectangular_star_mul]
    dsimp only [t]
    simp only [rectangular_mul_assoc]
  rwa [he]

lemma CuntzSubequiv.sandwich_left {x : CStarMatrix n n A} {h : CStarMatrix m m A}
    (hxh : CuntzSubequiv x h) (v : CStarMatrix n k A) :
    CuntzSubequiv (v.conjTranspose*x*v) h := by
  intro ε hε
  obtain ⟨δ,hδ,hcont⟩ := Metric.continuousAt_iff.mp
    (continuous_matrix_sandwich v).continuousAt ε hε
  obtain ⟨w,hw⟩ := hxh δ hδ
  refine ⟨w*v, ?_⟩
  rw [rectangular_star_mul]
  have he : (v.conjTranspose*w.conjTranspose)*h*(w*v) =
      v.conjTranspose*(w.conjTranspose*h*w)*v := by
    simp only [rectangular_mul_assoc]
  rw [he]
  simpa only [dist_eq_norm] using hcont (by simpa only [dist_eq_norm] using hw)

lemma rectangular_sandwich_cuntz (h : CStarMatrix n n A) (v : CStarMatrix n m A) :
    CuntzSubequiv (v.conjTranspose*h*v) h := (cuntzSubequiv_refl h).sandwich_left v

end

end WeakPureInfiniteness
end

end OAI
