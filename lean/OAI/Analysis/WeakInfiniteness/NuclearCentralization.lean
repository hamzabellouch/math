import Mathlib
import OAI.Analysis.WeakInfiniteness.ElementaryCP
import OAI.Analysis.WeakInfiniteness.NuclearColumnApproximation

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

open scoped CStarAlgebra ComplexOrder

universe u

section

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma nuclear_weaklyPurelyInfinite_centralizing_compression
    (hN : Nuclear A) (hW : WeaklyPurelyInfinite A)
    (F : Finset A) (ε : ℝ) (hε : 0<ε) :
    ∃ n : ℕ,1≤n ∧∃ v : Fin n → A,
      CompletelyPositive (finiteCompressionContinuous v) ∧
      ‖finiteCompressionContinuous v‖≤1 ∧
      ‖finiteCompression v 1-1‖<ε ∧
      ∀ a∈F,∀ r : A,‖r‖≤1 →
        ‖a*finiteCompression v r-finiteCompression v r*a‖<ε := by
  classical
  let δ : ℝ := min (ε/2) (ε^2/16)
  have hδ : 0<δ := lt_min (by positivity) (by positivity)
  have hδε : δ<ε := (min_le_left _ _).trans_lt (by linarith)
  have hδsq : δ≤ε^2/16 := min_le_right _ _
  let G : Finset A := F∪F.image star
  obtain ⟨n,hn,φ,v,hφ,_,hv,hv1,happ⟩ :=
    nuclear_weaklyPurelyInfinite_column_approximation hN hW G δ hδ
  let k : Fin n := ⟨0,by omega⟩
  have hv0 : 0 ≤ matrixCoefficientMap v 1 := matrixCoefficientMap_nonneg v k 1 zero_le_one
  have hvn : ‖∑ i,star (v i)*v i‖≤1 := by
    simpa only [matrixCoefficientMap_initial] using
      (CStarAlgebra.norm_le_one_iff_of_nonneg _ hv0).mpr hv
  refine ⟨n,hn,v,finiteCompressionContinuous_cp v,
    (finiteCompressionContinuous_norm_le v).trans hvn,?_,?_⟩
  · simpa only [finiteCompression,mul_one,matrixCoefficientMap_initial] using hv1.trans hδε
  · intro a ha r hr
    have haG : a∈G := Finset.mem_union_left _ ha
    have hasG : star a∈G := Finset.mem_union_right _ (Finset.mem_image_of_mem star ha)
    let D (b : A) : ℝ := ‖∑ i,star (matrixCoefficientAction (φ b) v i-v i*b)*
      (matrixCoefficientAction (φ b) v i-v i*b)‖
    have hD (b : A) (hb : b∈G) : Real.sqrt (D b)<ε/4 := by
      have hb0 : 0≤D b := norm_nonneg _
      have hbδ : D b<δ := (happ b hb).2
      have hsq := Real.sq_sqrt hb0
      have hs0 := Real.sqrt_nonneg (D b)
      nlinarith
    exact (finiteCompression_commutator_norm_le v φ hφ hvn a r hr).trans_lt
      (show Real.sqrt (D (star a))+Real.sqrt (D a)<ε by
        have h1 := hD (star a) hasG
        have h2 := hD a haG
        linarith)

end

end

end WeakPureInfiniteness
end

end OAI
