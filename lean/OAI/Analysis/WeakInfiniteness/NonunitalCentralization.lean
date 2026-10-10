import Mathlib
import OAI.Analysis.WeakInfiniteness.ElementaryCP
import OAI.Analysis.WeakInfiniteness.NonunitalColumnApproximation
import OAI.Analysis.WeakInfiniteness.NonunitalCompression

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

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {n : ℕ}

lemma norm_finite_inner_le (v w : Fin n → A) :
    ‖∑ i,star (v i)*w i‖≤
      Real.sqrt ‖∑ i,star (v i)*v i‖*Real.sqrt ‖∑ i,star (w i)*w i‖ := by
  have he : matrixSingletonHom ((finiteColumn v).conjTranspose*finiteColumn w)=
      ∑ i,star (v i)*w i := rfl
  rw [← he]
  calc
    _ ≤ ‖(finiteColumn v).conjTranspose*finiteColumn w‖ :=
      NonUnitalStarAlgHom.norm_apply_le _ _
    _ ≤ ‖(finiteColumn v).conjTranspose‖*‖finiteColumn w‖ := rectangular_norm_mul_le _ _
    _ = _ := by rw [rectangular_norm_conjTranspose,finiteColumn_norm,finiteColumn_norm]

lemma nonunitalCoefficient_initial_action_error (v : Fin n → A)
    (hv : ‖nonunitalCoefficientMap v 1‖≤1)
    (M : CStarMatrix (Fin n) (Fin n) ℂ) (a : A) :
    ‖nonunitalCoefficientMap v 1*a-a‖≤
      ‖nonunitalCoefficientMap v M-a‖+
        Real.sqrt ‖∑ i,star (nonunitalCoefficientAction M v i-v i*a)*
          (nonunitalCoefficientAction M v i-v i*a)‖ := by
  have he : nonunitalCoefficientMap v M-nonunitalCoefficientMap v 1*a=
      ∑ i,star (v i)*(nonunitalCoefficientAction M v i-v i*a) := by
    rw [nonunitalCoefficientMap_mixed,nonunitalCoefficientMap_initial]
    simp only [Finset.sum_mul,mul_sub,Finset.sum_sub_distrib,mul_assoc]
  have hb := norm_finite_inner_le v (fun i => nonunitalCoefficientAction M v i-v i*a)
  have hs : Real.sqrt ‖∑ i,star (v i)*v i‖≤1 := Real.sqrt_le_one.mpr (by
    simpa only [nonunitalCoefficientMap_initial] using hv)
  calc
    _ ≤ ‖nonunitalCoefficientMap v 1*a-nonunitalCoefficientMap v M‖+
        ‖nonunitalCoefficientMap v M-a‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖∑ i,star (v i)*(nonunitalCoefficientAction M v i-v i*a)‖+
        ‖nonunitalCoefficientMap v M-a‖ := by rw [norm_sub_rev,he]
    _ ≤ Real.sqrt ‖∑ i,star (nonunitalCoefficientAction M v i-v i*a)*
        (nonunitalCoefficientAction M v i-v i*a)‖+‖nonunitalCoefficientMap v M-a‖ := by
      refine add_le_add (hb.trans ?_) le_rfl
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg _)
    _ = _ := add_comm _ _

lemma nuclear_weaklyPurelyInfinite_nonunital_centralizing_compression
    (hN : Nuclear A) (hW : WeaklyPurelyInfinite A)
    (F : Finset A) (ε : ℝ) (hε : 0<ε) :
    ∃ n : ℕ,1≤n ∧∃ φ : A →L[ℂ] CStarMatrix (Fin n) (Fin n) ℂ,
      ∃ v : Fin n → A,CompletelyPositive φ ∧ ‖φ‖≤1 ∧
      ‖nonunitalCoefficientMap v 1‖≤1 ∧
      CompletelyPositive (finiteCompressionContinuous v) ∧
      ‖finiteCompressionContinuous v‖≤1 ∧
      ∀ a∈F,‖nonunitalCoefficientMap v (φ a)-a‖<ε ∧
        ‖nonunitalCoefficientMap v 1*a-a‖<ε ∧
        ‖a*nonunitalCoefficientMap v 1-a‖<ε ∧
        ∀ r : A,‖r‖≤1 → ‖a*finiteCompression v r-finiteCompression v r*a‖<ε := by
  classical
  let δ : ℝ := min (ε/4) (ε^2/64)
  have hδ : 0<δ := lt_min (by positivity) (by positivity)
  have hδε : δ≤ε/4 := min_le_left _ _
  have hδsq : δ≤ε^2/64 := min_le_right _ _
  let G : Finset A := F∪F.image star
  obtain ⟨n,hn,φ,v,hφ,hφn,hv,happ⟩ :=
    nuclear_weaklyPurelyInfinite_nonunital_column_approximation hN hW G δ hδ
  have hvn : ‖∑ i,star (v i)*v i‖≤1 := by
    simpa only [nonunitalCoefficientMap_initial] using hv
  let D (b : A) : ℝ := ‖∑ i,star (nonunitalCoefficientAction (φ b) v i-v i*b)*
    (nonunitalCoefficientAction (φ b) v i-v i*b)‖
  have hD (b : A) (hb : b∈G) : Real.sqrt (D b)<ε/8 := by
    have hb0 : 0≤D b := norm_nonneg _
    have hbδ : D b<δ := (happ b hb).2
    have hsq := Real.sq_sqrt hb0
    have hs0 := Real.sqrt_nonneg (D b)
    nlinarith
  have hrow (a : A) (ha : a∈G) : ‖nonunitalCoefficientMap v 1*a-a‖<ε := by
    have ht := nonunitalCoefficient_initial_action_error v hv (φ a) a
    have h1 := (happ a ha).1
    have h2 := hD a ha
    change _ ≤ ‖nonunitalCoefficientMap v (φ a)-a‖+Real.sqrt (D a) at ht
    linarith
  have hqstar : star (nonunitalCoefficientMap v 1)=nonunitalCoefficientMap v 1 :=
    (IsSelfAdjoint.of_nonneg (nonunitalCoefficientMap_nonneg v 1 zero_le_one)).star_eq
  refine ⟨n,hn,φ,v,hφ,hφn,hv,finiteCompressionContinuous_cp v,
    (finiteCompressionContinuous_norm_le v).trans hvn,?_⟩
  intro a ha
  have haG : a∈G := Finset.mem_union_left _ ha
  have hasG : star a∈G := Finset.mem_union_right _ (Finset.mem_image_of_mem star ha)
  refine ⟨(happ a haG).1.trans_le (hδε.trans (by linarith)),hrow a haG,?_,?_⟩
  · have he : star (nonunitalCoefficientMap v 1*star a-star a)=a*nonunitalCoefficientMap v 1-a := by
      rw [star_sub,star_mul,star_star,hqstar]
    rw [← he,norm_star]
    exact hrow (star a) hasG
  · intro r hr
    exact (finiteCompression_nonunital_commutator_norm_le v φ hφ hvn a r hr).trans_lt
      (show Real.sqrt (D (star a))+Real.sqrt (D a)<ε by
        have h1 := hD (star a) hasG
        have h2 := hD a haG
        linarith)

end

end

end WeakPureInfiniteness
end

end OAI
