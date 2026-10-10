import Mathlib
import OAI.Analysis.WeakInfiniteness.NonunitalColumn
import OAI.Analysis.WeakInfiniteness.NonunitalRealization

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

lemma nuclear_weaklyPurelyInfinite_nonunital_column_approximation
    (hN : Nuclear A) (hW : WeaklyPurelyInfinite A)
    (F : Finset A) (ε : ℝ) (hε : 0<ε) :
    ∃ n : ℕ,1≤n ∧∃ φ : A →L[ℂ] CStarMatrix (Fin n) (Fin n) ℂ,
      ∃ v : Fin n → A,CompletelyPositive φ ∧ ‖φ‖≤1 ∧
      ‖nonunitalCoefficientMap v 1‖≤1 ∧
      ∀ a∈F,‖nonunitalCoefficientMap v (φ a)-a‖<ε ∧
        ‖∑ i,star (nonunitalCoefficientAction (φ a) v i-v i*a)*
          (nonunitalCoefficientAction (φ a) v i-v i*a)‖<ε := by
  classical
  let M : ℝ := ∑ a ∈ F, ‖a‖
  have hM0 : 0≤M := Finset.sum_nonneg fun a _ => norm_nonneg a
  have hM (a : A) (ha : a∈F) : ‖a‖≤M :=
    Finset.single_le_sum (fun b _ => norm_nonneg b) ha
  let δ : ℝ := ε/(2*(1+2*M))
  have hd : 0<2*(1+2*M) := by positivity
  have hδ : 0<δ := div_pos hε hd
  have hδeq : δ*(2*(1+2*M))=ε := div_mul_cancel₀ ε (ne_of_gt hd)
  have hδε : δ<ε := by nlinarith [mul_nonneg hM0 (le_of_lt hδ)]
  let G : Finset A := F∪F.image (fun a => star a*a)
  obtain ⟨n,hn,φ,v,hφ,hφn,hvn,happ⟩ :=
    nuclear_weaklyPurelyInfinite_nonunital_coefficient_approximation hN hW G δ hδ
  have hv : ‖nonunitalCoefficientMap v 1‖≤1 := by
    simpa only [nonunitalCoefficientMap_initial] using hvn
  have happ' (a : A) (ha : a∈G) : ‖nonunitalCoefficientMap v (φ a)-a‖<δ := by
    simpa only [nonunitalCoefficientMap_apply,finiteCoefficientSum] using happ a ha
  refine ⟨n,hn,φ,v,hφ,hφn,hv,?_⟩
  intro a ha
  have haG : a∈G := Finset.mem_union_left _ ha
  have haaG : star a*a∈G := Finset.mem_union_right _
    (Finset.mem_image_of_mem _ ha)
  refine ⟨(happ' a haG).trans hδε,?_⟩
  have hb := nonunitalCoefficient_defect_norm_le v φ hφ hφn hv a
  have he : 2*‖a‖*‖nonunitalCoefficientMap v (φ a)-a‖≤2*‖a‖*δ :=
    mul_le_mul_of_nonneg_left (happ' a haG).le (by positivity)
  have hm : 2*‖a‖*δ≤2*M*δ := by gcongr; exact hM a ha
  have hsmall : δ+2*M*δ<ε := by nlinarith
  exact hb.trans_lt ((add_lt_add_of_lt_of_le (happ' (star a*a) haaG) (he.trans hm)).trans hsmall)

end

end

end WeakPureInfiniteness
end

end OAI
