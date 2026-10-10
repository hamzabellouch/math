import Mathlib
import OAI.Analysis.WeakInfiniteness.NuclearCoefficients
import OAI.Analysis.WeakInfiniteness.NuclearColumn

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

lemma matrixCoefficient_initial_gap {n : Type*} [Fintype n] [DecidableEq n]
    (v : n → A) (k : n) (φ : A →L[ℂ] CStarMatrix n n ℂ)
    (hφ : CompletelyPositive φ) (hφn : ‖φ‖≤1) (hv : matrixCoefficientMap v 1≤1) :
    ‖matrixCoefficientMap v 1-1‖≤‖matrixCoefficientMap v (φ 1)-1‖ := by
  have hq := matrixCoefficientMap_mono v k (completelyPositive_one_le_one hφ hφn)
  have hle : 1-matrixCoefficientMap v 1≤1-matrixCoefficientMap v (φ 1) := by
    apply sub_nonneg.mp
    convert sub_nonneg.mpr hq using 1
    abel
  have h := CStarAlgebra.norm_le_norm_of_le_of_nonneg hle (sub_nonneg.mpr hv)
  simpa only [norm_sub_rev (1:A)] using h

lemma nuclear_weaklyPurelyInfinite_column_approximation
    (hN : Nuclear A) (hW : WeaklyPurelyInfinite A)
    (F : Finset A) (ε : ℝ) (hε : 0<ε) :
    ∃ n : ℕ,1≤n ∧∃ φ : A →L[ℂ] CStarMatrix (Fin n) (Fin n) ℂ,
      ∃ v : Fin n → A,CompletelyPositive φ ∧ ‖φ‖≤1 ∧
      matrixCoefficientMap v 1≤1 ∧ ‖matrixCoefficientMap v 1-1‖<ε ∧
      ∀ a∈F,‖matrixCoefficientMap v (φ a)-a‖<ε ∧
        ‖∑ i,star (matrixCoefficientAction (φ a) v i-v i*a)*
          (matrixCoefficientAction (φ a) v i-v i*a)‖<ε := by
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
  let G : Finset A := insert 1 (F∪F.image (fun a => star a*a))
  obtain ⟨n,hn,φ,v,hφ,hφn,hvn,happ⟩ :=
    nuclear_weaklyPurelyInfinite_coefficient_approximation hN hW G δ hδ
  let k : Fin n := ⟨0,by omega⟩
  have hv0 : 0 ≤ matrixCoefficientMap v 1 := matrixCoefficientMap_nonneg v k 1 zero_le_one
  have hv : matrixCoefficientMap v 1≤1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ hv0).mp (by
      simpa only [matrixCoefficientMap_initial] using hvn)
  have happ' (a : A) (ha : a∈G) : ‖matrixCoefficientMap v (φ a)-a‖<δ := by
    simpa only [matrixCoefficientMap_apply] using happ a ha
  refine ⟨n,hn,φ,v,hφ,hφn,hv,?_,?_⟩
  · exact (matrixCoefficient_initial_gap v k φ hφ hφn hv).trans_lt
      ((happ' 1 (Finset.mem_insert_self ..)).trans hδε)
  · intro a ha
    have haG : a∈G := Finset.mem_insert_of_mem (Finset.mem_union_left _ ha)
    have haaG : star a*a∈G := Finset.mem_insert_of_mem (Finset.mem_union_right _
      (Finset.mem_image_of_mem _ ha))
    refine ⟨(happ' a haG).trans hδε,?_⟩
    have hb := matrixCoefficient_defect_norm_le v k φ hφ hφn hv a
    have he : 2*‖a‖*‖matrixCoefficientMap v (φ a)-a‖≤2*‖a‖*δ :=
      mul_le_mul_of_nonneg_left (happ' a haG).le (by positivity)
    have hm : 2*‖a‖*δ≤2*M*δ := by gcongr; exact hM a ha
    have hsmall : δ+2*M*δ<ε := by nlinarith
    exact hb.trans_lt ((add_lt_add_of_lt_of_le (happ' (star a*a) haaG) (he.trans hm)).trans hsmall)

end

end

end WeakPureInfiniteness
end

end OAI
