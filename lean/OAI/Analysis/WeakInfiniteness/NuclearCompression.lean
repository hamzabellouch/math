import Mathlib
import OAI.Analysis.WeakInfiniteness.NuclearColumn
import OAI.Analysis.WeakInfiniteness.PerturbationRows

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

def finiteColumn (v : Fin n → A) : CStarMatrix (Fin n) (Fin 1) A :=
  CStarMatrix.ofMatrix (fun i _ => v i)

omit [PartialOrder A] [StarOrderedRing A] in
lemma finiteColumn_initial (v : Fin n → A) :
    matrixSingletonHom ((finiteColumn v).conjTranspose*finiteColumn v)=∑ i,star (v i)*v i := rfl

lemma finiteColumn_norm_sq (v : Fin n → A) :
    ‖finiteColumn v‖^2=‖∑ i,star (v i)*v i‖ := by
  rw [← finiteColumn_initial,NonUnitalStarAlgHom.norm_map (matrixSingletonHom (A := A))
    matrixSingletonHom_injective,rectangular_norm_initial]

lemma finiteColumn_norm (v : Fin n → A) :
    ‖finiteColumn v‖=Real.sqrt ‖∑ i,star (v i)*v i‖ := by
  rw [← finiteColumn_norm_sq,Real.sqrt_sq (norm_nonneg _)]

omit [PartialOrder A] [StarOrderedRing A] in
lemma finiteColumn_sandwich (v w : Fin n → A) (r : A) :
    matrixSingletonHom ((finiteColumn v).conjTranspose*diagonalCopies n r*finiteColumn w)=
      ∑ i,star (v i)*r*w i := by
  change (∑ i,(∑ j,star (v j)*(if j=i then r else 0))*w i)=_
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

lemma norm_finite_sandwich_le (v w : Fin n → A) (r : A) :
    ‖∑ i,star (v i)*r*w i‖≤
      Real.sqrt ‖∑ i,star (v i)*v i‖*‖r‖*Real.sqrt ‖∑ i,star (w i)*w i‖ := by
  rw [← finiteColumn_sandwich]
  calc
    _ ≤ ‖(finiteColumn v).conjTranspose*diagonalCopies n r*finiteColumn w‖ :=
      NonUnitalStarAlgHom.norm_apply_le _ _
    _ ≤ (‖(finiteColumn v).conjTranspose‖*‖diagonalCopies n r‖)*‖finiteColumn w‖ :=
      (rectangular_norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (rectangular_norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (‖finiteColumn v‖*‖r‖)*‖finiteColumn w‖ := by
      rw [rectangular_norm_conjTranspose]
      gcongr
      exact norm_diagonalCopies_le _ _
    _ = _ := by rw [finiteColumn_norm,finiteColumn_norm]

omit [PartialOrder A] [StarOrderedRing A] in
def finiteCompression (v : Fin n → A) (r : A) : A := ∑ i,star (v i)*r*v i

lemma finiteCompression_norm_le (v : Fin n → A) (r : A) :
    ‖finiteCompression v r‖≤‖∑ i,star (v i)*v i‖*‖r‖ := by
  have h := norm_finite_sandwich_le v v r
  calc
    _ ≤ Real.sqrt ‖∑ i,star (v i)*v i‖*‖r‖*Real.sqrt ‖∑ i,star (v i)*v i‖ := h
    _ = _ := by rw [mul_right_comm _ ‖r‖,Real.mul_self_sqrt (norm_nonneg _)]

end

section Central

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {n : ℕ}

lemma finiteCompression_commutator (v : Fin n → A) (φ : A →L[ℂ] CStarMatrix (Fin n) (Fin n) ℂ)
    (hφ : CompletelyPositive φ) (a r : A) :
    a*finiteCompression v r-finiteCompression v r*a=
      -(∑ i,star (matrixCoefficientAction (φ (star a)) v i-v i*star a)*r*v i)+
        ∑ i,star (v i)*r*(matrixCoefficientAction (φ a) v i-v i*a) := by
  have he : (∑ i,∑ j,φ a j i • (star (v j)*r*v i)) =
      ∑ i,∑ j,φ a i j • (star (v i)*r*v j) := Finset.sum_comm
  simp only [finiteCompression,matrixCoefficientAction,star_sub,star_sum,star_smul,
    completelyPositive_map_star hφ,CStarMatrix.star_apply,star_star,star_mul,
    Finset.sum_mul,Finset.mul_sum,sub_mul,mul_sub,Finset.sum_sub_distrib,
    smul_mul_assoc,mul_smul_comm]
  rw [he]
  simp only [mul_assoc]
  abel

lemma finiteCompression_commutator_norm_le (v : Fin n → A)
    (φ : A →L[ℂ] CStarMatrix (Fin n) (Fin n) ℂ) (hφ : CompletelyPositive φ)
    (hv : ‖∑ i,star (v i)*v i‖≤1) (a r : A) (hr : ‖r‖≤1) :
    ‖a*finiteCompression v r-finiteCompression v r*a‖ ≤
      Real.sqrt ‖∑ i,star (matrixCoefficientAction (φ (star a)) v i-v i*star a)*
        (matrixCoefficientAction (φ (star a)) v i-v i*star a)‖+
      Real.sqrt ‖∑ i,star (matrixCoefficientAction (φ a) v i-v i*a)*
        (matrixCoefficientAction (φ a) v i-v i*a)‖ := by
  let d (a : A) (i : Fin n) := matrixCoefficientAction (φ a) v i-v i*a
  have hs : Real.sqrt ‖∑ i,star (v i)*v i‖≤1 := (Real.sqrt_le_one).mpr hv
  rw [finiteCompression_commutator v φ hφ a r]
  calc
    _ ≤ ‖∑ i,star (d (star a) i)*r*v i‖+‖∑ i,star (v i)*r*d a i‖ := by
      simpa only [norm_neg] using norm_add_le
        (-(∑ i,star (d (star a) i)*r*v i)) (∑ i,star (v i)*r*d a i)
    _ ≤ (Real.sqrt ‖∑ i,star (d (star a) i)*d (star a) i‖*‖r‖*
        Real.sqrt ‖∑ i,star (v i)*v i‖)+
        (Real.sqrt ‖∑ i,star (v i)*v i‖*‖r‖*Real.sqrt ‖∑ i,star (d a i)*d a i‖) :=
      add_le_add (norm_finite_sandwich_le (d (star a)) v r)
        (norm_finite_sandwich_le v (d a) r)
    _ ≤ (Real.sqrt ‖∑ i,star (d (star a) i)*d (star a) i‖*1*1)+
        (1*1*Real.sqrt ‖∑ i,star (d a i)*d a i‖) := by gcongr
    _ = _ := by simp only [mul_one,one_mul,d]

end Central

end

end WeakPureInfiniteness
end

end OAI
