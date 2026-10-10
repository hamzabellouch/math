import Mathlib
import OAI.Analysis.WeakInfiniteness.ChoiFactor
import OAI.Analysis.WeakInfiniteness.NonunitalCoefficients
import OAI.Analysis.WeakInfiniteness.NonunitalGram
import OAI.Analysis.WeakInfiniteness.NuclearExact

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

lemma nonunital_completelyPositive_coefficient_approximation
    (hpi : ∀ a : A,0 ≤ a → ProperlyInfinite (diagonalCopies 1 a))
    {n : ℕ} (hn : 1≤n)
    (ψ : CStarMatrix (Fin n) (Fin n) ℂ →L[ℂ] A)
    (hψ : CompletelyPositive ψ) (hψn : ‖ψ‖≤1)
    (F : Finset (CStarMatrix (Fin n) (Fin n) ℂ)) (ε : ℝ) (hε : 0<ε) :
    ∃ w : Fin n → A,‖∑ i,star (w i)*w i‖≤1 ∧
      ∀ M∈F,‖finiteCoefficientSum w M-ψ M‖<ε := by
  classical
  let W : ℝ := 1+∑ M∈F,(matrixCoefficientWeight M+(n:ℝ)*‖ψ M‖)
  have hW : 0<W := by
    have hs : 0≤∑ M∈F,(matrixCoefficientWeight M+(n:ℝ)*‖ψ M‖) :=
      Finset.sum_nonneg fun M _ => add_nonneg (matrixCoefficientWeight_nonneg M)
        (mul_nonneg (Nat.cast_nonneg n) (norm_nonneg _))
    dsimp only [W]
    linarith
  let η : ℝ := ε/(2*W)
  have hη : 0<η := div_pos hε (by positivity)
  have hηW : η*W<ε := by
    dsimp only [η]
    have hw0 : W≠0 := ne_of_gt hW
    field_simp
    nlinarith
  let M₀ : CStarMatrix (Fin n) (Fin n) A :=
    matrixLinearMap ψ (CStarMatrix.ofMatrix (fun i j : Fin n => matrixUnit i j))
  have hM₀ : 0≤M₀ := matrixLinearMap_nonneg hψ
    (matrixUnits_nonneg (⟨0,by omega⟩ : Fin n))
  obtain ⟨v,hv⟩ := nonunital_positive_matrix_gram_approximation hpi M₀ hM₀ η hη
  have hvij (i j : Fin n) : ‖star (v i)*v j-ψ (matrixUnit i j)‖≤η := by
    exact (CStarMatrix.norm_entry_le_norm (M := finiteGram v-M₀) (i := i) (j := j)).trans hv.le
  have hvM (M : CStarMatrix (Fin n) (Fin n) ℂ) :
      ‖finiteCoefficientSum v M-ψ M‖≤η*matrixCoefficientWeight M :=
    finiteCoefficientSum_gram_error ψ v η hvij M
  have hψ1 : ‖ψ 1‖≤1 := by
    let : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
    calc
      _ ≤ ‖ψ‖*‖(1:CStarMatrix (Fin n) (Fin n) ℂ)‖ := ψ.le_opNorm 1
      _ = ‖ψ‖ := by rw [norm_one,mul_one]
      _ ≤ 1 := hψn
  have hv1 : ‖finiteCoefficientSum v 1‖≤1+(n:ℝ)*η := by
    have he := hvM 1
    rw [matrixCoefficientWeight_one] at he
    have ht := norm_le_norm_sub_add (finiteCoefficientSum v 1) (ψ 1)
    nlinarith
  let κ : ℝ := (1+(n:ℝ)*η)⁻¹
  have hnη : 0≤(n:ℝ)*η := mul_nonneg (Nat.cast_nonneg n) hη.le
  have hd : 0<1+(n:ℝ)*η := by linarith
  have hκ : 0<κ := inv_pos.mpr hd
  have hκe : κ*(1+(n:ℝ)*η)=1 := inv_mul_cancel₀ (ne_of_gt hd)
  have hκ1 : κ≤1 := by nlinarith
  have hκerr : 1-κ≤(n:ℝ)*η := by nlinarith [mul_nonneg (sub_nonneg.mpr hκ1) hnη]
  let w : Fin n → A := fun i => (Real.sqrt κ:ℂ) • v i
  refine ⟨w,?_,?_⟩
  · rw [← finiteCoefficientSum_one]
    change ‖finiteCoefficientSum (fun i => (Real.sqrt κ:ℂ) • v i) 1‖≤1
    rw [finiteCoefficientSum_rescale v κ hκ.le 1,norm_smul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hκ]
    exact (mul_le_mul_of_nonneg_left hv1 hκ.le).trans_eq hκe
  · intro M hMF
    have hMW : matrixCoefficientWeight M+(n:ℝ)*‖ψ M‖≤W := by
      have ht := Finset.single_le_sum (s := F)
        (f := fun M => matrixCoefficientWeight M+(n:ℝ)*‖ψ M‖)
        (fun M _ => add_nonneg (matrixCoefficientWeight_nonneg M)
          (mul_nonneg (Nat.cast_nonneg n) (norm_nonneg _))) hMF
      dsimp only [W]
      linarith
    calc
      _ ≤ ‖finiteCoefficientSum v M-ψ M‖+(1-κ)*‖ψ M‖ :=
        finiteCoefficientSum_rescale_error v κ hκ.le hκ1 ψ M
      _ ≤ η*matrixCoefficientWeight M+((n:ℝ)*η)*‖ψ M‖ :=
        add_le_add (hvM M) (mul_le_mul_of_nonneg_right hκerr (norm_nonneg _))
      _ = η*(matrixCoefficientWeight M+(n:ℝ)*‖ψ M‖) := by ring
      _ ≤ η*W := mul_le_mul_of_nonneg_left hMW hη.le
      _ < ε := hηW

lemma nuclear_weaklyPurelyInfinite_nonunital_coefficient_approximation
    (hN : Nuclear A) (hW : WeaklyPurelyInfinite A)
    (F : Finset A) (ε : ℝ) (hε : 0<ε) :
    ∃ n : ℕ,1≤n ∧∃ φ : A →L[ℂ] CStarMatrix (Fin n) (Fin n) ℂ,
      ∃ v : Fin n → A,CompletelyPositive φ ∧ ‖φ‖≤1 ∧
      ‖∑ i,star (v i)*v i‖≤1 ∧
      ∀ a∈F,‖finiteCoefficientSum v (φ a)-a‖<ε := by
  classical
  have hpi : ∀ a : A,0 ≤ a → ProperlyInfinite (diagonalCopies 1 a) :=
    fun _ ha => exact_weaklyPurelyInfinite_individuallyProperlyInfinite_any
      (nuclear_exact hN) hW ha
  obtain ⟨n,hn,φ,ψ,hφ,hψ,hφn,hψn,happ⟩ := hN F (ε/2) (by positivity)
  obtain ⟨v,hv,hvapp⟩ := nonunital_completelyPositive_coefficient_approximation
    hpi hn ψ hψ hψn (F.image φ) (ε/2) (by positivity)
  refine ⟨n,hn,φ,v,hφ,hφn,hv,?_⟩
  intro a ha
  calc
    _ ≤ ‖finiteCoefficientSum v (φ a)-ψ (φ a)‖+‖ψ (φ a)-a‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε/2+ε/2 := add_lt_add (hvapp (φ a) (Finset.mem_image_of_mem φ ha)) (happ a ha)
    _ = ε := by ring

end

end

end WeakPureInfiniteness
end

end OAI
