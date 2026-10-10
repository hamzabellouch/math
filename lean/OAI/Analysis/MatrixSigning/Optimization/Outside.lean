import Mathlib
import OAI.Analysis.MatrixSigning.Optimization.Signing
import OAI.Analysis.MatrixSigning.Matrices.MatrixRealSmul

namespace OAI

open Matrix

namespace CurrentKS.RationalInput
noncomputable section
open Matrix CurrentKS.Hermitian CurrentKS.State CurrentKS.Difference
open CurrentKS.RationalFace CurrentKS.RationalSDP
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

lemma zero_outside (x : Input) (hx : Admissible x) (i : Fin x.N)
    (hi : i∉Set.range (index x)) : x.matrix i=0 := by
  apply (trace_zero_iff x hx i).mp
  by_contra hn
  exact hi ((index_range x i).mpr hn)

lemma trimmed_square_sum (x : Input) (hx : Admissible x) :
    (∑ j,x.matrix (index x j)*x.matrix (index x j))=∑ i,x.matrix i*x.matrix i := by
  apply Fintype.sum_of_injective (index x) (index_injective x)
  · intro i hi
    rw [zero_outside x hx i hi,mul_zero]
  · intro j;rfl

lemma lifted_signs_abs (x : Input) (s : Fin (indices x).length → ℚ) (hs : ∀ j,|s j|=1) :
    ∀ i,|orientation x i*extend (index x) (fun _=>1) s i|=1 := by
  intro i
  rw [abs_mul,orientation_abs,one_mul]
  unfold extend
  cases lookup (index x) i with
  | none => norm_num
  | some j => exact hs j

lemma sign_bits_value (x : Input) (s : Fin (indices x).length → ℚ) (hs : ∀ j,|s j|=1) (i : Fin x.N) :
    signValue ((List.ofFn fun i => decide (orientation x i*extend (index x) (fun _=>1) s i=1)).getD i.val false)=
      ((orientation x i*extend (index x) (fun _=>1) s i:ℚ):ℝ) := by
  have ha := (abs_eq (show (0:ℚ)≤1 by norm_num)).mp (lifted_signs_abs x s hs i)
  rcases ha with h|h
  · norm_num [List.getD,signValue,h]
  · norm_num [List.getD,signValue,h]

theorem signing_good (x : Input) (hx : Admissible x) : GoodOutput x (signing x) := by
  by_cases hn : (indices x).length=0
  · have hz : ∀ i,x.matrix i=0 := by
      intro i
      apply zero_outside x hx i
      rintro ⟨j,_⟩
      have hj := j.isLt
      omega
    constructor
    · simp [signing,hn]
    · have hsum : signedSum x (signing x)=0 := by simp only [signedSum,hz,matrix_real_smul_zero,Finset.sum_const_zero]
      have hvar : variance x=0 := by simp [variance,hz]
      rw [hsum,hvar]
      simp only [opNorm,map_zero,norm_zero,Real.sqrt_zero,mul_zero,le_refl]
  · let : NeZero (indices x).length := ⟨hn⟩
    let : NeZero x.d := ⟨dimension_ne x hx hn⟩
    let coords := normalizedCoordinates x
    let A := rationalAtoms coords
    let s := normalizedRun coords
    have hp := normalized_input_properties x hx hn
    have hh := normalizedRun_spec coords hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
    have hs : ∀ j,|s j|=1 := hh.1
    have hmat (j) : (A j:Mat x.d)=normalizedMatrix x.matrix (index x j) :=
      decode_normalizedCoordinates x hx j
    have hD : 0 < normalizer x.matrix := by
      rw [←scale_cast]
      exact_mod_cast scale_pos x hn
    have hout : signing x=List.ofFn (fun i => decide (orientation x i*extend (index x) (fun _=>1) s i=1)) := by
      simp only [signing,ite_eq_right hn]
      rfl
    have hsign (i) : signValue ((signing x).getD i.val false)=
        ((orientation x i*extend (index x) (fun _=>1) s i:ℚ):ℝ) := by
      rw [hout]
      exact sign_bits_value x s hs i
    have hsum : signedSum x (signing x)=normalizer x.matrix • (S A (pointCast s):H x.d).val := by
      unfold signedSum
      simp only [hsign,Rat.cast_mul,orientation_cast]
      have he : (∑ j,(traceSign (x.matrix (index x j))*(s j:ℝ)) • x.matrix (index x j))=
          ∑ i,(traceSign (x.matrix i)*((extend (index x) (fun _=>1) s i:ℚ):ℝ)) • x.matrix i := by
        apply Fintype.sum_of_injective (index x) (index_injective x)
        · intro i hi
          rw [zero_outside x hx i hi,matrix_real_smul_zero]
        · intro j
          rw [extend_at (index_injective x)]
      rw [←he,coe_S,matrix_real_smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [hmat]
      simp only [normalizedMatrix,pointCast,matrix_real_smul_smul]
      congr 1
      field_simp [hD.ne']
    have hv : operatorNorm (varianceH A)=(normalizer x.matrix)⁻¹^2*opNorm (variance x) := by
      change opNorm ((varianceH A:H x.d):Mat x.d)=_
      rw [coe_varianceH]
      simp only [hmat,normalized_square]
      rw [←matrix_real_smul_sum,trimmed_square_sum x hx,opNorm_real_smul,abs_of_nonneg (sq_nonneg _)]
      rfl
    have hroot : Real.sqrt (operatorNorm (varianceH A))=
        (normalizer x.matrix)⁻¹*Real.sqrt (opNorm (variance x)) := by
      rw [hv,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_pos (inv_pos.mpr hD)]
    refine ⟨by rw [hout,List.length_ofFn],?_⟩
    rw [hsum,opNorm_real_smul,abs_of_pos hD]
    have hb := mul_le_mul_of_nonneg_left hh.2 hD.le
    rw [hroot] at hb
    change normalizer x.matrix*operatorNorm (S A (pointCast s)) ≤ _
    convert hb using 1
    first | rfl | field_simp [hD.ne']
end
end CurrentKS.RationalInput

end OAI
