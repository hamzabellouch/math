import Mathlib
import OAI.Analysis.MatrixSigning.Realization.FaceQueryRealization

namespace OAI

/-! Real matrix bridge. -/

section

namespace AlgorithmicThinTrees.RealMatrixBridge
noncomputable section
open Matrix CurrentKS
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {n m d : ℕ}

def complexMatrix (A : Matrix (Fin n) (Fin m) ℝ) : Matrix (Fin n) (Fin m) ℂ :=
  A.map Complex.ofReal

lemma complexMatrix_one : complexMatrix (1 : Matrix (Fin n) (Fin n) ℝ)=1 := by
  exact Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one

lemma complexMatrix_add (A B : Matrix (Fin n) (Fin m) ℝ) :
    complexMatrix (A+B)=complexMatrix A+complexMatrix B := by
  ext i j;simp [complexMatrix]

lemma complexMatrix_sub (A B : Matrix (Fin n) (Fin m) ℝ) :
    complexMatrix (A-B)=complexMatrix A-complexMatrix B := by
  ext i j;simp [complexMatrix]

lemma complexMatrix_smul (r : ℝ) (A : Matrix (Fin n) (Fin m) ℝ) :
    complexMatrix (r • A)=r • complexMatrix A := by
  ext i j;simp [complexMatrix]

lemma complexMatrix_mul (A : Matrix (Fin n) (Fin d) ℝ) (B : Matrix (Fin d) (Fin m) ℝ) :
    complexMatrix (A*B)=complexMatrix A*complexMatrix B := by
  exact Matrix.map_mul (f:=Complex.ofRealHom)

lemma complexMatrix_transpose (A : Matrix (Fin n) (Fin m) ℝ) :
    complexMatrix Aᵀ=(complexMatrix A)ᴴ := by
  ext i j;simp [complexMatrix]

lemma complexMatrix_hermitian {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    (complexMatrix A).IsHermitian := by
  apply hA.map
  intro r
  simp

lemma complexMatrix_psd {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) :
    (complexMatrix A).PosSemidef := by
  obtain ⟨B,hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [hB]
  change (complexMatrix (Bᴴ*B)).PosSemidef
  rw [conjTranspose_eq_transpose_of_trivial,complexMatrix_mul,complexMatrix_transpose]
  exact posSemidef_conjTranspose_mul_self _

lemma of_complexMatrix_psd {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : (complexMatrix A).PosSemidef) : A.PosSemidef := by
  apply PosSemidef.of_dotProduct_mulVec_nonneg
  · apply isHermitian_iff_isSymm.mpr
    ext i j
    have hh := hA.isHermitian.apply i j
    have hr := congrArg Complex.re hh
    simpa [complexMatrix] using hr
  · intro x
    have hh := hA.dotProduct_mulVec_nonneg (fun i => (x i:ℂ))
    have he : star (fun i => (x i:ℂ)) ⬝ᵥ
        (complexMatrix A *ᵥ (fun i => (x i:ℂ)))=((x ⬝ᵥ (A*ᵥx):ℝ):ℂ) := by
      simp only [dotProduct,mulVec,complexMatrix,map_apply,Pi.star_apply,
        Complex.star_def,Complex.conj_ofReal,Complex.ofReal_sum,Complex.ofReal_mul]
    rw [he,Complex.zero_le_real] at hh
    simpa only [star_trivial] using hh

lemma complexMatrix_mono {A B : Matrix (Fin n) (Fin n) ℝ} (h : A ≤ B) :
    complexMatrix A ≤ complexMatrix B := by
  rw [Matrix.le_iff,←complexMatrix_sub]
  exact complexMatrix_psd h

lemma of_complexMatrix_le {A B : Matrix (Fin n) (Fin n) ℝ}
    (h : complexMatrix A ≤ complexMatrix B) : A ≤ B := by
  apply of_complexMatrix_psd
  rw [complexMatrix_sub]
  exact h

lemma le_norm_identity {A : Matrix (Fin n) (Fin n) ℝ} (hh : A.IsHermitian) :
    A ≤ opNorm (complexMatrix A) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  apply of_complexMatrix_le
  rw [complexMatrix_smul,complexMatrix_one]
  exact Hermitian.le_operatorNorm_smul_one ⟨complexMatrix A,complexMatrix_hermitian hh⟩

lemma norm_le_of_psd_bound {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    {r : ℝ} (hr : 0 ≤ r) (h : A ≤ r • (1 : Matrix (Fin n) (Fin n) ℝ)) :
    opNorm (complexMatrix A) ≤ r := by
  apply Hermitian.operatorNorm_le_of_psd_le (A:=⟨complexMatrix A,complexMatrix_hermitian hA.isHermitian⟩)
    (complexMatrix_psd hA) hr
  have hh := complexMatrix_mono h
  rwa [complexMatrix_smul,complexMatrix_one] at hh

lemma bounds_of_norm_le {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    {r : ℝ} (h : opNorm (complexMatrix A) ≤ r) :
    (-r) • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ A ∧ A ≤ r • 1 := by
  have hs {s t : ℝ} (hst : s ≤ t) : s • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ t • 1 := by
    rw [Matrix.le_iff,←sub_smul]
    exact PosSemidef.one.smul (sub_nonneg.mpr hst)
  constructor
  · have hh := le_norm_identity hA.neg
    have hn : opNorm (complexMatrix (-A))=opNorm (complexMatrix A) := by
      have he : complexMatrix (-A)=-complexMatrix A := by ext i j;simp [complexMatrix]
      rw [he,opNorm,map_neg,norm_neg]
      rfl
    rw [hn] at hh
    have hu := hh.trans (hs h)
    have hl := neg_le_neg hu
    simpa only [neg_neg,neg_smul] using hl
  · exact (le_norm_identity hA).trans (hs h)

end
end AlgorithmicThinTrees.RealMatrixBridge
end

end OAI
