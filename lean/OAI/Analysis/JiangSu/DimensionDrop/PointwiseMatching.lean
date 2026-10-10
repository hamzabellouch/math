import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CuntzSemigroup.CuntzRescaling
import OAI.Analysis.JiangSu.Nonunital.Regularization
import OAI.Analysis.JiangSu.CStarAlgebras.FiniteSpectralMatching

namespace OAI

noncomputable section


namespace JiangSuConstruction
open scoped CStarAlgebra ComplexOrder Kronecker
open FiniteSpectralMatching

variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem interval_matching_of_cumulative (x y : Fin n → Interval) (δ : ℝ)
    (hxy : ∀ t : ℝ,(Finset.univ.filter fun i => (x i:ℝ)≤t).card≤
      (Finset.univ.filter fun i => (y i:ℝ)≤t+δ).card)
    (hyx : ∀ t : ℝ,(Finset.univ.filter fun i => (y i:ℝ)≤t).card≤
      (Finset.univ.filter fun i => (x i:ℝ)≤t+δ).card) :
    ∃ e : Equiv.Perm (Fin n),∀ i,dist (x i) (y (e i))≤δ := by
  obtain ⟨e,he⟩ := permutation_of_cumulative_counts (fun i=>(x i:ℝ)) (fun i=>(y i:ℝ)) δ hxy hyx
  exact ⟨e,he⟩

 theorem pointwise_unitary_matching (x y : Fin n → Interval) (δ : ℝ)
    (hxy : ∀ t : ℝ,(Finset.univ.filter fun i => (x i:ℝ)≤t).card≤
      (Finset.univ.filter fun i => (y i:ℝ)≤t+δ).card)
    (hyx : ∀ t : ℝ,(Finset.univ.filter fun i => (y i:ℝ)≤t).card≤
      (Finset.univ.filter fun i => (x i:ℝ)≤t+δ).card) :
    ∃ u : unitary (CStarMatrix (ι×Fin n) (ι×Fin n) ℂ),
      ∀ (f : Interval → CStarMatrix ι ι ℂ) (η : ℝ),0≤η →
        (∀ s t,dist s t≤δ → ‖f s-f t‖≤η) →
        ‖unitaryConjugation u (blockDiagonalHom (fun i=>f (x i)))-
          blockDiagonalHom (fun i=>f (y i))‖≤η := by
  obtain ⟨e,he⟩ := interval_matching_of_cumulative x y δ hxy hyx
  refine ⟨permutationUnitary (Equiv.prodCongr (Equiv.refl ι) e),?_⟩
  intro f η hη hf
  rw [permutationUnitary_conjugation,reindex_blockDiagonal,←map_sub]
  apply (NonUnitalStarAlgHom.norm_apply_le
    (blockDiagonalHom : (Fin n → CStarMatrix ι ι ℂ) →⋆ₐ[ℂ]
      CStarMatrix (ι×Fin n) (ι×Fin n) ℂ) _).trans
  apply (pi_norm_le_iff_of_nonneg hη).mpr
  intro i
  apply hf
  simpa only [Equiv.apply_symm_apply] using he (e.symm i)

 theorem finite_matrix_tensor_flip (a : CStarMatrix ι ι ℂ) :
    unitaryConjugation (permutationUnitary (Equiv.prodComm ι ι))
      (CStarMatrix.ofMatrix (CStarMatrix.ofMatrix.symm a ⊗ₖ (1 : Matrix ι ι ℂ)))=
      CStarMatrix.ofMatrix ((1 : Matrix ι ι ℂ) ⊗ₖ CStarMatrix.ofMatrix.symm a) := by
  rw [permutationUnitary_conjugation]
  ext ⟨i,j⟩ ⟨k,l⟩
  change a j l*(1 : Matrix ι ι ℂ) i k=(1 : Matrix ι ι ℂ) i k*a j l
  exact mul_comm _ _

end JiangSuConstruction


namespace JiangSuConstruction
open scoped CStarAlgebra ComplexOrder Kronecker

lemma conjugation_near_commuting {A : Type*} [CStarAlgebra A]
    (u : unitary A) (a b : A) (hb : Commute (u:A) b) :
    ‖unitaryConjugation u a-a‖≤2*‖a-b‖ := by
  have he : unitaryConjugation u b=b := by
    change (u:A)*b*star (u:A)=b
    rw [hb.eq,mul_assoc,u.2.2,mul_one]
  have hd : ‖unitaryConjugation u a-unitaryConjugation u b‖≤‖a-b‖ := by
    rw [←map_sub]
    exact NonUnitalStarAlgHom.norm_apply_le (unitaryConjugation u) (a-b)
  have ht := norm_sub_le_norm_sub_add_norm_sub (unitaryConjugation u a) b a
  rw [he] at hd
  rw [norm_sub_rev b a] at ht
  calc
    ‖unitaryConjugation u a-a‖ ≤ ‖unitaryConjugation u a-b‖ + ‖a-b‖ := ht
    _ ≤ ‖a-b‖ + ‖a-b‖ := add_le_add hd le_rfl
    _ = 2 * ‖a-b‖ := (two_mul _).symm

lemma amplification_commute (p n : ℕ) (a : Mat p) (b : Mat n) :
    Commute (rightAmplification p n b) (leftAmplification p n a) := by
  change ((1 : Matrix (Fin p) (Fin p) ℂ) ⊗ₖ CStarMatrix.ofMatrix.symm b) *
    (CStarMatrix.ofMatrix.symm a ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) =
    (CStarMatrix.ofMatrix.symm a ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) *
    ((1 : Matrix (Fin p) (Fin p) ℂ) ⊗ₖ CStarMatrix.ofMatrix.symm b)
  rw [←Matrix.mul_kronecker_mul,←Matrix.mul_kronecker_mul]
  simp only [one_mul,mul_one]

lemma blockDiagonal_constant (p n : ℕ) (a : Mat p) :
    blockDiagonalHom (fun _ : Fin n => a)=leftAmplification p n a := by
  ext ⟨i,k⟩ ⟨j,l⟩
  change Matrix.blockDiagonal (fun _ : Fin n => CStarMatrix.ofMatrix.symm a) (i,k) (j,l)=
    a i j*(1 : Matrix (Fin n) (Fin n) ℂ) k l
  by_cases h : k=l
  · subst l; simp
  · simp [Matrix.blockDiagonal_apply,h]

 def amplifiedUnitary (p n : ℕ) (u : unitary (Mat n)) : unitary (TensorMat p n) :=
   ⟨rightAmplification p n u,Unitary.map_mem (rightAmplification p n) u.2⟩

lemma amplifiedUnitary_continuous (p n : ℕ) : Continuous (amplifiedUnitary p n) := by
  exact ((map_continuous (rightAmplification p n)).comp continuous_subtype_val).subtype_mk _

theorem cluster_path_control (p n : ℕ) (v w : unitary (Mat n)) :
    ∃ γ : Path (amplifiedUnitary p n v) (amplifiedUnitary p n w),
      ∀ (f : Interval → Mat p) (x : Fin n → Interval) (c : Interval) (η : ℝ),
        0≤η → (∀ i,‖f (x i)-f c‖≤η) →
        ∀ t,‖unitaryConjugation (γ t) (blockDiagonalHom (fun i=>f (x i)))-
          blockDiagonalHom (fun i=>f (x i))‖≤2*η := by
  let γ := (finiteMatrixUnitaryPath v w).map (amplifiedUnitary_continuous p n)
  refine ⟨γ,?_⟩
  intro f x c η hη hf t
  have hc : Commute ((γ t : unitary (TensorMat p n)) : TensorMat p n)
      (leftAmplification p n (f c)) :=
    amplification_commute p n (f c) ((finiteMatrixUnitaryPath v w) t)
  apply (conjugation_near_commuting (γ t) _ _ hc).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤2)
  rw [←blockDiagonal_constant p n,←map_sub]
  apply (NonUnitalStarAlgHom.norm_apply_le
    (blockDiagonalHom : (Fin n → Mat p) →⋆ₐ[ℂ] TensorMat p n) _).trans
  exact (pi_norm_le_iff_of_nonneg hη).mpr hf

end JiangSuConstruction


namespace JiangSuConstruction
open Complex NormedSpace selfAdjoint Unitary
open scoped CStarAlgebra ComplexOrder

lemma unitary_star_commute {A : Type*} [CStarAlgebra A]
    (u : unitary A) {b : A} (h : Commute (u:A) b) : Commute (star (u:A)) b := by
  have hh := congrArg (fun x : A => star (u:A)*x*star (u:A)) h.eq
  have hu := u.2.1
  have hv := u.2.2
  simp only [← mul_assoc,hu,one_mul] at hh
  have he : star (u:A)*b*(u:A)*star (u:A)=star (u:A)*b := by
    rw [mul_assoc, hv, mul_one]
  rw [he] at hh
  exact hh.symm

lemma unitary_argument_commute {A : Type*} [CStarAlgebra A]
    (u : unitary A) {b : A} (h : Commute (u:A) b) :
    Commute (argSelfAdjoint u : A) b := by
  rw [argSelfAdjoint_coe]
  exact h.cfc (unitary_star_commute u h) _

def finiteSpectrumLogPath {A : Type*} [CStarAlgebra A]
    (u : unitary A) (hf : (spectrum ℂ (u:A)).Finite) : Path 1 u where
  toFun t := expUnitary ((t:ℝ) • argSelfAdjoint u)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simpa using finite_spectrum_unitary_exp u hf

lemma finiteSpectrumLogPath_commute {A : Type*} [CStarAlgebra A]
    (u : unitary A) (hf : (spectrum ℂ (u:A)).Finite) {b : A}
    (h : Commute (u:A) b) (t : unitInterval) :
    Commute (finiteSpectrumLogPath u hf t : A) b := by
  change Commute (exp (I • (((t:ℝ) • argSelfAdjoint u : selfAdjoint A) : A))) b
  change Commute (exp (I • ((t:ℝ) • (argSelfAdjoint u : A)))) b
  exact (((unitary_argument_commute u h).smul_left (t:ℝ)).smul_left I).exp_left

theorem finiteSpectrumLogPath_control {A : Type*} [CStarAlgebra A]
    (u : unitary A) (hf : (spectrum ℂ (u:A)).Finite) (a b : A)
    (h : Commute (u:A) b) (t : unitInterval) :
    ‖unitaryConjugation (finiteSpectrumLogPath u hf t) a-a‖≤2*‖a-b‖ :=
  conjugation_near_commuting _ a b (finiteSpectrumLogPath_commute u hf h t)

end JiangSuConstruction

end

end OAI
