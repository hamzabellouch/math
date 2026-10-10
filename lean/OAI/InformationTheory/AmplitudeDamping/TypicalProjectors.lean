import OAI.InformationTheory.AmplitudeDamping.TypicalSets

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

theorem tensorMatrix_mul {n : ℕ} (A B : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    tensorMatrix n A * tensorMatrix n B = tensorMatrix n (fun k ↦ A k*B k) := by
  ext i j
  simp only [tensorMatrix,Matrix.mul_apply,← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun k l ↦ A k (i k) l*B k l (j k))).symm

theorem tensorMatrix_conjTranspose {n : ℕ} (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    (tensorMatrix n A)ᴴ=tensorMatrix n (fun k ↦ (A k)ᴴ) := by
  ext i j
  simp [tensorMatrix,Matrix.conjTranspose_apply]

theorem tensorMatrix_diagonal {n : ℕ} (a : Fin n → Fin 2 → ℂ) :
    tensorMatrix n (fun k ↦ Matrix.diagonal (a k))=Matrix.diagonal (fun i ↦ ∏ k, a k (i k)) := by
  ext i j
  by_cases hij : i=j
  · subst j; simp [tensorMatrix]
  · rw [Matrix.diagonal_apply_ne _ hij]
    have hx : ∃ k, i k ≠ j k := by simpa only [not_forall,funext_iff] using hij
    obtain ⟨k,hk⟩ := hx
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    exact Matrix.diagonal_apply_ne _ hk

theorem tensorMatrix_one {n : ℕ} : tensorMatrix n (fun _ ↦ (1 : Matrix (Fin 2) (Fin 2) ℂ))=1 := by
  have h := tensorMatrix_diagonal (fun _ : Fin n ↦ fun _ : Fin 2 ↦ (1:ℂ))
  simpa using h

def tensorEigenUnitary {n : ℕ} (U : Fin n → Matrix.unitaryGroup (Fin 2) ℂ) :
    Matrix.unitaryGroup (Basis n) ℂ :=
  ⟨tensorMatrix n (fun k ↦ U k), by
    constructor
    · change (tensorMatrix n _)ᴴ*tensorMatrix n _=1
      rw [tensorMatrix_conjTranspose,tensorMatrix_mul]
      simp only [← Matrix.star_eq_conjTranspose,Unitary.coe_star_mul_self]
      exact tensorMatrix_one
    · change tensorMatrix n _*(tensorMatrix n _)ᴴ=1
      rw [tensorMatrix_conjTranspose,tensorMatrix_mul]
      simp only [← Matrix.star_eq_conjTranspose,← Unitary.coe_star,Unitary.coe_mul_star_self]
      exact tensorMatrix_one⟩

variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

def spectralMatrix (U : Matrix.unitaryGroup ι ℂ) (q : ι → ℝ) : Matrix ι ι ℂ :=
  Unitary.conjStarAlgAut ℂ _ U (Matrix.diagonal (fun i ↦ (q i:ℂ)))

theorem spectralMatrix_hermitian (U : Matrix.unitaryGroup ι ℂ) (q : ι → ℝ) :
    (spectralMatrix U q).IsHermitian := by
  apply Matrix.isHermitian_mul_mul_conjTranspose
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i; exact Complex.conj_ofReal _

theorem spectralMatrix_posSemidef (U : Matrix.unitaryGroup ι ℂ) (q : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i) : (spectralMatrix U q).PosSemidef := by
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.PosSemidef.diagonal
  intro i
  change (0:ℂ) ≤ (q i:ℂ)
  exact_mod_cast hq i

theorem spectralMatrix_trace (U : Matrix.unitaryGroup ι ℂ) (q : ι → ℝ) :
    (spectralMatrix U q).trace=(∑ i, q i:ℝ) := by
  rw [spectralMatrix,trace_unitary_conj,Matrix.trace_diagonal]
  simp

theorem spectralMatrix_entropy (U : Matrix.unitaryGroup ι ℂ) (q : ι → ℝ) :
    entropy (spectralMatrix U q)=∑ i, Real.negMulLog (q i) := by
  rw [spectralMatrix,entropy_unitary_conj]
  · exact entropy_diagonal q
  · apply Matrix.isHermitian_diagonal_iff.mpr
    intro i; exact Complex.conj_ofReal _

theorem spectralMatrix_mul (U : Matrix.unitaryGroup ι ℂ) (q r : ι → ℝ) :
    spectralMatrix U q*spectralMatrix U r=spectralMatrix U (fun i ↦ q i*r i) := by
  rw [spectralMatrix,spectralMatrix,← map_mul,Matrix.diagonal_mul_diagonal]
  congr 2; funext i; exact (Complex.ofReal_mul _ _).symm

theorem spectralMatrix_sub (U : Matrix.unitaryGroup ι ℂ) (q r : ι → ℝ) :
    spectralMatrix U q-spectralMatrix U r=spectralMatrix U (fun i ↦ q i-r i) := by
  rw [spectralMatrix,spectralMatrix,← map_sub]
  congr 1
  ext i j
  by_cases h : i=j <;> simp [h]

theorem spectralMatrix_smul (U : Matrix.unitaryGroup ι ℂ) (c : ℝ) (q : ι → ℝ) :
    c • spectralMatrix U q=spectralMatrix U (fun i ↦ c*q i) := by
  simp only [spectralMatrix,Unitary.conjStarAlgAut_apply]
  rw [← Matrix.smul_mul,← Matrix.mul_smul]
  congr 2
  ext i j
  simp [Matrix.diagonal_apply,Complex.real_smul]

def spectralMask (U : Matrix.unitaryGroup ι ℂ) (s : Finset ι) : Matrix ι ι ℂ :=
  spectralMatrix U (fun i ↦ if i ∈ s then 1 else 0)

theorem spectralMask_projection (U : Matrix.unitaryGroup ι ℂ) (s : Finset ι) :
    IsProjection (spectralMask U s) := by
  refine ⟨spectralMatrix_hermitian _ _, ?_⟩
  rw [spectralMask,spectralMatrix_mul]
  congr 1; funext i; split_ifs <;> simp

theorem spectralMask_trace (U : Matrix.unitaryGroup ι ℂ) (s : Finset ι) :
    (spectralMask U s).trace=(s.card:ℂ) := by
  rw [spectralMask,spectralMatrix_trace]
  simp

theorem spectralMask_compress (U : Matrix.unitaryGroup ι ℂ) (q : ι → ℝ) (s : Finset ι) :
    spectralMask U s*spectralMatrix U q*spectralMask U s=
      spectralMatrix U (fun i ↦ if i ∈ s then q i else 0) := by
  rw [spectralMask,spectralMatrix_mul,spectralMatrix_mul]
  congr 1; funext i; split_ifs <;> simp

theorem spectralMask_compress_bound (U : Matrix.unitaryGroup ι ℂ) (q : ι → ℝ) (s : Finset ι)
    {c : ℝ} (hc : ∀ i ∈ s, q i ≤ c) :
    (c • spectralMask U s-spectralMask U s*spectralMatrix U q*spectralMask U s).PosSemidef := by
  rw [spectralMask_compress,spectralMask,spectralMatrix_smul,spectralMatrix_sub]
  apply spectralMatrix_posSemidef
  intro i
  split_ifs with hi
  · simpa using sub_nonneg.mpr (hc i hi)
  · simp

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

theorem tensor_spectralMatrix (n : ℕ) (U : Fin n → Matrix.unitaryGroup (Fin 2) ℂ)
    (q : Fin 2 → ℝ) :
    tensorMatrix n (fun k ↦ spectralMatrix (U k) q)=
      spectralMatrix (tensorEigenUnitary U) (iidWeight q n) := by
  dsimp only [spectralMatrix,Unitary.conjStarAlgAut_apply,tensorEigenUnitary]
  simp only [iidWeight,Complex.ofReal_prod,Matrix.star_eq_conjTranspose]
  rw [← tensorMatrix_diagonal (fun _ : Fin n ↦ fun i : Fin 2 ↦ (q i:ℂ)),
    tensorMatrix_conjTranspose, tensorMatrix_mul,tensorMatrix_mul]

theorem projection_gram_mass {ι : Type u_2} {κ : Type u_3} [Fintype ι] [Fintype κ]
    {P : Matrix ι ι ℂ} (hP : IsProjection P) (F : Matrix ι κ ℂ) :
    mass (P*F)=(P*gram F).trace.re := by
  rw [← projection_inner hP F,frobVector_inner]
  dsimp [gram]
  rw [← Matrix.mul_assoc,Matrix.trace_mul_cycle,Matrix.trace_mul_comm (F*Fᴴ)]

variable {ι : Type u_4} [Fintype ι] [DecidableEq ι]

theorem spectralMask_mass (U : Matrix.unitaryGroup ι ℂ) (q : ι → ℝ) (s : Finset ι) :
    (spectralMask U s*spectralMatrix U q).trace.re=∑ i ∈ s, q i := by
  rw [spectralMask,spectralMatrix_mul,spectralMatrix_trace,Complex.ofReal_re]
  simp [ite_mul]

theorem spectralMask_loss (U : Matrix.unitaryGroup ι ℂ) (q : ι → ℝ) (s : Finset ι)
    (hs : ∑ i, q i=1) :
    1-(spectralMask U s*spectralMatrix U q).trace.re=∑ i, if i ∈ s then 0 else q i := by
  rw [spectralMask_mass,← hs]
  have he : (∑ i, q i)=(∑ i ∈ s, q i)+(∑ i, if i ∈ s then 0 else q i) := by
    calc
      _ = ∑ i, ((if i ∈ s then q i else 0)+(if i ∈ s then 0 else q i)) := by
        apply Finset.sum_congr rfl
        intro i _; split_ifs <;> simp
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  linarith

def typicalProjection (n : ℕ) (U : Fin n → Matrix.unitaryGroup (Fin 2) ℂ)
    (q : Fin 2 → ℝ) (δ : ℝ) : QMatrix n :=
  spectralMask (tensorEigenUnitary U) (typicalSet q δ n)

theorem typicalProjection_properties (n : ℕ) (U : Fin n → Matrix.unitaryGroup (Fin 2) ℂ)
    (q : Fin 2 → ℝ) (hq : ∀ i, 0 ≤ q i) (hs : ∑ i, q i=1)
    {δ : ℝ} (hδ : 0 < δ) (hn : 0 < n) :
    IsProjection (typicalProjection n U q δ) ∧
    (typicalProjection n U q δ).trace.re ≤ Real.exp ((n:ℝ)*(classicalEntropy q+δ)) ∧
    1-(typicalProjection n U q δ*tensorMatrix n (fun k ↦ spectralMatrix (U k) q)).trace.re ≤
      logVariance q/((n:ℝ)*δ^2) ∧
    (Real.exp (-(n:ℝ)*(classicalEntropy q-δ)) • typicalProjection n U q δ-
      typicalProjection n U q δ*tensorMatrix n (fun k ↦ spectralMatrix (U k) q)*typicalProjection n U q δ).PosSemidef := by
  classical
  refine ⟨spectralMask_projection _ _, ?_, ?_, ?_⟩
  · rw [typicalProjection,spectralMask_trace,Complex.natCast_re]
    exact typical_card q hq hs δ n
  · rw [tensor_spectralMatrix,typicalProjection,spectralMask_loss _ _ _ (iidWeight_total q hs n)]
    simpa only [typicalSet,Finset.mem_filter,Finset.mem_univ,true_and] using typical_tail q hq hs hδ hn
  · rw [tensor_spectralMatrix,typicalProjection]
    apply spectralMask_compress_bound
    intro x hx
    exact typical_weight_upper q δ n x (Finset.mem_filter.mp hx).2

end GAD

end

end OAI
