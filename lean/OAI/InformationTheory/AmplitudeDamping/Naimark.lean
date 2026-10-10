import OAI.InformationTheory.AmplitudeDamping.BlockFactors

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_1} {μ : Type u_2} [Fintype ι] [Fintype μ] [DecidableEq ι] [DecidableEq μ]

def naimark (D : μ → Matrix ι ι ℂ) (hD : ∀ m, (D m).PosSemidef) : Matrix (ι × μ) ι ℂ :=
  fun im j ↦ star (spectralFactor (hD im.2) j im.1)

omit [DecidableEq μ] in
theorem naimark_isometry (D : μ → Matrix ι ι ℂ) (hD : ∀ m, (D m).PosSemidef)
    (hDs : ∑ m, D m=1) : (naimark D hD)ᴴ*naimark D hD=1 := by
  rw [← hDs]
  ext i j
  simp only [Matrix.mul_apply,Fintype.sum_prod_type,Matrix.conjTranspose_apply,naimark,star_star,
    Matrix.sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  exact congrArg (fun A : Matrix ι ι ℂ ↦ A i j) (spectralFactor_gram (hD m))

theorem naimark_block (D : μ → Matrix ι ι ℂ) (hD : ∀ m, (D m).PosSemidef)
    (X : Matrix ι ι ℂ) (m : μ) :
    blockProjection (ι := ι) m*(naimark D hD*X)=
      blockInjection (ι := ι) m*((spectralFactor (hD m))ᴴ*X) := by
  ext im j
  rw [blockProjection_mul,blockInjection_mul]
  split_ifs with h
  · simp only [Matrix.mul_apply,naimark,h,Matrix.conjTranspose_apply]
  · rfl

theorem naimark_success (D : μ → Matrix ι ι ℂ) (hD : ∀ m, (D m).PosSemidef)
    (X : Matrix ι ι ℂ) (m : μ) :
    mass (blockProjection (ι := ι) m*(naimark D hD*X))=(D m*gram X).trace.re := by
  rw [naimark_block,mass_isometry _ (blockInjection_isometry m)]
  dsimp only [mass,gram]
  rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.trace_mul_cycle]
  have hF : spectralFactor (hD m)*(spectralFactor (hD m))ᴴ=D m := spectralFactor_gram (hD m)
  rw [Matrix.mul_assoc Xᴴ (spectralFactor (hD m)) _,hF,Matrix.trace_mul_cycle,Matrix.trace_mul_comm (X*Xᴴ)]

theorem blockProjection_injection (m : μ) (X : Matrix ι ι ℂ) :
    blockProjection (ι := ι) m*(blockInjection (ι := ι) m*X)=blockInjection (ι := ι) m*X := by
  ext im j
  rw [blockProjection_mul,blockInjection_mul]
  split_ifs <;> rfl

/-- Approximate orthogonalization of well decoded states in a Naimark dilation. -/
theorem exists_orthogonal_factors (A D : μ → Matrix ι ι ℂ)
    (hA : ∀ m, IsState (A m)) (hD : ∀ m, (D m).PosSemidef) (hDs : ∑ m, D m=1) :
    ∃ Y : μ → Matrix (ι × μ) ι ℂ,
      (∀ m, mass (Y m)=1) ∧ (∀ m, blockProjection (ι := ι) m*Y m=Y m) ∧
      (∀ m, mass (naimark D hD*spectralFactor (hA m).1-Y m) ≤ 2*(1-(D m*A m).trace.re)) := by
  have hm (m : μ) : mass (spectralFactor (hA m).1)=1 := by
    dsimp [mass]
    rw [spectralFactor_gram,(hA m).2,Complex.one_re]
  have hy (m : μ) := exists_projected_factor (blockProjection_isProjection m)
    (naimark D hD*spectralFactor (hA m).1) (blockInjection (ι := ι) m*spectralFactor (hA m).1)
    (by rw [mass_isometry _ (naimark_isometry D hD hDs),hm])
    (by rw [mass_isometry _ (blockInjection_isometry m),hm])
    (blockProjection_injection m _)
  choose Y hY hPY hd using hy
  refine ⟨Y,hY,hPY,fun m ↦ ?_⟩
  simpa only [naimark_success,spectralFactor_gram] using hd m

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_3} {κ : Type u_4} {μ : Type u_5} [Fintype ι] [Fintype κ] [Fintype μ]

def concatenate (w : μ → ℝ) (X : μ → Matrix ι κ ℂ) : Matrix ι (μ × κ) ℂ :=
  fun i mk ↦ (Real.sqrt (w mk.1):ℂ)*X mk.1 i mk.2

omit [Fintype ι] in
theorem gram_concatenate (w : μ → ℝ) (X : μ → Matrix ι κ ℂ) (hw : ∀ m, 0 ≤ w m) :
    gram (concatenate w X)=∑ m, w m • gram (X m) := by
  ext i j
  simp only [gram,Matrix.mul_apply,Matrix.conjTranspose_apply,concatenate,
    Fintype.sum_prod_type,Matrix.sum_apply,Matrix.smul_apply,Complex.real_smul,
    star_mul,Complex.star_def,Complex.conj_ofReal,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro k _
  have hs : (Real.sqrt (w m):ℂ)^2=(w m:ℂ) := by exact_mod_cast Real.sq_sqrt (hw m)
  linear_combination X m i k*(starRingEnd ℂ) (X m j k)*hs

theorem mass_concatenate (w : μ → ℝ) (X : μ → Matrix ι κ ℂ) (hw : ∀ m, 0 ≤ w m) :
    mass (concatenate w X)=∑ m, w m*mass (X m) := by
  simp only [mass,gram_concatenate w X hw,Matrix.trace_sum,Matrix.trace_smul,
    Complex.re_sum,Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]

omit [Fintype ι] [Fintype κ] [Fintype μ] in
theorem concatenate_sub (w : μ → ℝ) (X Y : μ → Matrix ι κ ℂ) :
    concatenate w X-concatenate w Y=concatenate w (fun m ↦ X m-Y m) := by
  ext i mk
  simp [concatenate,mul_sub]

theorem concatenate_mass_one (w : μ → ℝ) (X : μ → Matrix ι κ ℂ)
    (hw : ∀ m, 0 ≤ w m) (hws : ∑ m, w m=1) (hX : ∀ m, mass (X m)=1) :
    mass (concatenate w X)=1 := by
  rw [mass_concatenate w X hw]
  simp only [hX,mul_one,hws]

variable [DecidableEq ι] [DecidableEq κ] [DecidableEq μ]

theorem orthogonal_factor_entropy (w : μ → ℝ) (Y : μ → Matrix (ι × μ) κ ℂ)
    (hY : ∀ m, mass (Y m)=1) (hPY : ∀ m, blockProjection (ι := ι) m*Y m=Y m) :
    entropy (∑ m, w m • gram (Y m))=
      ∑ m, (w m*entropy (gram (Y m))+Real.negMulLog (w m)) := by
  let Z : μ → Matrix ι κ ℂ := fun m i k ↦ Y m (i,m) k
  have hZ (m : μ) : blockInjection (ι := ι) m*Z m=Y m := blockProjection_range (hPY m)
  have hmZ (m : μ) : mass (Z m)=1 := by
    rw [← mass_isometry _ (blockInjection_isometry m),hZ,hY]
  have he : (∑ m, w m • gram (Y m))=Matrix.blockDiagonal (fun m ↦ w m • gram (Z m)) := by
    ext ia jb
    simp only [Matrix.sum_apply,Matrix.smul_apply,← hZ,gram_blockInjection,Matrix.blockDiagonal_apply]
    by_cases h : ia.2=jb.2
    · simp only [h,and_self]
      simp
    · have hf (m : μ) : ¬(ia.2=m ∧ jb.2=m) := by intro hm; exact h (hm.1.trans hm.2.symm)
      simp [hf,h]
  rw [he,entropy_blockDiagonal _ (fun m ↦ (gram_posSemidef (Z m)).isHermitian.smul (IsSelfAdjoint.all (w m)))]
  apply Finset.sum_congr rfl
  intro m _
  rw [entropy_smul _ (gram_posSemidef (Z m)).isHermitian,gram_trace,hmZ]
  simp only [Complex.ofReal_one,Complex.one_re,mul_one]
  rw [← hZ,block_factor_entropy]

end GAD

end

end OAI
