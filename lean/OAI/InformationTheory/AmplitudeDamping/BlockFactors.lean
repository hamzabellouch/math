import OAI.InformationTheory.AmplitudeDamping.EntropyContinuity

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

section
variable {ι : Type u_1} {μ : Type u_2} [Fintype ι] [Fintype μ] [DecidableEq ι] [DecidableEq μ]

def blockUnitary (U : μ → Matrix.unitaryGroup ι ℂ) : Matrix.unitaryGroup (ι × μ) ℂ :=
  ⟨Matrix.blockDiagonal (fun m ↦ U m), by
    constructor
    · change (Matrix.blockDiagonal _)ᴴ*Matrix.blockDiagonal _=1
      rw [Matrix.blockDiagonal_conjTranspose,← Matrix.blockDiagonal_mul]
      simp only [← Matrix.star_eq_conjTranspose,Unitary.coe_star_mul_self]
      exact Matrix.blockDiagonal_one
    · change Matrix.blockDiagonal _*(Matrix.blockDiagonal _)ᴴ=1
      rw [Matrix.blockDiagonal_conjTranspose,← Matrix.blockDiagonal_mul]
      simp only [← Matrix.star_eq_conjTranspose,← Unitary.coe_star,Unitary.coe_mul_star_self]
      exact Matrix.blockDiagonal_one⟩

theorem entropy_blockDiagonal (A : μ → Matrix ι ι ℂ) (hA : ∀ m, (A m).IsHermitian) :
    entropy (Matrix.blockDiagonal A)=∑ m, entropy (A m) := by
  let U := blockUnitary (fun m ↦ (hA m).eigenvectorUnitary)
  let d : ι × μ → ℝ := fun im ↦ (hA im.2).eigenvalues im.1
  have he : Matrix.blockDiagonal A=Unitary.conjStarAlgAut ℂ _ U (Matrix.diagonal (fun im ↦ (d im:ℂ))) := by
    rw [Unitary.conjStarAlgAut_apply]
    change Matrix.blockDiagonal A=Matrix.blockDiagonal _*Matrix.diagonal _*(Matrix.blockDiagonal _)ᴴ
    dsimp only [d]
    rw [← Matrix.blockDiagonal_diagonal (fun m i ↦ ((hA m).eigenvalues i:ℂ)),Matrix.blockDiagonal_conjTranspose,
      ← Matrix.blockDiagonal_mul,← Matrix.blockDiagonal_mul]
    congr 1; funext m
    exact (hA m).spectral_theorem
  have hh : (Matrix.diagonal (fun im ↦ (d im:ℂ))).IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro im; exact Complex.conj_ofReal _
  rw [he,entropy_unitary_conj U hh,entropy_diagonal,Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  exact (entropy_eq_sum (hA m)).symm

end

variable {ι : Type u_3} {κ : Type u_4} {μ : Type u_5} [Fintype ι] [Fintype κ] [Fintype μ]
  [DecidableEq ι] [DecidableEq μ]

def blockProjection (m : μ) : Matrix (ι × μ) (ι × μ) ℂ :=
  Matrix.diagonal (fun im ↦ if im.2=m then 1 else 0)

def blockInjection (m : μ) : Matrix (ι × μ) ι ℂ :=
  fun ia j ↦ if ia.2=m then if ia.1=j then 1 else 0 else 0

theorem blockProjection_isProjection (m : μ) : IsProjection (blockProjection (ι := ι) m) := by
  constructor
  · apply Matrix.isHermitian_diagonal_iff.mpr
    intro im; split_ifs <;> simp
  · rw [blockProjection,Matrix.diagonal_mul_diagonal]
    congr 1; funext im; split_ifs <;> simp

omit [Fintype κ] in
theorem blockProjection_mul (m : μ) (X : Matrix (ι × μ) κ ℂ) (ia : ι × μ) (j : κ) :
    (blockProjection (ι := ι) m*X) ia j=if ia.2=m then X ia j else 0 := by
  simp [blockProjection,Matrix.diagonal_mul]

omit [Fintype κ] [Fintype μ] in
theorem blockInjection_mul (m : μ) (X : Matrix ι κ ℂ) (ia : ι × μ) (j : κ) :
    (blockInjection (ι := ι) m*X) ia j=if ia.2=m then X ia.1 j else 0 := by
  simp [blockInjection,Matrix.mul_apply,ite_mul]

theorem blockInjection_isometry (m : μ) :
    (blockInjection (ι := ι) m)ᴴ*blockInjection (ι := ι) m=1 := by
  ext i j
  simp only [Matrix.mul_apply,Fintype.sum_prod_type,Matrix.conjTranspose_apply,blockInjection]
  simp [Matrix.one_apply,eq_comm]

omit [Fintype κ] in
theorem blockProjection_range {m : μ} {X : Matrix (ι × μ) κ ℂ}
    (hX : blockProjection (ι := ι) m*X=X) : blockInjection (ι := ι) m*(show Matrix ι κ ℂ from fun i j ↦ X (i,m) j)=X := by
  ext ia j
  have h := congrArg (fun A : Matrix (ι × μ) κ ℂ ↦ A ia j) hX
  rw [blockProjection_mul] at h
  rw [blockInjection_mul]
  split_ifs with hm
  · cases ia with | mk i a => change a=m at hm; subst a; rfl
  · simpa only [ite_eq_right hm] using h

theorem mass_isometry {ρ : Type u_6} [Fintype ρ] (W : Matrix ρ ι ℂ)
    (hW : Wᴴ*W=1) (X : Matrix ι κ ℂ) : mass (W*X)=mass X := by
  dsimp [mass,gram]
  rw [Matrix.conjTranspose_mul,Matrix.trace_mul_comm]
  have h : Xᴴ*Wᴴ*(W*X)=Xᴴ*X := by
    rw [← Matrix.mul_assoc _ W,Matrix.mul_assoc Xᴴ, hW,Matrix.mul_one]
  rw [h,Matrix.trace_mul_comm]

theorem entropy_gram_isometry {ρ : Type u_7} [Fintype ρ] [DecidableEq ρ] [DecidableEq κ]
    (W : Matrix ρ ι ℂ) (hW : Wᴴ*W=1) (X : Matrix ι κ ℂ) :
    entropy (gram (W*X))=entropy (gram X) := by
  change entropy ((W*X)*(W*X)ᴴ)=entropy (X*Xᴴ)
  rw [entropy_mul_conjTranspose,entropy_mul_conjTranspose X,Matrix.conjTranspose_mul]
  congr 1
  rw [← Matrix.mul_assoc _ W,Matrix.mul_assoc Xᴴ,hW,Matrix.mul_one]

theorem block_factor_entropy [DecidableEq κ] (m : μ) (X : Matrix ι κ ℂ) :
    entropy (gram (blockInjection (ι := ι) m*X))=entropy (gram X) :=
  entropy_gram_isometry _ (blockInjection_isometry m) X

omit [Fintype μ] in
theorem gram_blockInjection (m : μ) (X : Matrix ι κ ℂ) (ia jb : ι × μ) :
    gram (blockInjection (ι := ι) m*X) ia jb=
      if ia.2=m ∧ jb.2=m then gram X ia.1 jb.1 else 0 := by
  change (∑ k, (blockInjection (ι := ι) m*X) ia k*star ((blockInjection (ι := ι) m*X) jb k)) = _
  simp only [blockInjection_mul]
  by_cases hi : ia.2=m <;> by_cases hj : jb.2=m <;>
    simp [hi,hj,gram,Matrix.mul_apply,Matrix.conjTranspose_apply]

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_8} [Fintype ι] [DecidableEq ι]

theorem trace_product_nonneg {A B : Matrix ι ι ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A*B).trace.re := by
  let L := spectralFactor hB
  have hL : L*Lᴴ=B := spectralFactor_gram hB
  have h := (hA.conjTranspose_mul_mul_same L).trace_nonneg
  rw [Matrix.trace_mul_cycle] at h
  rw [hL] at h
  simpa only [Matrix.trace_mul_comm B A] using (Complex.nonneg_iff.mp h).1

theorem trace_product_mono {P A B : Matrix ι ι ℂ} (hP : P.PosSemidef)
    (hAB : (B-A).PosSemidef) : (P*A).trace.re ≤ (P*B).trace.re := by
  have h := trace_product_nonneg hP hAB
  simpa only [Matrix.mul_sub,Matrix.trace_sub,Complex.sub_re,sub_nonneg] using h

theorem IsState.le_one {A : Matrix ι ι ℂ} (hA : IsState A) : (1-A).PosSemidef := by
  let U := hA.1.isHermitian.eigenvectorUnitary
  let l := hA.1.isHermitian.eigenvalues
  have hl : ∀ i, l i ≤ 1 := by
    intro i
    rw [← spectral_weights_sum hA]
    exact Finset.single_le_sum (fun j _ ↦ hA.1.eigenvalues_nonneg j) (Finset.mem_univ i)
  have hd : (Matrix.diagonal (fun i ↦ ((1-l i:ℝ):ℂ))).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    change (0:ℂ) ≤ ((1-l i:ℝ):ℂ)
    exact_mod_cast sub_nonneg.mpr (hl i)
  have he : 1-A=U.val*Matrix.diagonal (fun i ↦ ((1-l i:ℝ):ℂ))*U.valᴴ := by
    have hs := hA.1.isHermitian.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at hs
    have hd' : Matrix.diagonal (fun i ↦ ((1-l i:ℝ):ℂ))=1-Matrix.diagonal (fun i ↦ (l i:ℂ)) := by
      ext i j
      by_cases h : i=j <;> simp [h]
    rw [hd',Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one]
    have hu : U.val*U.valᴴ=1 := by
      change U.val*star U.val=1
      exact Unitary.mul_star_self_of_mem U.prop
    rw [hu]
    exact congrArg (fun M ↦ 1-M) hs
  rw [he]
  exact hd.mul_mul_conjTranspose_same _

theorem state_measurement_prob_le_trace {A D : Matrix ι ι ℂ} (hA : IsState A)
    (hD : D.PosSemidef) : (D*A).trace.re ≤ D.trace.re := by
  simpa only [Matrix.mul_one] using trace_product_mono hD hA.le_one

end GAD

end

end OAI
