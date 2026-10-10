import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.PosLower
import OAI.Analysis.MatrixSigning.Potential.EnergyMatrix
import OAI.Analysis.MatrixSigning.Potential.RowSquareSum

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Covariance
open Matrix WithLp
open scoped BigOperators Matrix.Norms.L2Operator

variable {n : ℕ}

def diagBlock (A B : Mat n) : Mat (2*n) :=
  Matrix.reindex (pairIndex n) (pairIndex n) (Matrix.fromBlocks A 0 0 B)

lemma diagBlock_symm {A B : Mat n} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (diagBlock A B).IsHermitian := by
  exact (Matrix.IsHermitian.fromBlocks hA (by simp) hB).submatrix _

lemma diagBlock_apply_left (A B : Mat n) (v : E (2*n)) (i : Fin n) :
    ((diagBlock A B).toEuclideanLin v) (pairIndex n (.inl i)) = A.toEuclideanLin (fstVec v) i := by
  change (∑ j,diagBlock A B (pairIndex n (.inl i)) j*v j) = _
  rw [sum_pair]
  simp only [diagBlock,Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply,
    Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.zero_apply,zero_mul,
    Finset.sum_const_zero,add_zero]
  rfl

lemma diagBlock_apply_right (A B : Mat n) (v : E (2*n)) (i : Fin n) :
    ((diagBlock A B).toEuclideanLin v) (pairIndex n (.inr i)) = B.toEuclideanLin (sndVec v) i := by
  change (∑ j,diagBlock A B (pairIndex n (.inr i)) j*v j) = _
  rw [sum_pair]
  simp only [diagBlock,Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply,
    Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Matrix.zero_apply,zero_mul,
    Finset.sum_const_zero,zero_add]
  rfl

lemma quad_diagBlock (A B : Mat n) (v : E (2*n)) :
    quad (diagBlock A B) v = quad A (fstVec v)+quad B (sndVec v) := by
  simp only [quad,EuclideanSpace.inner_eq_star_dotProduct,star_trivial,dotProduct]
  rw [sum_pair]
  simp only [diagBlock_apply_left,diagBlock_apply_right]
  rfl

lemma diagBlock_psd {A B : Mat n} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (diagBlock A B).PosSemidef := by
  rw [← Matrix.isPositive_toEuclideanLin_iff]
  refine ⟨Matrix.isSymmetric_toEuclideanLin_iff.mpr (diagBlock_symm hA.1 hB.1),?_⟩
  intro v
  change 0 ≤ inner ℝ ((diagBlock A B).toEuclideanLin v) v
  rw [real_inner_comm v ((diagBlock A B).toEuclideanLin v)]
  change 0 ≤ quad (diagBlock A B) v
  rw [quad_diagBlock]
  apply add_nonneg
  · have hh := (Matrix.isPositive_toEuclideanLin_iff.mpr hA).2 (fstVec v)
    change 0 ≤ inner ℝ (A.toEuclideanLin (fstVec v)) (fstVec v) at hh
    simpa only [quad,real_inner_comm] using hh
  · have hh := (Matrix.isPositive_toEuclideanLin_iff.mpr hB).2 (sndVec v)
    change 0 ≤ inner ℝ (B.toEuclideanLin (sndVec v)) (sndVec v) at hh
    simpa only [quad,real_inner_comm] using hh

lemma diagBlock_diag (A B : Mat n) (i : Fin (2*n)) :
    diagBlock A B i i = pairWeight (fun j => A j j) (fun j => B j j) i := by
  obtain ⟨i,rfl⟩ := (pairIndex n).surjective i
  cases i <;> simp [diagBlock,pairWeight]

end CurrentKS.Covariance

namespace CurrentKS.Interaction
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.State CurrentKS.Covariance Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

lemma coordinate_pos [NeZero d] (A X : H d) (hA : A ∈ psdCone d) (hA0 : A ≠ 0) (hX : X ∈ pd d) :
    0 < inner ℝ A X := by
  have hh := inner_nonneg_of_psd A X hA hX.posSemidef
  apply lt_of_le_of_ne hh
  intro he
  apply hA0
  apply eq_zero_of_inner_pd hX hA
  simpa only [real_inner_comm] using he.symm

lemma interaction_duality_le {c ε : ℝ} (hε : 0 ≤ ε) (A : Fin N → H d) (x : Coordinates N)
    (hA : ∀ i, A i ∈ psdCone d) (hrank : ∀ i, (A i : Hermitian.Mat d).rank ≤ 1)
    (l m : Fin N → ℝ) (hl : ∀ i, 0 ≤ l i) (hlm : ∀ i, l i*m i = psi (x i))
    (X P Q : H d) (hX : X ∈ pd d)
    (hP : sandwich (invH X) P = eta c A x Q+ε • (Hermitian.one : H d)) (i : Fin N) :
    (interaction c A l X *ᵥ (fun j => m j*inner ℝ (A j) Q)) i ≤ l i*inner ℝ (A i) P := by
  rw [interaction_duality c ε A x hA hrank l m hlm X P Q hX hP i]
  exact sub_le_self _ (mul_nonneg (mul_nonneg hε (hl i))
    (inner_nonneg_of_psd _ _ (hA i) (sandwich_psd _ _ one_mem_psdCone)))

lemma interaction_whiten_trace [NeZero d] {c ε : ℝ} (hc : 0 < c) (hε : 0 ≤ ε)
    (A : Fin N → H d) (x : Coordinates N) (hA : ∀ i, A i ∈ psdCone d)
    (hA0 : ∀ i, A i ≠ 0) (hrank : ∀ i, (A i : Hermitian.Mat d).rank ≤ 1)
    (l m : Fin N → ℝ) (hl : ∀ i, 0 < l i) (hm : ∀ i, 0 < m i)
    (hlm : ∀ i, l i*m i = psi (x i))
    (X Y P Q : H d) (hX : X ∈ pd d) (hY : Y ∈ pd d) (hPpos : P ∈ pd d) (hQpos : Q ∈ pd d)
    (hP : sandwich (invH X) P = eta c A x Q+ε • (Hermitian.one : H d))
    (hab : ∀ i, (l i*inner ℝ (A i) X)*(m i*inner ℝ (A i) Y) ≤ c⁻¹^2) :
    let a := fun i => (l i*inner ℝ (A i) X)*(l i*inner ℝ (A i) P)
    let b := fun i => (m i*inner ℝ (A i) Y)*(m i*inner ℝ (A i) Q)
    ((whitenWeighted a b (interaction c A l X)).conjTranspose *
      whitenWeighted a b (interaction c A l X)).trace ≤ (N : ℝ)/c := by
  dsimp only
  have hxp i := coordinate_pos (A i) X (hA i) (hA0 i) hX
  have hyp i := coordinate_pos (A i) Y (hA i) (hA0 i) hY
  have hpp i := coordinate_pos (A i) P (hA i) (hA0 i) hPpos
  have hqp i := coordinate_pos (A i) Q (hA i) (hA0 i) hQpos
  rw [whitenWeighted_trace _ _ (fun i => (mul_pos (mul_pos (hl i) (hxp i)) (mul_pos (hl i) (hpp i))).le)
    (fun i => (mul_pos (mul_pos (hm i) (hyp i)) (mul_pos (hm i) (hqp i))).le)]
  exact weighted_frobenius_bound hc _ _ _ _ (fun i => mul_pos (hl i) (hxp i))
    (fun i => (mul_pos (hm i) (hyp i)).le) (fun i => mul_pos (hl i) (hpp i))
    (fun i => (mul_pos (hm i) (hqp i)).le) _ (interaction_symm c A l X)
    (interaction_nonneg hc.le A hA l (fun i => (hl i).le) X) hab
    (interaction_entry_square hc.le A hA l (fun i => (hl i).le) X hX.posSemidef)
    (interaction_duality_le hε A x hA hrank l m (fun i => (hl i).le) hlm X P Q hX hP)

theorem state_energy_ensemble [NeZero d] {c ε : ℝ} (hc : 384 ≤ c) (hε : 0 ≤ ε)
    (A : Fin N → H d) (x : Coordinates N) (hA : ∀ i, A i ∈ psdCone d)
    (hA0 : ∀ i, A i ≠ 0) (hrank : ∀ i, (A i : Hermitian.Mat d).rank ≤ 1)
    (l m : Fin N → ℝ) (hl : ∀ i, 0 < l i) (hm : ∀ i, 0 < m i)
    (hlm : ∀ i, l i*m i = psi (x i))
    (X Y P Q : H d) (hX : X ∈ pd d) (hY : Y ∈ pd d) (hPpos : P ∈ pd d) (hQpos : Q ∈ pd d)
    (hP : sandwich (invH X) P = eta c A x Q+ε • (Hermitian.one : H d))
    (hQ : sandwich (invH Y) Q = eta c A x P+ε • (Hermitian.one : H d))
    (hab : ∀ i, (l i*inner ℝ (A i) X)*(m i*inner ℝ (A i) Y) ≤ c⁻¹^2) :
    let IA := interaction c A l X
    let IB := interaction c A m Y
    ∃ Γ : Covariance.Mat (2*N), Γ.PosSemidef ∧ (∀ i, Γ i i ≤ 1) ∧
      ((4 : ℝ) • (1 : Covariance.Mat (2*N))-Γ).PosSemidef ∧ (23/48 : ℝ)*N ≤ Γ.trace ∧
      (∀ j, constraintLin IA IB (column (CFC.sqrt Γ) j) = 0) ∧
      (∑ j, energy X Y P Q
        (sandwich X (responseInput A l (fstVec (column (CFC.sqrt Γ) j))))
        (sandwich Y (responseInput A m (sndVec (column (CFC.sqrt Γ) j))))) ≤
      16*(∑ i, ((l i*inner ℝ (A i) X)*(l i*inner ℝ (A i) P)+
          (m i*inner ℝ (A i) Y)*(m i*inner ℝ (A i) Q))*
        (∑ j, (responseLin IB (column (CFC.sqrt Γ) j) i)^2)) := by
  dsimp only
  let a := fun i => (l i*inner ℝ (A i) X)*(l i*inner ℝ (A i) P)
  let b := fun i => (m i*inner ℝ (A i) Y)*(m i*inner ℝ (A i) Q)
  have ha : ∀ i, 0 < a i := fun i => mul_pos
    (mul_pos (hl i) (coordinate_pos (A i) X (hA i) (hA0 i) hX))
    (mul_pos (hl i) (coordinate_pos (A i) P (hA i) (hA0 i) hPpos))
  have hb : ∀ i, 0 < b i := fun i => mul_pos
    (mul_pos (hm i) (coordinate_pos (A i) Y (hA i) (hA0 i) hY))
    (mul_pos (hm i) (coordinate_pos (A i) Q (hA i) (hA0 i) hQpos))
  have h384 : (N : ℝ)/c ≤ (N : ℝ)/384 := div_le_div_of_nonneg_left (Nat.cast_nonneg N) (by norm_num) hc
  have hc0 : 0 < c := by linarith
  have hWA := (interaction_whiten_trace hc0 hε A x hA hA0 hrank l m hl hm hlm
    X Y P Q hX hY hPpos hQpos hP hab).trans h384
  have hm' : ∀ i, m i*l i = psi (x i) := fun i => by rw [mul_comm,hlm i]
  have hab' : ∀ i, (m i*inner ℝ (A i) Y)*(l i*inner ℝ (A i) X) ≤ c⁻¹^2 := fun i => by
    rw [mul_comm]; exact hab i
  have hWB := (interaction_whiten_trace hc0 hε A x hA hA0 hrank m l hm hl hm'
    Y X Q P hY hX hQpos hPpos hQ hab').trans h384
  let EM := diagBlock (energyMatrix A l X P) (energyMatrix A m Y Q)
  have hEM : EM.PosSemidef := diagBlock_psd (energyMatrix_psd A l X P hX.posSemidef hPpos.posSemidef)
    (energyMatrix_psd A m Y Q hY.posSemidef hQpos.posSemidef)
  have hdiag : ∀ i, EM i i = pairWeight a b i := by
    intro i
    dsimp only [EM]
    rw [diagBlock_diag]
    congr 1 <;> funext j <;> exact energyMatrix_diag A _ _ _ hA hrank j
  obtain ⟨Γ,hΓ,hd,hs,ht,hcouple,he⟩ := weighted_block_ensemble a b ha hb
    (interaction c A l X) (interaction c A m Y) EM hEM hdiag hWA hWB
  refine ⟨Γ,hΓ,hd,hs,ht,hcouple,?_⟩
  convert he using 1
  apply Finset.sum_congr rfl
  intro j _
  rw [proposed_energy A l m _ _ X Y P Q hX hY,quad_diagBlock]
  simp only [quad,EuclideanSpace.inner_eq_star_dotProduct,star_trivial]
  congr 1 <;> exact dotProduct_comm _ _

end CurrentKS.Interaction

end

end OAI
