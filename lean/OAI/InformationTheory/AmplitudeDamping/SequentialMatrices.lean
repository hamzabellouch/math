import OAI.InformationTheory.AmplitudeDamping.CapacityConverse

namespace OAI

universe u_1 u_2

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix
namespace GAD
variable {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ] [DecidableEq ι]

def projectionAction (P : Matrix ι ι ℂ) (v : EuclideanSpace ℂ (ι × κ)) :
    EuclideanSpace ℂ (ι × κ) := frobVector (P*(show Matrix ι κ ℂ from fun i k ↦ v (i,k)))

omit [Fintype κ] [DecidableEq ι] in
theorem projectionAction_frob (P : Matrix ι ι ℂ) (X : Matrix ι κ ℂ) :
    projectionAction P (frobVector X)=frobVector (P*X) := rfl

omit [DecidableEq ι] in
theorem projectionAction_orthogonal {P : Matrix ι ι ℂ} (hP : IsProjection P)
    (v w : EuclideanSpace ℂ (ι × κ)) :
    ⟪projectionAction P v,w-projectionAction P w⟫_ℝ=0 := by
  exact projection_orthogonal hP (fun i k ↦ v (i,k)) (fun i k ↦ w (i,k))

omit [DecidableEq ι] in
theorem matrix_sequential_union_bound (P : ℕ → Matrix ι ι ℂ) (hP : ∀ i, IsProjection (P i))
    (X : ℕ → Matrix ι κ ℂ) (hX : ∀ i, X (i+1)=P i*X i) (n : ℕ) :
    mass (X 0)-mass (X n) ≤ 4*∑ i ∈ Finset.range n, mass (X 0-P i*X 0) := by
  have h := sequential_union_bound (fun i ↦ projectionAction (P i))
    (fun i ↦ projectionAction_orthogonal (hP i)) (fun i ↦ frobVector (X i))
    (fun i ↦ by rw [hX]; rfl) n
  simpa only [projectionAction_frob,← frobVector_sub,frobVector_norm] using h

def rejectProduct (Q : ℕ → Matrix ι ι ℂ) : ℕ → Matrix ι ι ℂ
  | 0 => 1
  | k+1 => (1-Q k)*rejectProduct Q k

theorem rejectProduct_loss (Q : ℕ → Matrix ι ι ℂ) (hQ : ∀ k, IsProjection (Q k)) (k : ℕ) :
    (rejectProduct Q k)ᴴ*rejectProduct Q k-
      (rejectProduct Q (k+1))ᴴ*rejectProduct Q (k+1)=
      (rejectProduct Q k)ᴴ*Q k*rejectProduct Q k := by
  rw [rejectProduct,Matrix.conjTranspose_mul,(hQ k).complement.1.eq]
  have he : (rejectProduct Q k)ᴴ*(1-Q k)*((1-Q k)*rejectProduct Q k)=
      (rejectProduct Q k)ᴴ*(1-Q k)*rejectProduct Q k := by
    rw [← Matrix.mul_assoc _ (1-Q k),Matrix.mul_assoc (rejectProduct Q k)ᴴ,
      (hQ k).complement.2]
  rw [he,Matrix.mul_sub,Matrix.mul_one,Matrix.sub_mul]
  abel

theorem rejectProduct_sum (Q : ℕ → Matrix ι ι ℂ) (hQ : ∀ k, IsProjection (Q k)) (n : ℕ) :
    (∑ k ∈ Finset.range n, (rejectProduct Q k)ᴴ*Q k*rejectProduct Q k)=
      1-(rejectProduct Q n)ᴴ*rejectProduct Q n := by
  simp_rw [← rejectProduct_loss Q hQ]
  rw [Finset.sum_range_sub']
  simp [rejectProduct]

theorem sequential_projector_success (Q : ℕ → Matrix ι ι ℂ)
    (hQ : ∀ k, IsProjection (Q k)) (Y : Matrix ι κ ℂ) (m : ℕ) :
    mass Y-mass (Q m*rejectProduct Q m*Y) ≤
      4*(mass (Y-Q m*Y)+∑ j ∈ Finset.range m, mass (Q j*Y)) := by
  let P : ℕ → Matrix ι ι ℂ := fun k ↦ if k=m then Q m else 1-Q k
  have hp (k : ℕ) : IsProjection (P k) := by
    dsimp [P]; split_ifs
    · exact hQ m
    · exact (hQ k).complement
  -- Only the first m+1 recurrence steps matter; use a genuine recursively defined sequence.
  let Z : ℕ → Matrix ι κ ℂ := fun k ↦ Nat.rec Y (fun j A ↦ P j*A) k
  have hz (k : ℕ) : Z (k+1)=P k*Z k := rfl
  have hZ (k : ℕ) (hk : k ≤ m) : Z k=rejectProduct Q k*Y := by
    induction k with
    | zero => simp [Z,rejectProduct]
    | succ k ih =>
      rw [hz,ih (by omega)]
      have hkm : k ≠ m := by omega
      simp only [P,ite_eq_right hkm,rejectProduct,Matrix.mul_assoc]
  have hZend : Z (m+1)=Q m*rejectProduct Q m*Y := by
    rw [hz,hZ m le_rfl]; simp only [P,ite_eq_left rfl,Matrix.mul_assoc]
  have h := matrix_sequential_union_bound P hp Z hz (m+1)
  have hZ0 : Z 0=Y := rfl
  rw [hZ0,hZend,Finset.sum_range_succ] at h
  have hs : (∑ j ∈ Finset.range m, mass (Y-P j*Y))=∑ j ∈ Finset.range m, mass (Q j*Y) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjm : j ≠ m := by have := Finset.mem_range.mp hj; omega
    simp only [P,ite_eq_right hjm,Matrix.sub_mul,Matrix.one_mul,sub_sub_cancel]
  rw [hs] at h
  simpa only [P,ite_eq_left rfl,add_comm] using h

omit [DecidableEq ι] in
theorem mass_triangle_sq (X Y : Matrix ι κ ℂ) : mass (X+Y) ≤ 2*mass X+2*mass Y := by
  have h := norm_sub_sq_real (frobVector X) (frobVector Y)
  rw [mass_add,← frobVector_norm X,← frobVector_norm Y]
  nlinarith [sq_nonneg ‖frobVector X-frobVector Y‖]

theorem projected_self_failure {P Q : Matrix ι ι ℂ} (hQ : IsProjection Q)
    (F : Matrix ι κ ℂ) : mass (P*F-Q*(P*F)) ≤ 2*mass (F-Q*F)+2*mass (F-P*F) := by
  have he : P*F-Q*(P*F)=(F-Q*F)+(-(1-Q)*(F-P*F)) := by
    simp only [Matrix.neg_mul,Matrix.sub_mul,Matrix.one_mul,Matrix.mul_sub]
    abel
  rw [he]
  have hb := mass_triangle_sq (F-Q*F) (-(1-Q)*(F-P*F))
  have hn : mass (-(1-Q)*(F-P*F))=mass ((1-Q)*(F-P*F)) := by
    rw [Matrix.neg_mul,← neg_one_smul ℝ ((1-Q)*(F-P*F)),mass_real_smul]
    norm_num
  rw [hn] at hb
  have hc := projection_mass_le hQ.complement (F-P*F)
  linarith

end GAD

end

end OAI
