import OAI.MathematicalPhysics.Heisenberg.PhysicalSpectral

namespace OAI

attribute [instance] instDecidableEqFin instDecidableEqProd
noncomputable section
open scoped Classical BigOperators Matrix Matrix.Norms.Operator
namespace Heisenberg.TensorMatrix
variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
omit [DecidableEq m] in
lemma compress_eq (A : Matrix m m ℝ) (B : Matrix n n ℝ) (V : Matrix m n ℝ)
    (hV : V.transpose*V=1) (hAB : A*V=V*B) : V.transpose*A*V=B := by
  rw [Matrix.mul_assoc,hAB,←Matrix.mul_assoc,hV,Matrix.one_mul]
omit [DecidableEq m] in
lemma compress_symmetric (A : Matrix m m ℝ) (B : Matrix n n ℝ) (V : Matrix m n ℝ)
    (hV : V.transpose*V=1) (hAB : A*V=V*B) (hA : A.transpose=A) : B.transpose=B := by
  rw [←compress_eq A B V hV hAB]
  simp only [Matrix.transpose_mul,Matrix.transpose_transpose,hA,Matrix.mul_assoc]
omit [DecidableEq m] in
lemma compress_commute (A D : Matrix m m ℝ) (B E : Matrix n n ℝ) (V : Matrix m n ℝ)
    (hV : V.transpose*V=1) (hAB : A*V=V*B) (hDE : D*V=V*E) (hAD : Commute A D) : Commute B E := by
  have he:=congrArg (fun M : Matrix m m ℝ=>V.transpose*M*V) hAD.eq
  simp only [Matrix.mul_assoc] at he
  rw [hDE,hAB,←Matrix.mul_assoc A V E,hAB,←Matrix.mul_assoc D V B,hDE] at he
  simp only [←Matrix.mul_assoc,hV,Matrix.one_mul] at he
  exact he
end Heisenberg.TensorMatrix
namespace Heisenberg.SlotColor
variable {V : Type} [Fintype V]
lemma magnetization_permute (π : Equiv.Perm V) (c : V → Bool) :
    magnetization (permute π c)=magnetization c := by
  exact π.symm.sum_comp (fun v=>if c v then (1:ℝ)/2 else -1/2)
lemma matrix_mag_commute (π : Equiv.Perm V) :
    Commute (matrix π) (Matrix.diagonal (magnetization (V:=V))) := by
  ext a b
  simp only [Matrix.mul_diagonal,Matrix.diagonal_mul,matrix]
  split_ifs with h
  · subst a
    simp only [one_mul,mul_one,magnetization_permute]
  · simp
lemma matrix_swap_transpose [DecidableEq V] (x y : V) : (matrix (Equiv.swap x y)).transpose=matrix (Equiv.swap x y) := by
  ext a b
  simp only [Matrix.transpose_apply,matrix]
  congr 1
  have hi : Function.Involutive (permute (Equiv.swap x y)) := by
    intro c
    ext v
    simp only [permute_apply,Equiv.symm_swap,Equiv.swap_apply_self]
  exact propext ⟨fun h=>by rw [←h,hi],fun h=>by rw [←h,hi]⟩
end Heisenberg.SlotColor
namespace Heisenberg.SlotTensor
open TensorMatrix SpinSlots
variable {X : Type} [Fintype X] [DecidableEq X]
lemma clockGenerator_transpose (R : X → X → Prop) (ℓ : ℕ) :
    (clockGenerator R ℓ).transpose=clockGenerator R ℓ := by
  simp only [clockGenerator,Matrix.transpose_sum,Matrix.transpose_smul,Matrix.transpose_sub,
    SlotColor.matrix_swap_transpose,Matrix.transpose_one]
lemma clockGenerator_mag (R : X → X → Prop) (ℓ : ℕ) :
    Commute (clockGenerator R ℓ) (Matrix.diagonal (SlotColor.magnetization (V:=X×Fin ℓ))) := by
  change clockGenerator R ℓ * _ = _ * clockGenerator R ℓ
  ext a b
  simp only [Matrix.mul_diagonal,Matrix.diagonal_mul,clockGenerator,Matrix.sum_apply,
    Matrix.smul_apply,Matrix.sub_apply,smul_eq_mul,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  simp only [SlotColor.matrix,Matrix.one_apply]
  split_ifs with h h'
  · subst a
    ring
  · subst a
    rw [SlotColor.magnetization_permute]
    ring
  · subst a
    ring
  · ring

lemma spinGenerator_transpose (R : X → X → Prop) (hR : ∀ x y,R x y → x≠y) (ℓ : ℕ) :
    (spinGenerator R ℓ).transpose=spinGenerator R ℓ := by
  apply compress_symmetric _ _ (tensor (fun _ : X=>basis ℓ)) (basis_orthonormal ℓ) (generator_intertwines R hR ℓ)
  change Matrix.reindex _ _ ((clockGenerator R ℓ).transpose)=_
  rw [clockGenerator_transpose]
lemma spinGenerator_mag (R : X → X → Prop) (hR : ∀ x y,R x y → x≠y) (ℓ : ℕ) :
    Commute (spinGenerator R ℓ) (Matrix.diagonal (physicalMagnetization (X:=X) ℓ)) := by
  apply compress_commute _ (Matrix.diagonal (configMagnetization (X:=X) ℓ)) _ _
    (tensor (fun _ : X=>basis ℓ)) (basis_orthonormal ℓ) (generator_intertwines R hR ℓ) (total_diagonal_intertwines ℓ)
  have hh:=(clockGenerator_mag R ℓ).map (Matrix.reindexAlgEquiv ℝ ℝ (configEquiv (X:=X) ℓ))
  change Commute (Matrix.reindex _ _ _) (Matrix.reindex _ _ _) at hh
  rw [show Matrix.diagonal (SlotColor.magnetization (V:=X×Fin ℓ))=
      Matrix.diagonal (fun c=>id (SlotColor.magnetization c)) from rfl,
    reindex_spectral ℓ id] at hh
  exact hh
omit [DecidableEq X] in
lemma physicalMagnetization_bounds (ℓ : ℕ) (k : X → Level ℓ) :
    -(Fintype.card X:ℝ)*ℓ/2≤physicalMagnetization ℓ k ∧
      physicalMagnetization ℓ k≤(Fintype.card X:ℝ)*ℓ/2 := by
  have hl : ∑ x : X,(-((ℓ:ℝ)/2))≤physicalMagnetization ℓ k := by
    apply Finset.sum_le_sum
    intro x _
    have hk : (0:ℝ)≤k x:=by positivity
    linarith
  have hu : physicalMagnetization ℓ k≤∑ _ : X,(ℓ:ℝ)/2 := by
    apply Finset.sum_le_sum
    intro x _
    have hk : (k x:ℝ)≤ℓ:=by exact_mod_cast Nat.le_of_lt_succ (k x).isLt
    linarith
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hl hu
  constructor <;> linarith
end Heisenberg.SlotTensor
end

end OAI
