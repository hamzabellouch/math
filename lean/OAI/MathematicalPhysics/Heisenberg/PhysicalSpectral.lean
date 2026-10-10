import OAI.MathematicalPhysics.Heisenberg.SymmetrizedSurface

namespace OAI

attribute [instance] instDecidableEqFin instDecidableEqProd
noncomputable section
open scoped Classical BigOperators Matrix Matrix.Norms.Operator
namespace Heisenberg.TensorMatrix
variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] [DecidableEq n] in
lemma trace_reindex_eq (e : m ≃ n) (A : Matrix m m ℝ) :
    Matrix.trace (Matrix.reindex e e A)=Matrix.trace A := by
  exact e.symm.sum_comp (fun i=>A i i)

lemma reindex_exp (e : m ≃ n) (A : Matrix m m ℝ) :
    Matrix.reindex e e (NormedSpace.exp A)=NormedSpace.exp (Matrix.reindex e e A) :=
  NormedSpace.map_exp (Matrix.reindexAlgEquiv ℝ ℝ e)
    (Matrix.reindexAlgEquiv ℝ ℝ e).toLinearMap.continuous_of_finiteDimensional A
lemma trace_reindex_exp_compression {p : Type} [Fintype p] [DecidableEq p]
    (e : m ≃ p) (P A D : Matrix m m ℝ) (B E : Matrix n n ℝ) (V : Matrix p n ℝ)
    (hV : V.transpose*V=1) (hP : Matrix.reindex e e P=V*V.transpose)
    (hAB : Matrix.reindex e e A*V=V*B) (hDE : Matrix.reindex e e D*V=V*E) :
    Matrix.trace (P*NormedSpace.exp A*D)=Matrix.trace (NormedSpace.exp B*E) := by
  let r:=Matrix.reindexAlgEquiv ℝ ℝ e
  rw [←trace_reindex_eq e]
  change Matrix.trace (r (P*NormedSpace.exp A*D))=_
  rw [_root_.map_mul,_root_.map_mul]
  change Matrix.trace (Matrix.reindex e e P * Matrix.reindex e e (NormedSpace.exp A) * Matrix.reindex e e D)=_
  rw [hP,reindex_exp]
  exact trace_exp_compression _ _ _ hV hAB _ _ hDE

end Heisenberg.TensorMatrix

namespace Heisenberg.SlotTensor
open TensorMatrix SpinSlots
variable {X : Type} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
lemma reindex_spectral (ℓ : ℕ) (f : ℝ → ℝ) :
    Matrix.reindex (configEquiv ℓ) (configEquiv ℓ)
      (Matrix.diagonal (fun c : (X×Fin ℓ) → Bool=>f (SlotColor.magnetization c)))=
      Matrix.diagonal (fun a : X → Config ℓ=>f (configMagnetization ℓ a)) := by
  ext a b
  by_cases hab : a=b
  · subst b
    simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Matrix.diagonal_apply_eq,color_config_mag]
  · have he : (configEquiv ℓ).symm a ≠ (configEquiv ℓ).symm b := fun hh=>hab ((configEquiv ℓ).symm.injective hh)
    simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Matrix.diagonal_apply_ne _ he,
      Matrix.diagonal_apply_ne _ hab]

theorem trace_clock_spectral (R : X → X → Prop) (hR : ∀ x y,R x y → x≠y)
    (ℓ : ℕ) (t : ℝ) (f : ℝ → ℝ) :
    Matrix.trace (Surface.colorSymmetrizer X ℓ * NormedSpace.exp (t • clockGenerator R ℓ) *
      Matrix.diagonal (fun c : (X×Fin ℓ) → Bool=>f (SlotColor.magnetization c)))=
    Matrix.trace (NormedSpace.exp (t • spinGenerator R ℓ) *
      Matrix.diagonal (fun k : X → Level ℓ=>f (physicalMagnetization ℓ k))) := by
  have hAB : Matrix.reindex (configEquiv ℓ) (configEquiv ℓ) (t • clockGenerator R ℓ)*tensor (fun _ : X=>basis ℓ)=
      tensor (fun _ : X=>basis ℓ)*(t • spinGenerator R ℓ) := by
    have he := congrArg (fun M : Matrix (X → Config ℓ) (X → Level ℓ) ℝ=>t • M)
      (generator_intertwines R hR ℓ)
    have hs : Matrix.reindex (configEquiv ℓ) (configEquiv ℓ) (t • clockGenerator R ℓ) =
        t • Matrix.reindex (configEquiv ℓ) (configEquiv ℓ) (clockGenerator R ℓ) := rfl
    rw [hs,Matrix.smul_mul,Matrix.mul_smul]
    exact he
  have hDE : Matrix.reindex (configEquiv ℓ) (configEquiv ℓ)
      (Matrix.diagonal (fun c : (X×Fin ℓ) → Bool=>f (SlotColor.magnetization c)))*tensor (fun _ : X=>basis ℓ)=
      tensor (fun _ : X=>basis ℓ)*Matrix.diagonal (fun k : X → Level ℓ=>f (physicalMagnetization ℓ k)) := by
    rw [reindex_spectral]
    exact diagonal_function_intertwines _ _ _ (total_diagonal_intertwines (X:=X) ℓ) f
  have hP : Matrix.reindex (configEquiv ℓ) (configEquiv ℓ) (Surface.colorSymmetrizer X ℓ)=
      tensor (fun _ : X=>basis ℓ)*(tensor (fun _ : X=>basis ℓ)).transpose := by
    convert Surface.colorSymmetrizer_reindex X ℓ using 1; congr! 20
  exact trace_reindex_exp_compression (configEquiv ℓ) _ _ _ _ _
    (tensor (fun _ : X=>basis ℓ)) (basis_orthonormal ℓ) hP hAB hDE

end Heisenberg.SlotTensor
end

end OAI
