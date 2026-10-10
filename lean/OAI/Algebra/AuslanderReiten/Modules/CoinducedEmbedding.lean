import OAI.Algebra.AuslanderReiten.Algebras.FrobeniusTrace

namespace OAI

namespace ArExplicit.Coinduced

variable {k R M : Type*} [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

def adjoint (φ : Module.Dual k M) : M →ₗ[R] Coinduced k R where
  toFun m := ⟨{
    toFun := fun r => φ (r • m)
    map_add' := fun r s => by simp [add_smul]
    map_smul' := fun c r => by simp [smul_assoc] }⟩
  map_add' m n := by ext r; simp [smul_add]
  map_smul' r m := by
    ext s
    change φ (s • r • m) = φ ((s * r) • m)
    rw [mul_smul]

@[simp] theorem adjoint_eval_one (φ : Module.Dual k M) (m : M) :
    (adjoint (R := R) φ m).functional (1 : R) = φ m := by simp [adjoint]

variable [Module.Finite k M]

noncomputable def finiteEmbedding : M →ₗ[R] (Fin (Module.finrank k M) → Coinduced k R) :=
  LinearMap.pi fun i => adjoint ((Module.finBasis k M).coord i)

theorem finiteEmbedding_injective :
    Function.Injective (finiteEmbedding (k := k) (R := R) (M := M)) := by
  intro x y h
  apply (Module.finBasis k M).ext_elem
  intro i
  have hi := congrArg (fun f : Fin (Module.finrank k M) → Coinduced k R =>
    (f i).functional 1) h
  simpa [finiteEmbedding, Module.Basis.coord_apply] using hi

end ArExplicit.Coinduced

namespace ArExplicit.FrobeniusTrace

variable {k R M : Type*} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R)
variable [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
variable [Module.Finite k M]

noncomputable def finiteFreeEmbedding : M →ₗ[R] (Fin (Module.finrank k M) → R) :=
  LinearMap.pi fun i => τ.leftEquiv.symm.toLinearMap.comp
    (Coinduced.adjoint ((Module.finBasis k M).coord i))

theorem finiteFreeEmbedding_injective :
    Function.Injective (τ.finiteFreeEmbedding (M := M)) := by
  intro x y h
  apply Coinduced.finiteEmbedding_injective (k := k) (R := R)
  funext i
  have hi := congrFun h i
  exact τ.leftEquiv.symm.injective hi

include τ in
theorem exists_finiteFree_embedding :
    ∃ n : ℕ, ∃ i : M →ₗ[R] (Fin n → R), Function.Injective i :=
  ⟨Module.finrank k M, τ.finiteFreeEmbedding, τ.finiteFreeEmbedding_injective⟩

end ArExplicit.FrobeniusTrace

end OAI
