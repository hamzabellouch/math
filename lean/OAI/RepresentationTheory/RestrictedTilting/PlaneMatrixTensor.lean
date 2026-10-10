import OAI.RepresentationTheory.RestrictedTilting.CompatibleJets

namespace OAI

namespace FiberFunctorProof
open scoped BigOperators TensorProduct
universe u
section MatrixTensor
variable {k : Type u} [Field k] {G : Type u} [Monoid G]
variable {β : Type u} [Fintype β] [DecidableEq β]
variable {M : Type u} [AddCommGroup M] [Module k M]

noncomputable def matrixTensorLinear (A : Matrix β β k) (f : M →ₗ[k] M) :
    (β → M) →ₗ[k] (β → M) :=
  LinearMap.pi fun i => ∑ j, A i j • f.comp (LinearMap.proj j)

omit [DecidableEq β] in
lemma matrixTensorLinear_apply (A : Matrix β β k) (f : M →ₗ[k] M) (v : β → M) (i : β) :
    matrixTensorLinear A f v i = ∑ j, A i j • f (v j) := by
  simp only [matrixTensorLinear, LinearMap.pi_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply]

lemma matrixTensorLinear_one : matrixTensorLinear (1 : Matrix β β k) (LinearMap.id : M →ₗ[k] M) = 1 := by
  apply LinearMap.ext
  intro v
  funext i
  simp [matrixTensorLinear_apply, Matrix.one_apply]

omit [DecidableEq β] in
lemma matrixTensorLinear_mul (A B : Matrix β β k) (f g : M →ₗ[k] M) :
    matrixTensorLinear (A*B) (f*g) = matrixTensorLinear A f * matrixTensorLinear B g := by
  apply LinearMap.ext
  intro v
  funext i
  simp only [Module.End.mul_apply, matrixTensorLinear_apply, Matrix.mul_apply,
    Finset.sum_smul, map_sum, map_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

noncomputable def matrixTensorRepresentation
    (τ : Representation k G (β → k)) (σ : Representation k G M) :
    Representation k G (β → M) where
  toFun g := matrixTensorLinear (LinearMap.toMatrix' (τ g)) (σ g)
  map_one' := by
    simp only [map_one, LinearMap.toMatrix'_one]
    exact matrixTensorLinear_one
  map_mul' g h := by
    simp only [map_mul, LinearMap.toMatrix'_mul, matrixTensorLinear_mul]

lemma matrixTensorRepresentation_apply (τ : Representation k G (β → k))
    (σ : Representation k G M) (g : G) (v : β → M) (i : β) :
    matrixTensorRepresentation τ σ g v i = ∑ j, LinearMap.toMatrix' (τ g) i j • σ g (v j) :=
  matrixTensorLinear_apply _ _ _ _

end MatrixTensor

section PlaneTensor
variable (k : Type u) [Field k]
variable {β : Type u} [Fintype β] [DecidableEq β]
variable {M : Type u} [AddCommGroup M] [Module k M]
variable (τ : Representation k (SL2 k) (β → k)) (σ : Representation k (SL2 k) M)

lemma matrixTensor_rational (hτ : IsRational k τ) (hσ : IsRational k σ) :
    IsRational k (matrixTensorRepresentation τ σ) := by
  classical
  intro v l
  choose P hP using fun (i j : β) => hτ (Pi.single j 1) (LinearMap.proj i)
  choose Q hQ using fun (i j : β) => hσ (v j) (l.comp (LinearMap.single k (fun _ : β => M) i))
  refine ⟨∑ i, ∑ j, P i j * Q i j, fun g => ?_⟩
  have he : matrixTensorRepresentation τ σ g v =
      ∑ i, ∑ j, LinearMap.toMatrix' (τ g) i j •
        (LinearMap.single k (fun _ : β => M) i) (σ g (v j)) := by
    calc
      _ = ∑ i, (LinearMap.single k (fun _ : β => M) i)
          (matrixTensorRepresentation τ σ g v i) := (Finset.univ_sum_single _).symm
      _ = _ := by
        simp only [matrixTensorRepresentation_apply, map_sum, map_smul]
  rw [he]
  simp only [map_sum, map_smul, smul_eq_mul, map_mul, ← hP, ← hQ,
    LinearMap.comp_apply, LinearMap.toMatrix'_apply, LinearMap.proj_apply]

variable [Module (MvPolynomial (Fin 2) k) M]
  [IsScalarTower k (MvPolynomial (Fin 2) k) M]

lemma matrixTensor_planeCompatible (hσ : PlaneCompatible k σ) :
    PlaneCompatible k (matrixTensorRepresentation τ σ) := by
  intro g P v
  funext i
  simp only [matrixTensorRepresentation_apply, Pi.smul_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [hσ]
  exact smul_comm _ _ _

omit [Fintype β] [DecidableEq β] [Module k M] [IsScalarTower k (MvPolynomial (Fin 2) k) M] in
lemma pi_regular_x
    (hx : Function.Injective (fun m : M => (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) • m)) :
    Function.Injective (fun m : β → M => (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) • m) := by
  intro v w h
  funext i
  exact hx (congrFun h i)

omit [Fintype β] [DecidableEq β] [Module k M] [IsScalarTower k (MvPolynomial (Fin 2) k) M] in
lemma pi_regular_y
    (hy : ∀ v n : M, (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) • v =
      (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) • n → ∃ w : M, v = (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) • w) :
    ∀ v n : β → M, (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) • v =
      (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) • n → ∃ w : β → M, v = (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) • w := by
  intro v n h
  choose w hw using fun i => hy (v i) (n i) (congrFun h i)
  exact ⟨w, funext hw⟩

end PlaneTensor
end FiberFunctorProof

end OAI
