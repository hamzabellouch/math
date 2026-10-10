import OAI.Algebra.Finitistic.Bar.Splitting

namespace OAI
open scoped TensorProduct
open TensorProduct TrivSqZeroExt
noncomputable section

namespace DerivedBar.SquareZero
universe u

private theorem sign_square {k : Type u} [Field k] (r : ℕ) :
    (-1 : k)^r * (-1 : k)^r = 1 := by
  rw [← mul_pow]
  simp

variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]

/-- Projection to count r, rescaled by one minus sign per base/ideal inversion.
For block lengths i₀,...,iᵣ the exponent is Σⱼ (r-j)iⱼ. -/
def signedProjection : (n r : ℕ) → Module.End k (term k (TrivSqZeroExt D X) N n)
  | 0, 0 => LinearMap.id
  | 0, _+1 => 0
  | n+1, 0 => TensorProduct.map (baseProjection k D X) (signedProjection n 0)
  | n+1, r+1 => (-1 : k)^(r+1) •
      TensorProduct.map (baseProjection k D X) (signedProjection n (r+1)) +
      TensorProduct.map (idealProjection k D X) (signedProjection n r)

@[simp] theorem signedProjection_base (n r : ℕ) (d : D)
    (v : term k (TrivSqZeroExt D X) N n) :
    signedProjection k D X N (n+1) r ((inl d : TrivSqZeroExt D X) ⊗ₜ[k] v) =
      (-1 : k)^r • ((inl d : TrivSqZeroExt D X) ⊗ₜ[k]
        signedProjection k D X N n r v) := by
  cases r <;> simp [signedProjection]

@[simp] theorem signedProjection_ideal_zero (n : ℕ) (x : X)
    (v : term k (TrivSqZeroExt D X) N n) :
    signedProjection k D X N (n+1) 0 ((inr x : TrivSqZeroExt D X) ⊗ₜ[k] v) = 0 := by
  simp [signedProjection]

@[simp] theorem signedProjection_ideal_succ (n r : ℕ) (x : X)
    (v : term k (TrivSqZeroExt D X) N n) :
    signedProjection k D X N (n+1) (r+1) ((inr x : TrivSqZeroExt D X) ⊗ₜ[k] v) =
      (inr x : TrivSqZeroExt D X) ⊗ₜ[k] signedProjection k D X N n r v := by
  simp [signedProjection]

variable {k D X N}

/-- The rescaling stays inside the actual count subspace. -/
theorem signedProjection_word_mem {n r : ℕ} {v : term k (TrivSqZeroExt D X) N n}
    (hv : Word k D X N n r v) :
    signedProjection k D X N n r v ∈ weight k D X N n r := by
  induction hv with
  | nil v => exact Submodule.subset_span (Word.nil v)
  | base d h ih =>
    rw [signedProjection_base]
    exact Submodule.smul_mem _ _ (base_tmul_mem d ih)
  | ideal x h ih =>
    rw [signedProjection_ideal_succ]
    exact ideal_tmul_mem x ih

/-- The sign rescaling is its own inverse on homogeneous pure tensors. -/
theorem signedProjection_sq_word {n r : ℕ} {v : term k (TrivSqZeroExt D X) N n}
    (hv : Word k D X N n r v) :
    signedProjection k D X N n r (signedProjection k D X N n r v) = v := by
  induction hv with
  | nil v => rfl
  | @base n r v d h ih =>
    rw [signedProjection_base, map_smul, signedProjection_base, ih, smul_smul,
      sign_square, one_smul]
  | @ideal n r v x h ih =>
    rw [signedProjection_ideal_succ, signedProjection_ideal_succ, ih]

theorem signedProjection_mem {n r : ℕ} {v : term k (TrivSqZeroExt D X) N n}
    (hv : v ∈ weight k D X N n r) :
    signedProjection k D X N n r v ∈ weight k D X N n r := by
  have h : weight k D X N n r ≤
      (weight k D X N n r).comap (signedProjection k D X N n r) :=
    Submodule.span_le.mpr (fun _ hw => signedProjection_word_mem hw)
  exact h hv

/-- Involutivity holds on the entire submodule, including sums of block tensors. -/
theorem signedProjection_sq {n r : ℕ} {v : term k (TrivSqZeroExt D X) N n}
    (hv : v ∈ weight k D X N n r) :
    signedProjection k D X N n r (signedProjection k D X N n r v) = v := by
  have h : weight k D X N n r ≤
      ((signedProjection k D X N n r).comp (signedProjection k D X N n r) -
        LinearMap.id).ker := by
    apply Submodule.span_le.mpr
    intro w hw
    change signedProjection k D X N n r (signedProjection k D X N n r w) - w = 0
    rw [signedProjection_sq_word hw, sub_self]
  exact sub_eq_zero.mp (h hv)

variable (k D X N)

/-- The signed count operator preserves the exterior left D-action. -/
def twoSidedSignedProjection (n r : ℕ) :
    Module.End D (D ⊗[k] term k (TrivSqZeroExt D X) N n) :=
  AlgebraTensorModule.lTensor D D (signedProjection k D X N n r)

variable {k D X N}

theorem twoSidedSignedProjection_mem {n r : ℕ}
    {v : D ⊗[k] term k (TrivSqZeroExt D X) N n}
    (hv : v ∈ twoSidedWeight k D X N n r) :
    twoSidedSignedProjection k D X N n r v ∈ twoSidedWeight k D X N n r := by
  have h : twoSidedWeight k D X N n r ≤
      (twoSidedWeight k D X N n r).comap (twoSidedSignedProjection k D X N n r) := by
    apply Submodule.span_le.mpr
    rintro w ⟨d, z, hz, rfl⟩
    exact tensor_weight_mem d (signedProjection_word_mem hz)
  exact h hv

theorem twoSidedSignedProjection_sq {n r : ℕ}
    {v : D ⊗[k] term k (TrivSqZeroExt D X) N n}
    (hv : v ∈ twoSidedWeight k D X N n r) :
    twoSidedSignedProjection k D X N n r (twoSidedSignedProjection k D X N n r v) = v := by
  have h : twoSidedWeight k D X N n r ≤
      ((twoSidedSignedProjection k D X N n r).comp
        (twoSidedSignedProjection k D X N n r) - LinearMap.id).ker := by
    apply Submodule.span_le.mpr
    rintro w ⟨d, z, hz, rfl⟩
    change d ⊗ₜ[k] signedProjection k D X N n r (signedProjection k D X N n r z) -
      d ⊗ₜ[k] z = 0
    rw [signedProjection_sq_word hz, sub_self]
  exact sub_eq_zero.mp (h hv)

variable (k D X N)

/-- Actual D-linear involution giving the manuscript's component rescaling.
This alone is not the chain comparison or the derived tensor identification. -/
def signEquiv (n r : ℕ) : twoSidedWeight k D X N n r ≃ₗ[D]
    twoSidedWeight k D X N n r where
  toLinearMap := (twoSidedSignedProjection k D X N n r).restrict
    (fun _ hv => twoSidedSignedProjection_mem hv)
  invFun v := ⟨twoSidedSignedProjection k D X N n r v, twoSidedSignedProjection_mem v.property⟩
  left_inv v := Subtype.ext (twoSidedSignedProjection_sq v.property)
  right_inv v := Subtype.ext (twoSidedSignedProjection_sq v.property)
end DerivedBar.SquareZero

end

end OAI
