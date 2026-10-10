import Mathlib

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison.MatrixModules

open Matrix

variable {𝕜 I E : Type*} [Field 𝕜] [Fintype I] [DecidableEq I]
  [AddCommGroup E] [Module 𝕜 E]

variable (ρ : Matrix I I 𝕜 →ₐ[𝕜] Module.End 𝕜 E) (o : I)

abbrev corner : Submodule 𝕜 E := LinearMap.range (ρ (single o o 1))

lemma corner_fixed (x : corner ρ o) : ρ (single o o 1) (x : E) = x := by
  obtain ⟨y, hy⟩ := x.property
  rw [← hy]
  change (ρ (single o o 1) * ρ (single o o 1)) y = _
  rw [← map_mul, Matrix.single_mul_single_same, one_mul]

noncomputable def coordinates (i : I) : E →ₗ[𝕜] corner ρ o :=
  (ρ (single o i 1)).codRestrict _ (fun x => by
    refine ⟨ρ (single o i 1) x, ?_⟩
    change (ρ (single o o 1) * ρ (single o i 1)) x = _
    rw [← map_mul, Matrix.single_mul_single_same, one_mul])

noncomputable def recombine : (I → corner ρ o) →ₗ[𝕜] E :=
  ∑ i : I, (ρ (single i o 1)).comp
    ((corner ρ o).subtype.comp (LinearMap.proj i))

@[simp] lemma coordinates_apply (i : I) (x : E) :
    (coordinates ρ o i x : E) = ρ (single o i 1) x := rfl

@[simp] lemma recombine_apply (x : I → corner ρ o) :
    recombine ρ o x = ∑ i : I, ρ (single i o 1) (x i : E) := by
  simp [recombine]

lemma coordinates_recombine (x : I → corner ρ o) (i : I) :
    coordinates ρ o i (recombine ρ o x) = x i := by
  apply Subtype.ext
  rw [coordinates_apply, recombine_apply, map_sum]
  have hdiag : ρ (single o i 1) (ρ (single i o 1) (x i : E)) = x i := by
    change (ρ (single o i 1) * ρ (single i o 1)) (x i : E) = _
    rw [← map_mul, Matrix.single_mul_single_same, one_mul]
    exact corner_fixed ρ o _
  rw [Finset.sum_eq_single i]
  · exact hdiag
  · intro j _ hji
    change (ρ (single o i 1) * ρ (single j o 1)) (x j : E) = 0
    rw [← map_mul, Matrix.single_mul_single_of_ne 1 o i j hji.symm 1,
      map_zero, LinearMap.zero_apply]
  · simp

lemma recombine_coordinates (x : E) :
    recombine ρ o (fun i => coordinates ρ o i x) = x := by
  rw [recombine_apply]
  simp only [coordinates_apply]
  have h (i : I) : ρ (single i o 1) (ρ (single o i 1) x) = ρ (single i i 1) x := by
    change (ρ (single i o 1) * ρ (single o i 1)) x = _
    rw [← map_mul, Matrix.single_mul_single_same, one_mul]
  simp only [h]
  rw [← LinearMap.sum_apply, ← map_sum, Matrix.sum_single_one, map_one]
  rfl

noncomputable def moduleEquiv : (I → corner ρ o) ≃ₗ[𝕜] E where
  __ := recombine ρ o
  invFun x i := coordinates ρ o i x
  left_inv x := funext (coordinates_recombine ρ o x)
  right_inv := recombine_coordinates ρ o

lemma moduleEquiv_intertwines (a : Matrix I I 𝕜) (x : I → corner ρ o) :
    ρ a (moduleEquiv ρ o x) = moduleEquiv ρ o (fun i => ∑ j, a i j • x j) := by
  change ρ a (recombine ρ o x) = recombine ρ o _
  simp only [recombine_apply, Submodule.coe_sum, Submodule.coe_smul, map_sum,
    map_smul]
  have hm (j : I) : a * single j o 1 = ∑ i, a i j • single i o 1 := by
    ext i k
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
      Matrix.single, Matrix.of_apply]
    by_cases h : o = k <;> simp [h]
  calc
    (∑ j, ρ a (ρ (single j o 1) (x j : E))) =
        ∑ j, ∑ i, a i j • ρ (single i o 1) (x j : E) := by
      apply Finset.sum_congr rfl
      intro j _
      change (ρ a * ρ (single j o 1)) (x j : E) = _
      rw [← map_mul, hm, map_sum, LinearMap.sum_apply]
      simp only [map_smul, LinearMap.smul_apply]
    _ = _ := Finset.sum_comm

section Coordinates

variable {R : Type*} [Fintype R]

noncomputable def basisCopies (b : Module.Basis R 𝕜 (corner ρ o)) :
    (I × R → 𝕜) ≃ₗ[𝕜] (I → corner ρ o) :=
  (LinearEquiv.curry 𝕜 𝕜 I R).trans
    (LinearEquiv.piCongrRight fun _ => b.equivFun.symm)

@[simp] lemma basisCopies_apply (b : Module.Basis R 𝕜 (corner ρ o)) (v : I × R → 𝕜)
    (i : I) : basisCopies ρ o b v i = b.equivFun.symm (fun r => v (i, r)) := rfl

def inflate [DecidableEq R] (a : Matrix I I 𝕜) : Matrix (I × R) (I × R) 𝕜 :=
  fun x y => if x.2 = y.2 then a x.1 y.1 else 0

omit [DecidableEq I] in
lemma inflate_mulVec [DecidableEq R] (a : Matrix I I 𝕜) (v : I × R → 𝕜)
    (i : I) (r : R) : (inflate (R := R) a *ᵥ v) (i, r) = ∑ j, a i j * v (j, r) := by
  classical
  simp [Matrix.mulVec, dotProduct, inflate, Fintype.sum_prod_type]

lemma basisCopies_intertwines [DecidableEq R] (b : Module.Basis R 𝕜 (corner ρ o))
    (a : Matrix I I 𝕜) (v : I × R → 𝕜) :
    basisCopies ρ o b (inflate a *ᵥ v) =
      fun i => ∑ j, a i j • basisCopies ρ o b v j := by
  funext i
  simp only [basisCopies_apply, inflate_mulVec]
  apply b.equivFun.injective
  rw [LinearEquiv.apply_symm_apply, map_sum]
  simp only [map_smul, LinearEquiv.apply_symm_apply]
  ext r
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

noncomputable def representationEquiv (b : Module.Basis R 𝕜 (corner ρ o)) :
    (I × R → 𝕜) ≃ₗ[𝕜] E := (basisCopies ρ o b).trans (moduleEquiv ρ o)

lemma representationEquiv_intertwines [DecidableEq R]
    (b : Module.Basis R 𝕜 (corner ρ o)) (a : Matrix I I 𝕜) (v : I × R → 𝕜) :
    ρ a (representationEquiv ρ o b v) = representationEquiv ρ o b (inflate a *ᵥ v) := by
  change ρ a (moduleEquiv ρ o (basisCopies ρ o b v)) =
    moduleEquiv ρ o (basisCopies ρ o b (inflate a *ᵥ v))
  rw [moduleEquiv_intertwines, basisCopies_intertwines]

end Coordinates

end Kadison.MatrixModules
end

end OAI
