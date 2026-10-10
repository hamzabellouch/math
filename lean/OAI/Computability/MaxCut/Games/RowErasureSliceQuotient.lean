import Mathlib
import OAI.Computability.MaxCut.Model

namespace OAI

/-!
Every nonempty affine row/column slice is an affine copy of the full space of
linear maps from the column quotient into the row kernel. This gives exact
uniform-law transport and preserves the affine evaluation offset.
-/

namespace MaxCutGames.Inverse.RowErasureSliceQuotient

noncomputable section

variable {R E K L : Type*} [Field R]
  [AddCommGroup E] [AddCommGroup K] [AddCommGroup L]
  [Module R E] [Module R K] [Module R L]

/-- The linear part of the affine parametrization. -/
def direction (A : K →ₗ[R] L) (Q : Submodule R E)
    (N : (E ⧸ Q) →ₗ[R] A.ker) : E →ₗ[R] K :=
  A.ker.subtype.comp (N.comp Q.mkQ)

@[simp] theorem direction_apply (A : K →ₗ[R] L) (Q : Submodule R E)
    (N : (E ⧸ Q) →ₗ[R] A.ker) (x : E) :
    direction A Q N x = (N (Q.mkQ x) : K) := rfl

/-- Quotient descent of a linear map which vanishes on the column span and
takes values in the common row kernel. -/
theorem exists_direction_of_row_and_column (A : K →ₗ[R] L)
    (Q : Submodule R E) (B : E →ₗ[R] K)
    (hQ : Q ≤ B.ker) (hA : LinearMap.range B ≤ A.ker) :
    ∃ N : (E ⧸ Q) →ₗ[R] A.ker, direction A Q N = B := by
  let B' : E →ₗ[R] A.ker := B.codRestrict A.ker
    (fun x => hA ⟨x, rfl⟩)
  have hQ' : Q ≤ B'.ker := by
    intro q hq
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    change B q = 0
    exact hQ hq
  refine ⟨Q.liftQ B' hQ', ?_⟩
  ext x
  rfl

theorem direction_injective (A : K →ₗ[R] L) (Q : Submodule R E) :
    Function.Injective (direction A Q) := by
  intro N P h
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := Q.mkQ_surjective x
  apply Subtype.ext
  exact congrArg (fun f : E →ₗ[R] K => f v) h

/-- The concrete affine slice around any one point satisfying its equations. -/
def AffineSlice (A : K →ₗ[R] L) (Q : Submodule R E) (M₀ : E →ₗ[R] K) :=
  {M : E →ₗ[R] K // A.comp M = A.comp M₀ ∧ ∀ q ∈ Q, M q = M₀ q}

def ofQuotient (A : K →ₗ[R] L) (Q : Submodule R E) (M₀ : E →ₗ[R] K)
    (N : (E ⧸ Q) →ₗ[R] A.ker) : AffineSlice A Q M₀ := by
  refine ⟨M₀ + direction A Q N, ?_, ?_⟩
  · apply LinearMap.ext
    intro x
    change A (M₀ x + (N (Q.mkQ x) : K)) = A (M₀ x)
    rw [map_add, show A (N (Q.mkQ x) : K) = 0 from (N (Q.mkQ x)).property,
      add_zero]
  · intro q hq
    have hz : Q.mkQ q = 0 := (Submodule.Quotient.mk_eq_zero Q).mpr hq
    simp [direction, hz]

@[simp] theorem ofQuotient_val (A : K →ₗ[R] L) (Q : Submodule R E)
    (M₀ : E →ₗ[R] K) (N : (E ⧸ Q) →ₗ[R] A.ker) :
    (ofQuotient A Q M₀ N).val = M₀ + direction A Q N := rfl

theorem ofQuotient_bijective (A : K →ₗ[R] L) (Q : Submodule R E)
    (M₀ : E →ₗ[R] K) : Function.Bijective (ofQuotient A Q M₀) := by
  constructor
  · intro N P h
    apply direction_injective A Q
    exact add_left_cancel (congrArg Subtype.val h)
  · intro M
    have hQ : Q ≤ (M.val - M₀).ker := by
      intro q hq
      change M.val q - M₀ q = 0
      exact sub_eq_zero.mpr (M.property.2 q hq)
    have hA : LinearMap.range (M.val - M₀) ≤ A.ker := by
      rintro y ⟨x, rfl⟩
      change A (M.val x - M₀ x) = 0
      rw [map_sub]
      apply sub_eq_zero.mpr
      exact congrArg (fun f : E →ₗ[R] L => f x) M.property.1
    obtain ⟨N, hN⟩ := exists_direction_of_row_and_column A Q (M.val - M₀) hQ hA
    refine ⟨N, ?_⟩
    apply Subtype.ext
    rw [ofQuotient_val, hN]
    simpa only [← add_sub_assoc] using add_sub_cancel_left M₀ M.val

/-- Uniform free quotient maps parametrize exactly the original affine slice. -/
def equiv (A : K →ₗ[R] L) (Q : Submodule R E) (M₀ : E →ₗ[R] K) :
    ((E ⧸ Q) →ₗ[R] A.ker) ≃ AffineSlice A Q M₀ :=
  Equiv.ofBijective (ofQuotient A Q M₀) (ofQuotient_bijective A Q M₀)

@[simp] theorem equiv_apply (A : K →ₗ[R] L) (Q : Submodule R E)
    (M₀ : E →ₗ[R] K) (N : (E ⧸ Q) →ₗ[R] A.ker) :
    equiv A Q M₀ N = ofQuotient A Q M₀ N := rfl

/-- The base point contributes an affine offset; it is not discarded. -/
theorem equiv_affine_target (A : K →ₗ[R] L) (Q : Submodule R E)
    (M₀ : E →ₗ[R] K) (N : (E ⧸ Q) →ₗ[R] A.ker) (z : E) (u : K) :
    (equiv A Q M₀ N).val z + u =
      (N (Q.mkQ z) : K) + (M₀ z + u) := by
  change (M₀ z + (N (Q.mkQ z) : K)) + u = _
  ac_rfl

/-- Exact uniform-law transport through the affine parametrization. -/
theorem expect_equiv (A : K →ₗ[R] L) (Q : Submodule R E) (M₀ : E →ₗ[R] K)
    [Fintype ((E ⧸ Q) →ₗ[R] A.ker)] [Fintype (AffineSlice A Q M₀)]
    (f : AffineSlice A Q M₀ → ℝ) :
    Finset.univ.expect (fun N => f (equiv A Q M₀ N)) = Finset.univ.expect f := by
  exact Fintype.expect_equiv (equiv A Q M₀) _ _ (fun _ => rfl)

end
end MaxCutGames.Inverse.RowErasureSliceQuotient

end OAI
