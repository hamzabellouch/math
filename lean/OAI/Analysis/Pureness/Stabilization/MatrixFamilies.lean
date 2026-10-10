import OAI.Analysis.Pureness.Stabilization.MatrixSystem
import OAI.Analysis.Pureness.Stabilization.FamilyNorm

namespace OAI
noncomputable section
open scoped ENNReal Topology CStarAlgebra
open Filter
namespace CuntzTrace
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def matrixFamily (n : ℕ) : FinMatrix A n →⋆ₙₐ[ℂ] BoundedFamilies (FinMatrix A) where
  toFun M := ⟨fun m => if h : n ≤ m then matrixInclusion h M else 0,
    memℓp_infty ⟨‖M‖, by
      rintro _ ⟨m,rfl⟩
      change ‖if h : n ≤ m then matrixInclusion h M else 0‖ ≤ ‖M‖
      split_ifs <;> simp_all [norm_nonneg]⟩⟩
  map_zero' := by apply lp.ext; funext m; change (if h : n ≤ m then matrixInclusion h 0 else 0) = 0; split_ifs <;> simp_all
  map_add' M N := by
    apply lp.ext; funext m
    change (if h : n ≤ m then matrixInclusion h (M+N) else 0) =
      (if h : n ≤ m then matrixInclusion h M else 0) + (if h : n ≤ m then matrixInclusion h N else 0)
    split_ifs <;> simp_all
  map_mul' M N := by
    apply lp.ext; funext m
    change (if h : n ≤ m then matrixInclusion h (M*N) else 0) =
      (if h : n ≤ m then matrixInclusion h M else 0) * (if h : n ≤ m then matrixInclusion h N else 0)
    split_ifs <;> simp_all
  map_smul' c M := by
    apply lp.ext; funext m
    change (if h : n ≤ m then matrixInclusion h (c • M) else 0) =
      c • (if h : n ≤ m then matrixInclusion h M else 0)
    split_ifs <;> simp_all
  map_star' M := by
    apply lp.ext; funext m
    change (if h : n ≤ m then matrixInclusion h (star M) else 0) =
      star (if h : n ≤ m then matrixInclusion h M else 0)
    by_cases h : n ≤ m
    · rw [dite_eq_left h, dite_eq_left h]
      exact map_star (matrixInclusion h) M
    · rw [dite_eq_right h, dite_eq_right h]
      exact (star_zero _).symm

namespace FamilyQuotient
variable {F : ℕ → Type*} [∀ n, NonUnitalCStarAlgebra (F n)]
def quotientHom : BoundedFamilies F →⋆ₙₐ[ℂ] FamilyQuotient F where
  toFun := mk
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

lemma mk_eq_of_eventually_eq (x y : BoundedFamilies F) (h : ∀ᶠ n in atTop, x n = y n) : mk x = mk y := by
  apply (mk_eq_mk_iff _ _).mpr
  change Tendsto (fun n => ‖x n-y n‖) atTop (𝓝 0)
  apply tendsto_const_nhds.congr'
  filter_upwards [h] with n hn
  simp [hn]
end FamilyQuotient

def matrixStage (n : ℕ) : FinMatrix A n →⋆ₙₐ[ℂ] FamilyQuotient (FinMatrix A) :=
  FamilyQuotient.quotientHom.comp (matrixFamily n)

@[simp] lemma matrixStage_norm (n : ℕ) (M : FinMatrix A n) : ‖matrixStage n M‖ = ‖M‖ := by
  change ‖FamilyQuotient.mk (matrixFamily n M)‖ = _
  rw [FamilyQuotient.norm_mk_eq_limsup]
  calc
    _ = limsup (fun _ : ℕ => ‖M‖) atTop := limsup_congr (by
      filter_upwards [eventually_ge_atTop n] with m hm
      change ‖if h : n ≤ m then matrixInclusion h M else 0‖ = ‖M‖
      simp [hm])
    _ = ‖M‖ := limsup_const (b := ‖M‖)

lemma matrixStage_isometry (n : ℕ) : Isometry (matrixStage (A := A) n) :=
  AddMonoidHomClass.isometry_of_norm _ (matrixStage_norm n)

@[simp] lemma matrixStage_compatible {n m : ℕ} (h : n ≤ m) (M : FinMatrix A n) :
    matrixStage m (matrixInclusion h M) = matrixStage n M := by
  apply FamilyQuotient.mk_eq_of_eventually_eq
  filter_upwards [eventually_ge_atTop m] with k hk
  change (if g : m ≤ k then matrixInclusion g (matrixInclusion h M) else 0) =
    (if g : n ≤ k then matrixInclusion g M else 0)
  simp [hk, h.trans hk]
end CuntzTrace

end

end OAI
