import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.InnerProductSpace.l2Space

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped InnerProductSpace ENNReal
variable {A ι : Type*} [CStarAlgebra A] {H : ι → Type*}
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
variable [∀ i, CompleteSpace (H i)]
variable (ρ : ∀ i, A →⋆ₐ[ℂ] (H i →L[ℂ] H i))

def hilbertSumAction (a : A) (x : lp H 2) : lp H 2 :=
  ⟨fun i => ρ i a (x i), ((lp.memℓp x).norm.const_mul ‖a‖).mono (fun i =>
    ((ρ i a).le_opNorm (x i)).trans (mul_le_mul_of_nonneg_right
      (NonUnitalStarAlgHom.norm_apply_le (ρ i).toNonUnitalStarAlgHom a) (norm_nonneg _)))⟩

lemma hilbertSumAction_norm_le (a : A) (x : lp H 2) :
    ‖hilbertSumAction ρ a x‖ ≤ ‖a‖ * ‖x‖ := by
  let y : lp H 2 := (‖a‖ : ℂ) • x
  have hy : ∀ i, ‖hilbertSumAction ρ a x i‖ ≤ ‖y i‖ := by
    intro i
    change ‖ρ i a (x i)‖ ≤ ‖(‖a‖ : ℂ) • x i‖
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg a)]
    exact ((ρ i a).le_opNorm (x i)).trans (mul_le_mul_of_nonneg_right
      (NonUnitalStarAlgHom.norm_apply_le (ρ i).toNonUnitalStarAlgHom a) (norm_nonneg _))
  have hn := lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0) hy
  refine hn.trans_eq ((norm_smul (‖a‖ : ℂ) x).trans ?_)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg a)]

def hilbertSumOperator (a : A) : lp H 2 →L[ℂ] lp H 2 :=
  LinearMap.mkContinuous
    { toFun := hilbertSumAction ρ a
      map_add' := fun x y => by apply lp.ext; funext i; exact (ρ i a).map_add _ _
      map_smul' := fun c x => by apply lp.ext; funext i; exact (ρ i a).map_smul c _ }
    ‖a‖ (hilbertSumAction_norm_le ρ a)

lemma hilbertSumOperator_apply (a : A) (x : lp H 2) (i : ι) :
    hilbertSumOperator ρ a x i = ρ i a (x i) := rfl

def hilbertSumRepresentation : A →⋆ₐ[ℂ] (lp H 2 →L[ℂ] lp H 2) where
  toFun := hilbertSumOperator ρ
  map_zero' := by ext x i; exact congrArg (fun f : H i →L[ℂ] H i => f (x i)) (map_zero (ρ i))
  map_one' := by ext x i; exact congrArg (fun f : H i →L[ℂ] H i => f (x i)) (map_one (ρ i))
  map_add' a b := by ext x i; exact congrArg (fun f : H i →L[ℂ] H i => f (x i)) (map_add (ρ i) a b)
  map_mul' a b := by ext x i; exact congrArg (fun f : H i →L[ℂ] H i => f (x i)) (map_mul (ρ i) a b)
  commutes' c := by
    ext x i
    exact congrArg (fun f : H i →L[ℂ] H i => f (x i)) ((ρ i).commutes c)
  map_star' a := by
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro x y
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    apply tsum_congr
    intro i
    change ⟪ρ i (star a) (x i), y i⟫_ℂ = ⟪x i, ρ i a (y i)⟫_ℂ
    rw [map_star]
    exact ContinuousLinearMap.adjoint_inner_left _ _ _

lemma hilbertSumRepresentation_apply (a : A) (x : lp H 2) (i : ι) :
    hilbertSumRepresentation ρ a x i = ρ i a (x i) := rfl

lemma hilbertSumRepresentation_eq_iff (a b : A) :
    hilbertSumRepresentation ρ a = hilbertSumRepresentation ρ b ↔ ∀ i, ρ i a = ρ i b := by
  classical
  constructor
  · intro h i
    ext x
    have hh := congrArg (fun f : lp H 2 →L[ℂ] lp H 2 => f (lp.single 2 i x) i) h
    simpa only [hilbertSumRepresentation_apply, lp.single_apply, Pi.single_eq_same] using hh
  · intro h
    ext x i
    exact congrArg (fun f : H i →L[ℂ] H i => f (x i)) (h i)
end CuntzPureness

end

end OAI
