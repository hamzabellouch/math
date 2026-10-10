import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFiniteExistence
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorFiniteField

namespace OAI

/-! Backward finite-interval continuation of the actual clipped exterior equation. -/

open Set
namespace DefocusingNLS

noncomputable def radialExteriorReverseField (ν : ℂ) (n : ℕ) (m : ℝ → ℂ)
    (hm : Continuous m) (δ u T : ℝ) : C((Icc (0 : ℝ) T) × (ℂ × ℂ),ℂ × ℂ) where
  toFun x := -radialExteriorFiniteField ν n m δ (u-(x.1 : ℝ)) x.2
  continuous_toFun := ((radialExteriorFiniteField_continuous ν n m hm δ).comp
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd)).neg

@[simp] theorem radialExteriorReverseField_apply (ν : ℂ) (n : ℕ) (m : ℝ → ℂ)
    (hm : Continuous m) (δ u T : ℝ) (s : Icc (0 : ℝ) T) (z : ℂ × ℂ) :
    radialExteriorReverseField ν n m hm δ u T (s,z)=
      -radialExteriorFiniteField ν n m δ (u-(s : ℝ)) z := rfl

theorem radialExteriorReverseField_lipschitz (ν : ℂ) (n : ℕ) (m : ℝ → ℂ)
    (hm : Continuous m) (δ ρ u T : ℝ) (hδ : 0 ≤ δ)
    (hb : ∀ t ∈ Icc (u-T) u, ‖m t‖+2*δ ≤ ρ)
    (s : Icc (0 : ℝ) T) (z w : ℂ × ℂ) :
    ‖radialExteriorReverseField ν n m hm δ u T (s,z)-
      radialExteriorReverseField ν n m hm δ u T (s,w)‖ ≤
      (radialExteriorMatrixBound ν+Real.exp (2*u)/2+2*(2*(n : ℝ)+1)*ρ^(2*n))*‖z-w‖ := by
  have hs : u-(s : ℝ) ∈ Icc (u-T) u := by constructor <;> linarith [s.2.1,s.2.2]
  have h := radialExteriorFiniteField_difference ν n m δ ρ (u-s) hδ (hb _ hs) z w
  change ‖-radialExteriorFiniteField ν n m δ (u-s) z-
    -radialExteriorFiniteField ν n m δ (u-s) w‖ ≤ _
  rw [neg_sub_neg,norm_sub_rev]
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have he : Real.exp (2*(u-(s : ℝ))) ≤ Real.exp (2*u) := Real.exp_le_exp.mpr (by linarith [s.2.1])
  linarith

theorem exists_radialExterior_clipped_finite (ν : ℂ) (n : ℕ) (m : ℝ → ℂ)
    (hm : Continuous m) (δ ρ u T : ℝ) (hδ : 0 ≤ δ) (hT : 0 ≤ T)
    (hb : ∀ t ∈ Icc (u-T) u, ‖m t‖+2*δ ≤ ρ) (x : ℂ × ℂ) :
    ∃ Z : ℝ → ℂ × ℂ, Continuous Z ∧ Z u=x ∧
      ∀ t ∈ Icc (u-T) u, HasDerivAt Z (radialExteriorFiniteField ν n m δ t (Z t)) t := by
  have hρ : 0 ≤ ρ := by
    have h := hb u ⟨by linarith,le_rfl⟩
    exact (add_nonneg (norm_nonneg _) (mul_nonneg (by norm_num) hδ)).trans h
  let K := radialExteriorMatrixBound ν+Real.exp (2*u)/2+2*(2*(n : ℝ)+1)*ρ^(2*n)
  have hK : 0 ≤ K := by
    dsimp [K]
    have hB := (radialExteriorMatrixBound_pos ν).le
    positivity
  obtain ⟨α,hα,hinit,hd⟩ := exists_radial_finite_solution T hT
    (radialExteriorReverseField ν n m hm δ u T) K hK
    (radialExteriorReverseField_lipschitz ν n m hm δ ρ u T hδ hb) x
  let Z : ℝ → ℂ × ℂ := fun t => α (u-t)
  refine ⟨Z,hα.comp (continuous_const.sub continuous_id),?_,?_⟩
  · simpa only [Z,sub_self] using hinit
  · intro t ht
    have hr : u-t ∈ Icc (0 : ℝ) T := by constructor <;> linarith [ht.1,ht.2]
    have h := (hd (u-t) hr).scomp t ((hasDerivAt_id t).const_sub u)
    convert h using 1
    · rfl
    · rw [neg_one_smul,radialExteriorReverseField_apply,neg_neg]
      simp only [sub_sub_cancel,Z]

end DefocusingNLS

end OAI
