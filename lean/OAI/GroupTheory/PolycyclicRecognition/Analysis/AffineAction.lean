import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.GroupTheory.Index
import Mathlib.Tactic

namespace OAI

/-!
# Exact linear parts of a uniformly affine height quasi-action

A bounded error on a surjective real height quotient forces the linear parts
of a quasi-action to multiply exactly. This is the algebraic argument in
Proposition `prop:recognition-from-height` of *Quasi-isometric recognition of
virtually polycyclic groups*, Section 11.
-/

noncomputable section

namespace PolycyclicRecognition

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A real linear map that is uniformly bounded on its entire domain vanishes. -/
theorem linear_eq_zero_of_uniform_bound (L : W →L[ℝ] W)
    (C : ℝ) (hC : ∀ w, ‖L w‖ ≤ C) : L = 0 := by
  have hC0 : 0 ≤ C := by simpa using hC 0
  ext w
  apply norm_eq_zero.mp
  by_contra hne
  have hp : 0 < ‖L w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
  have ht : 0 < (C + 1) / ‖L w‖ := div_pos (by linarith) hp
  have h := hC (((C + 1) / ‖L w‖) • w)
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ht,
    div_mul_cancel₀ _ (ne_of_gt hp)] at h
  linarith

/-- Two affine maps a bounded distance apart have identical linear parts. -/
theorem linear_parts_eq_of_bounded_affine_difference
    (L M : W →L[ℝ] W) (b : W) (C : ℝ)
    (h : ∀ w, ‖b + L w - M w‖ ≤ C) : L = M := by
  have hz : L - M = 0 := linear_eq_zero_of_uniform_bound (L - M) (C + ‖b‖) fun w => by
    calc
      ‖(L - M) w‖ = ‖(b + L w - M w) - b‖ := by congr 1; simp; abel
      _ ≤ ‖b + L w - M w‖ + ‖b‖ := norm_sub_le _ _
      _ ≤ C + ‖b‖ := add_le_add (h w) le_rfl
  exact sub_eq_zero.mp hz

variable {H X : Type*} [Group H]

/-- Height-coordinate data for a quasi-action. All geometric estimates are
recorded explicitly, and no exact action law for `F` is assumed. -/
structure HeightQuasiAction (H X W : Type*) [Group H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] where
  height : X → W
  height_surjective : Function.Surjective height
  maps : H → X → X
  shift : H → W
  linear : H → W ≃L[ℝ] W
  error : ℝ
  error_nonneg : 0 ≤ error
  affine_error : ∀ h x,
    ‖height (maps h x) - (shift h + linear h (height x))‖ ≤ error
  composition_error : ℝ
  composition_nonneg : 0 ≤ composition_error
  composition_close : ∀ h k x,
    ‖height (maps h (maps k x)) - height (maps (h * k) x)‖ ≤ composition_error

namespace HeightQuasiAction

variable (Q : HeightQuasiAction H X W)

/-- The composition defect of the affine approximations has a bound independent
of the height argument. The bound may depend on the first linear map. -/
theorem affine_composition_bound (h k : H) (x : X) :
    ‖(Q.shift h + Q.linear h (Q.shift k) - Q.shift (h * k)) +
      Q.linear h (Q.linear k (Q.height x)) - Q.linear (h * k) (Q.height x)‖ ≤
      Q.error + ‖(Q.linear h).toContinuousLinearMap‖ * Q.error +
        Q.composition_error + Q.error := by
  let a := Q.height (Q.maps h (Q.maps k x))
  let b := Q.height (Q.maps (h * k) x)
  let c := Q.height (Q.maps k x)
  let u := Q.shift h + Q.linear h c
  let v := Q.shift h + Q.linear h (Q.shift k + Q.linear k (Q.height x))
  let z := Q.shift (h * k) + Q.linear (h * k) (Q.height x)
  have huv : ‖u - v‖ ≤ ‖(Q.linear h).toContinuousLinearMap‖ * Q.error := by
    calc
      ‖u - v‖ = ‖Q.linear h (c - (Q.shift k + Q.linear k (Q.height x)))‖ := by
        congr 1
        dsimp [u, v]
        rw [map_sub]
        abel
      _ ≤ ‖(Q.linear h).toContinuousLinearMap‖ *
          ‖c - (Q.shift k + Q.linear k (Q.height x))‖ :=
        (Q.linear h).toContinuousLinearMap.le_opNorm _
      _ ≤ ‖(Q.linear h).toContinuousLinearMap‖ * Q.error :=
        mul_le_mul_of_nonneg_left (Q.affine_error k x) (norm_nonneg _)
  have hva : ‖v - a‖ ≤ Q.error + ‖(Q.linear h).toContinuousLinearMap‖ * Q.error := by
    calc
      ‖v - a‖ ≤ ‖v - u‖ + ‖u - a‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖u - v‖ + ‖a - u‖ := by rw [norm_sub_rev v u, norm_sub_rev u a]
      _ ≤ ‖(Q.linear h).toContinuousLinearMap‖ * Q.error + Q.error :=
        add_le_add huv (Q.affine_error h (Q.maps k x))
      _ = _ := add_comm _ _
  have hvz : ‖v - z‖ ≤ Q.error + ‖(Q.linear h).toContinuousLinearMap‖ * Q.error +
      Q.composition_error + Q.error := by
    calc
      ‖v - z‖ ≤ ‖v - a‖ + ‖a - z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ‖v - a‖ + (‖a - b‖ + ‖b - z‖) :=
        add_le_add le_rfl (norm_sub_le_norm_sub_add_norm_sub a b z)
      _ ≤ (Q.error + ‖(Q.linear h).toContinuousLinearMap‖ * Q.error) +
          (Q.composition_error + Q.error) :=
        add_le_add hva (add_le_add (Q.composition_close h k x) (Q.affine_error (h * k) x))
      _ = _ := by ring
  convert hvz using 1
  dsimp [v, z]
  rw [map_add]
  congr 1
  abel

/-- Bounded quasi-action errors force the linear parts to compose exactly. -/
theorem linear_mul (h k : H) : Q.linear (h * k) = Q.linear h * Q.linear k := by
  have hc : (Q.linear h).toContinuousLinearMap.comp (Q.linear k).toContinuousLinearMap =
      (Q.linear (h * k)).toContinuousLinearMap := by
    apply linear_parts_eq_of_bounded_affine_difference _ _
      (Q.shift h + Q.linear h (Q.shift k) - Q.shift (h * k))
      (Q.error + ‖(Q.linear h).toContinuousLinearMap‖ * Q.error +
        Q.composition_error + Q.error)
    intro w
    obtain ⟨x, rfl⟩ := Q.height_surjective w
    exact Q.affine_composition_bound h k x
  ext w
  exact (congrArg (fun L : W →L[ℝ] W => L w) hc).symm

/-- The exact homomorphism of linear height parts. -/
def linearHom : H →* W ≃L[ℝ] W :=
  MonoidHom.mk' Q.linear Q.linear_mul

@[simp]
theorem linearHom_apply (h : H) : Q.linearHom h = Q.linear h := rfl

/-- When only finitely many linear parts occur, the subgroup with trivial
linear part has finite index, as required in the recognition argument. -/
theorem finiteIndex_linear_kernel (hfinite : Set.Finite (Set.range Q.linear)) :
    Q.linearHom.ker.FiniteIndex := by
  have hrange : Finite Q.linearHom.range := by
    exact hfinite.to_subtype
  exact Subgroup.finiteIndex_ker Q.linearHom

/-- Uniform defect bound for translations on the kernel of the linear action. -/
def translationDefect : ℝ :=
  Q.error + ‖(ContinuousLinearMap.id ℝ W)‖ * Q.error + Q.composition_error + Q.error

/-- Restricting the height shifts to the subgroup with trivial linear part gives
an additive map up to a uniformly bounded error. -/
theorem translation_defect_le (h k : Q.linearHom.ker) :
    ‖Q.shift (h * k) - Q.shift h - Q.shift k‖ ≤ Q.translationDefect := by
  obtain ⟨x, hx⟩ := Q.height_surjective 0
  have hh : Q.linear (h : H) = 1 := h.property
  have hb := Q.affine_composition_bound (h : H) (k : H) x
  rw [hx, map_zero, map_zero, map_zero, hh] at hb
  change ‖Q.shift (h : H) + Q.shift (k : H) - Q.shift ((h : H) * k) + 0 - 0‖ ≤ _ at hb
  have heq : Q.shift (h * k) - Q.shift h - Q.shift k =
      -(Q.shift (h : H) + Q.shift (k : H) - Q.shift ((h : H) * k) + 0 - 0) := by
    abel
  rw [heq, norm_neg]
  exact hb

end HeightQuasiAction

end PolycyclicRecognition

end

end OAI
