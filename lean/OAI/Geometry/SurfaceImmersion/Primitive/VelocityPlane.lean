import Mathlib

namespace OAI

/-! The normal-plane projection used in the velocity-circle construction. -/

noncomputable section

namespace ClosedSurfaceR4.VelocityPlane

abbrev Space := EuclideanSpace ℝ (Fin 4)

def tangentPlane (X Y : Space) : Submodule ℝ Space :=
  Submodule.span ℝ ({X, Y} : Set Space)

def oldNormal (X Y : Space) : Submodule ℝ Space := (tangentPlane X Y)ᗮ

def velocityPlane (Y C : Space) : Submodule ℝ Space := (tangentPlane Y C)ᗮ

lemma left_mem_tangent (X Y : Space) : X ∈ tangentPlane X Y :=
  Submodule.subset_span (by simp)

lemma right_mem_tangent (X Y : Space) : Y ∈ tangentPlane X Y :=
  Submodule.subset_span (by simp)

lemma coefficients_eq_zero {X Y : Space} (hXY : LinearIndependent ℝ ![X, Y])
    {a b : ℝ} (h : a • X + b • Y = 0) : a = 0 ∧ b = 0 := by
  have hc := (Fintype.linearIndependent_iff.mp hXY) ![a, b]
    (by simpa [Fin.sum_univ_two] using h)
  exact ⟨by simpa using hc 0, by simpa using hc 1⟩

/-- A nonzero longitudinal Hessian coefficient makes projection onto the new
velocity plane injective on the old normal plane. -/
theorem projection_kernel_on_oldNormal {X Y B C n : Space} {a b : ℝ}
    (hXY : LinearIndependent ℝ ![X, Y]) (ha : a ≠ 0)
    (hB : B ∈ oldNormal X Y) (hC : C = a • X + b • Y + B)
    (hn : n ∈ oldNormal X Y)
    (hp : (velocityPlane Y C).starProjection n = 0) : n = 0 := by
  have hmem : n ∈ tangentPlane Y C := by
    have hh := (Submodule.starProjection_apply_eq_zero_iff (velocityPlane Y C)).mp hp
    simpa only [velocityPlane, Submodule.orthogonal_orthogonal] using hh
  obtain ⟨c, d, hcd⟩ := Submodule.mem_span_pair.mp hmem
  have hqx : (tangentPlane X Y).starProjection X = X :=
    Submodule.starProjection_eq_self_iff.mpr (left_mem_tangent X Y)
  have hqy : (tangentPlane X Y).starProjection Y = Y :=
    Submodule.starProjection_eq_self_iff.mpr (right_mem_tangent X Y)
  have hqb : (tangentPlane X Y).starProjection B = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff (tangentPlane X Y)).mpr hB
  have hqn : (tangentPlane X Y).starProjection n = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff (tangentPlane X Y)).mpr hn
  have he := congrArg (tangentPlane X Y).starProjection hcd
  simp only [hC, map_add, map_smul, hqx, hqy, hqb, hqn, add_zero] at he
  have hz : (d * a) • X + (c + d * b) • Y = 0 := by
    calc
      (d * a) • X + (c + d * b) • Y = c • Y + d • (a • X + b • Y) := by
        simp only [smul_add, add_smul, smul_smul]
        abel
      _ = 0 := he
  obtain ⟨hda, hcb⟩ := coefficients_eq_zero hXY hz
  have hd : d = 0 := (mul_eq_zero.mp hda).resolve_right ha
  have hc : c = 0 := by simpa only [hd, zero_mul, add_zero] using hcb
  simpa only [hc, hd, zero_smul, add_zero] using hcd.symm

theorem projection_injective_on_oldNormal {X Y B C : Space} {a b : ℝ}
    (hXY : LinearIndependent ℝ ![X, Y]) (ha : a ≠ 0)
    (hB : B ∈ oldNormal X Y) (hC : C = a • X + b • Y + B) :
    Set.InjOn (velocityPlane Y C).starProjection (oldNormal X Y : Set Space) := by
  intro n hn m hm hnm
  apply sub_eq_zero.mp
  apply projection_kernel_on_oldNormal hXY ha hB hC
    ((oldNormal X Y).sub_mem hn hm)
  simp only [map_sub, hnm, sub_self]

theorem projected_normal_ne_zero {X Y B C n : Space} {a b : ℝ}
    (hXY : LinearIndependent ℝ ![X, Y]) (ha : a ≠ 0)
    (hB : B ∈ oldNormal X Y) (hC : C = a • X + b • Y + B)
    (hn : n ∈ oldNormal X Y) (hn0 : n ≠ 0) :
    (velocityPlane Y C).starProjection n ≠ 0 :=
  fun hp => hn0 (projection_kernel_on_oldNormal hXY ha hB hC hn hp)

/-- The projected old second form points oppositely to the projected
longitudinal tangent when the longitudinal Hessian coefficient is positive. -/
theorem projected_second_form {X Y B C : Space} {a b : ℝ}
    (hC : C = a • X + b • Y + B) :
    (velocityPlane Y C).starProjection B =
      -a • (velocityPlane Y C).starProjection X := by
  have hy : (velocityPlane Y C).starProjection Y = 0 := by
    apply (Submodule.starProjection_apply_eq_zero_iff (velocityPlane Y C)).mpr
    simpa only [velocityPlane, Submodule.orthogonal_orthogonal] using
      left_mem_tangent Y C
  have hc : (velocityPlane Y C).starProjection C = 0 := by
    apply (Submodule.starProjection_apply_eq_zero_iff (velocityPlane Y C)).mpr
    simpa only [velocityPlane, Submodule.orthogonal_orthogonal] using
      right_mem_tangent Y C
  have he : a • (velocityPlane Y C).starProjection X +
      (velocityPlane Y C).starProjection B = 0 := by
    calc
      _ = (velocityPlane Y C).starProjection (a • X + b • Y + B) := by
        simp only [map_add, map_smul, hy, smul_zero, add_zero]
      _ = (velocityPlane Y C).starProjection C := congrArg _ hC.symm
      _ = 0 := hc
  simpa only [neg_smul] using (eq_neg_of_add_eq_zero_right he)

/-- Replacing the projected velocity by a longer vector in the same plane
adds precisely a rank-one term to the metric. -/
theorem leading_metric {X Y C V : Space} {a : ℝ}
    (hV : V ∈ velocityPlane Y C)
    (hR : ‖V‖ ^ 2 = ‖(velocityPlane Y C).starProjection X‖ ^ 2 + a ^ 2) :
    ‖X - (velocityPlane Y C).starProjection X + V‖ ^ 2 = ‖X‖ ^ 2 + a ^ 2 ∧
      inner ℝ (X - (velocityPlane Y C).starProjection X + V) Y = inner ℝ X Y := by
  let P := velocityPlane Y C
  have hp : P.starProjection X ∈ P := P.orthogonalProjectionOnto X |>.property
  have hxv : inner ℝ (X - P.starProjection X) V = 0 :=
    P.starProjection_inner_eq_zero X V hV
  have hxp : inner ℝ (X - P.starProjection X) (P.starProjection X) = 0 :=
    P.starProjection_inner_eq_zero X _ hp
  have hold : ‖X‖ ^ 2 = ‖X - P.starProjection X‖ ^ 2 + ‖P.starProjection X‖ ^ 2 := by
    calc
      ‖X‖ ^ 2 = ‖X - P.starProjection X + P.starProjection X‖ ^ 2 := by
        rw [sub_add_cancel]
      _ = _ := by rw [norm_add_sq_real, hxp]; ring
  have hvy : inner ℝ V Y = 0 := by
    exact (real_inner_comm Y V).trans
      ((Submodule.mem_orthogonal _ _).mp hV Y (left_mem_tangent Y C))
  have hpy : inner ℝ (P.starProjection X) Y = 0 := by
    exact (real_inner_comm Y (P.starProjection X)).trans
      ((Submodule.mem_orthogonal _ _).mp hp Y (left_mem_tangent Y C))
  constructor
  · change ‖X - P.starProjection X + V‖ ^ 2 = _
    rw [norm_add_sq_real, hxv]
    linarith
  · change inner ℝ (X - P.starProjection X + V) Y = _
    simp only [inner_add_left, inner_sub_left, hvy, hpy, sub_zero, add_zero]

end ClosedSurfaceR4.VelocityPlane

end

end OAI
