import OAI.Analysis.LipschitzFree.Model

namespace OAI

/-!
# Evaluation isometries, completeness, and closed-span induction
-/

noncomputable section
open scoped BigOperators ENNReal

namespace DiscreteFree

section EvaluationGeometry

variable {M : Type*} [MetricSpace M]

def distanceTest (o y : M) : Lip0 o :=
  Lip0.ofBound o (fun z => dist z y - dist o y) (by simp) 1 (by norm_num)
    (fun x z => by simpa using abs_dist_sub_le x z y)

@[simp] theorem distanceTest_apply (o y z : M) :
    distanceTest o y z = dist z y - dist o y := rfl

theorem distanceTest_norm_le (o y : M) : ‖distanceTest o y‖ ≤ 1 := by
  apply (Lip0.norm_le_iff _ (by norm_num)).mpr
  intro x z
  simpa using abs_dist_sub_le x z y

theorem evaluation_sub_norm (o x y : M) : ‖evaluation o x - evaluation o y‖ = dist x y := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ dist_nonneg
    intro f
    change ‖f x - f y‖ ≤ dist x y * ‖f‖
    rw [Real.norm_eq_abs, mul_comm]
    exact Lip0.sub_le f x y
  · have h := (evaluation o x - evaluation o y).le_opNorm_of_le (distanceTest_norm_le o y)
    simpa [Real.norm_eq_abs, abs_of_nonneg dist_nonneg] using h

@[simp] theorem evaluation_norm (o x : M) : ‖evaluation o x‖ = dist x o := by
  simpa using evaluation_sub_norm o x o

@[simp] theorem delta_base (o : M) : delta o o = 0 := by
  apply Subtype.ext
  exact evaluation_base o

@[simp] theorem delta_sub_norm (o x y : M) : ‖delta o x - delta o y‖ = dist x y :=
  evaluation_sub_norm o x y

@[simp] theorem delta_norm (o x : M) : ‖delta o x‖ = dist x o := evaluation_norm o x

theorem delta_isometry (o : M) : Isometry (delta o) := by
  apply isometry_iff_dist_eq.mpr
  intro x y
  rw [dist_eq_norm, delta_sub_norm]

instance (o : M) : CompleteSpace (FreeSpace o) :=
  (Submodule.isClosed_topologicalClosure (Submodule.span ℝ (Set.range (evaluation o)))).completeSpace_coe

theorem freeSpace_induction {o : M} (P : FreeSpace o → Prop)
    (hclosed : IsClosed {u | P u}) (hzero : P 0)
    (hadd : ∀ u v, P u → P v → P (u + v))
    (hsmul : ∀ (c : ℝ) u, P u → P (c • u)) (heval : ∀ x, P (delta o x)) :
    ∀ u, P u := by
  let S : Submodule ℝ (FreeSpace o) :=
    { carrier := {u | P u}, zero_mem' := hzero, add_mem' := fun {u v} => hadd u v, smul_mem' := hsmul }
  let incl : FreeSpace o →L[ℝ] (Lip0 o →L[ℝ] ℝ) :=
    (freeSubmodule o).subtypeL
  have hinc : IsClosedMap incl :=
    (Submodule.isClosed_topologicalClosure (Submodule.span ℝ (Set.range (evaluation o)))).isClosedEmbedding_subtypeVal.isClosedMap
  have himage : IsClosed (S.map incl.toLinearMap : Set (Lip0 o →L[ℝ] ℝ)) :=
    by
      change IsClosed (incl '' {u | P u})
      exact hinc _ hclosed
  have hspan : Submodule.span ℝ (Set.range (evaluation o)) ≤ S.map incl.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    exact ⟨delta o x, heval x, rfl⟩
  have hAll : freeSubmodule o ≤ S.map incl.toLinearMap :=
    Submodule.topologicalClosure_minimal _ hspan himage
  intro u
  obtain ⟨v, hv, hvu⟩ := hAll u.property
  have hvu' : v = u := Subtype.ext hvu
  change P v at hv
  simpa [hvu'] using hv

end EvaluationGeometry

end DiscreteFree

end

end OAI
