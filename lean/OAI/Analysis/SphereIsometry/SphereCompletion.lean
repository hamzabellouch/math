import OAI.Analysis.SphereIsometry.Basic
import Mathlib.Analysis.Normed.Module.Completion

namespace OAI

/-!
# Unit spheres and completion

The unit sphere of a normed space is dense in the unit sphere of its ambient
completion. This identifies its metric completion with that completed sphere.
An actual sphere isometry and its inverse therefore extend to the completed
spheres, with exact preservation of the ambient fixed-radius defect.

No completeness of the original spaces, compactness, or separability is used.
-/

noncomputable section

open UniformSpace

namespace Tingley

universe u v

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A unit sphere is complete when its ambient normed space is complete. -/
instance UnitSphere.instCompleteSpace [CompleteSpace E] : CompleteSpace (UnitSphere E) :=
  (isClosed_eq continuous_norm continuous_const).completeSpace_coe

/-- The canonical ambient completion embedding restricted to the unit sphere. -/
def sphereCoe (E : Type u) [NormedAddCommGroup E] :
    UnitSphere E → UnitSphere (Completion E) := fun x =>
  ⟨(x : E), by simpa only [Completion.norm_coe] using x.property⟩

omit [NormedSpace ℝ E] in
@[simp] theorem sphereCoe_val (x : UnitSphere E) :
    (sphereCoe E x : Completion E) = ((x : E) : Completion E) := rfl

theorem sphereCoe_isometry (E : Type u) [NormedAddCommGroup E] :
    Isometry (sphereCoe E) := by
  apply Isometry.of_dist_eq
  intro x y
  change dist ((x : E) : Completion E) ((y : E) : Completion E) =
    dist (x : E) (y : E)
  exact Completion.dist_eq (x : E) (y : E)

private theorem norm_normalize_sub (x : E) (hx : x ≠ 0) :
    ‖(normalize x hx : E) - x‖ = |1 - ‖x‖| := by
  calc
    _ = ‖(1 - ‖x‖) • (normalize x hx : E)‖ := by
      congr 1
      rw [sub_smul, one_smul, norm_smul_normalize]
    _ = |1 - ‖x‖| := by
      rw [norm_smul, Real.norm_eq_abs, UnitSphere.norm_coe, mul_one]

/-- Normalizing close old vectors proves density in the completed unit sphere. -/
theorem sphereCoe_denseRange (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    DenseRange (sphereCoe E) := by
  refine Metric.denseRange_iff.mpr ?_
  intro z ε hε
  have hδ : 0 < min (1 : ℝ) (ε / 2) := lt_min zero_lt_one (by linarith)
  obtain ⟨x, hdx⟩ :=
    (Completion.denseRange_coe : DenseRange ((↑) : E → Completion E)).exists_dist_lt
      (z : Completion E) hδ
  have habs : |1 - ‖x‖| ≤ dist (z : Completion E) (x : Completion E) := by
    simpa only [UnitSphere.norm_coe, Completion.norm_coe, dist_eq_norm] using
      abs_norm_sub_norm_le (z : Completion E) (x : Completion E)
  have hnorm : 0 < ‖x‖ := by
    have ha := (le_abs_self (1 - ‖x‖)).trans habs
    have hb := hdx.trans_le (min_le_left (1 : ℝ) (ε / 2))
    linarith
  have hx : x ≠ 0 := norm_pos_iff.mp hnorm
  have hrad : dist (x : Completion E) ((normalize x hx : E) : Completion E) =
      |1 - ‖x‖| := by
    rw [dist_comm, Completion.dist_eq, dist_eq_norm, norm_normalize_sub]
  have hsmall := hdx.trans_le (min_le_right (1 : ℝ) (ε / 2))
  refine ⟨normalize x hx, ?_⟩
  change dist (z : Completion E) ((normalize x hx : E) : Completion E) < ε
  calc
    _ ≤ dist (z : Completion E) (x : Completion E) +
        dist (x : Completion E) ((normalize x hx : E) : Completion E) :=
      dist_triangle _ _ _
    _ = dist (z : Completion E) (x : Completion E) + |1 - ‖x‖| := by rw [hrad]
    _ ≤ 2 * dist (z : Completion E) (x : Completion E) := by linarith
    _ < ε := by linarith

private def sphereCompletionMap (E : Type u) [NormedAddCommGroup E] :
    Completion (UnitSphere E) → UnitSphere (Completion E) :=
  Completion.extension (sphereCoe E)

private theorem sphereCompletionMap_isometry (E : Type u) [NormedAddCommGroup E] :
    Isometry (sphereCompletionMap E) :=
  (sphereCoe_isometry E).completion_extension

omit [NormedSpace ℝ E] in
private theorem sphereCompletionMap_coe (x : UnitSphere E) :
    sphereCompletionMap E (x : Completion (UnitSphere E)) = sphereCoe E x :=
  Completion.extension_coe (sphereCoe_isometry E).uniformContinuous x

private theorem sphereCompletionMap_surjective
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Function.Surjective (sphereCompletionMap E) := by
  have hclosed : IsClosed (Set.range (sphereCompletionMap E)) :=
    (sphereCompletionMap_isometry E).isClosedEmbedding.isClosed_range
  exact isClosed_property (sphereCoe_denseRange E) hclosed fun x =>
    ⟨(x : Completion (UnitSphere E)), sphereCompletionMap_coe x⟩

/-- The metric completion of the old sphere is the sphere of the ambient completion. -/
def sphereCompletionEquiv (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Completion (UnitSphere E) ≃ᵢ UnitSphere (Completion E) :=
  { Equiv.ofBijective (sphereCompletionMap E)
      ⟨(sphereCompletionMap_isometry E).injective, sphereCompletionMap_surjective E⟩ with
    isometry_toFun := sphereCompletionMap_isometry E }

@[simp] theorem sphereCompletionEquiv_coe (x : UnitSphere E) :
    sphereCompletionEquiv E (x : Completion (UnitSphere E)) = sphereCoe E x :=
  sphereCompletionMap_coe x

@[simp] theorem sphereCompletionEquiv_symm_coe (x : UnitSphere E) :
    (sphereCompletionEquiv E).symm (sphereCoe E x) =
      (x : Completion (UnitSphere E)) := by
  apply (sphereCompletionEquiv E).injective
  simp only [IsometryEquiv.apply_symm_apply, sphereCompletionEquiv_coe]

private def sphereIsometryCompletion (f : UnitSphere E ≃ᵢ UnitSphere F) :
    Completion (UnitSphere E) ≃ᵢ Completion (UnitSphere F) where
  toFun := Completion.map f
  invFun := Completion.map f.symm
  left_inv x := by
    have h := congr_fun
      (Completion.map_comp f.symm.isometry.uniformContinuous f.isometry.uniformContinuous) x
    rw [f.symm_comp_self, Completion.map_id] at h
    exact h
  right_inv y := by
    have h := congr_fun
      (Completion.map_comp f.isometry.uniformContinuous f.symm.isometry.uniformContinuous) y
    rw [f.self_comp_symm, Completion.map_id] at h
    exact h
  isometry_toFun := f.isometry.completion_map

/-- Extend the actual sphere isometry and its inverse through the sphere completions. -/
def completedSphereEquiv (f : UnitSphere E ≃ᵢ UnitSphere F) :
    UnitSphere (Completion E) ≃ᵢ UnitSphere (Completion F) :=
  ((sphereCompletionEquiv E).symm.trans (sphereIsometryCompletion f)).trans
    (sphereCompletionEquiv F)

@[simp] theorem completedSphereEquiv_coe (f : UnitSphere E ≃ᵢ UnitSphere F)
    (x : UnitSphere E) :
    completedSphereEquiv f (sphereCoe E x) = sphereCoe F (f x) := by
  change sphereCompletionEquiv F
    (Completion.map f ((sphereCompletionEquiv E).symm (sphereCoe E x))) = sphereCoe F (f x)
  rw [sphereCompletionEquiv_symm_coe, Completion.map_coe f.isometry.uniformContinuous,
    sphereCompletionEquiv_coe]

@[simp] theorem completedSphereEquiv_symm (f : UnitSphere E ≃ᵢ UnitSphere F) :
    (completedSphereEquiv f).symm = completedSphereEquiv f.symm := by
  apply IsometryEquiv.ext
  intro y
  rfl

/-- The canonical ambient embedding preserves all real scalar difference norms. -/
theorem norm_completion_sub_smul (x y : E) (q : ℝ) :
    ‖(x : Completion E) - q • (y : Completion E)‖ = ‖x - q • y‖ := by
  rw [← Completion.coe_smul, ← Completion.coe_sub, Completion.norm_coe]

/-- The defect on embedded old points is preserved for every real scalar. -/
@[simp] theorem signedDefect_completedSphereEquiv_coe
    (f : UnitSphere E ≃ᵢ UnitSphere F) (q : ℝ) (x y : UnitSphere E) :
    signedDefect (completedSphereEquiv f) q (sphereCoe E x) (sphereCoe E y) =
      signedDefect f q x y := by
  unfold signedDefect
  rw [completedSphereEquiv_coe, completedSphereEquiv_coe]
  simp only [sphereCoe_val, norm_completion_sub_smul]

/-- The fixed-radius signed defect is continuous on pairs of unit points. -/
theorem continuous_signedDefect_pair (f : UnitSphere E ≃ᵢ UnitSphere F) (q : ℝ) :
    Continuous (fun p : UnitSphere E × UnitSphere E => signedDefect f q p.1 p.2) := by
  have hx : Continuous (fun p : UnitSphere E × UnitSphere E => (p.1 : E)) :=
    continuous_subtype_val.comp continuous_fst
  have hy : Continuous (fun p : UnitSphere E × UnitSphere E => (p.2 : E)) :=
    continuous_subtype_val.comp continuous_snd
  have hfx : Continuous (fun p : UnitSphere E × UnitSphere E => (f p.1 : F)) :=
    continuous_subtype_val.comp (f.continuous.comp continuous_fst)
  have hfy : Continuous (fun p : UnitSphere E × UnitSphere E => (f p.2 : F)) :=
    continuous_subtype_val.comp (f.continuous.comp continuous_snd)
  exact (hfx.sub (hfy.const_smul q)).norm.sub (hx.sub (hy.const_smul q)).norm

/-- Every fixed-radius bound passes to all pairs in the completed spheres. -/
theorem HasDefectBound.completedSphereEquiv {f : UnitSphere E ≃ᵢ UnitSphere F} {M : ℝ}
    (h : HasDefectBound f M) : HasDefectBound (completedSphereEquiv f) M := by
  intro q hq x y
  have hclosed : IsClosed {p : UnitSphere (Completion E) × UnitSphere (Completion E) |
      |signedDefect (Tingley.completedSphereEquiv f) q p.1 p.2| ≤ M} :=
    isClosed_le (continuous_signedDefect_pair (Tingley.completedSphereEquiv f) q).abs continuous_const
  exact isClosed_property2
    (p := fun a b : UnitSphere (Completion E) =>
      |signedDefect (Tingley.completedSphereEquiv f) q a b| ≤ M)
    (sphereCoe_denseRange E) hclosed
    (fun a b => by simpa only [signedDefect_completedSphereEquiv_coe] using h q hq a b) x y

/-- An attained signed defect remains attained at the same embedded points and scalar. -/
theorem attainedDefect_completedSphereEquiv (f : UnitSphere E ≃ᵢ UnitSphere F)
    {q M : ℝ} {x y : UnitSphere E} (h : signedDefect f q x y = M) :
    signedDefect (completedSphereEquiv f) q (sphereCoe E x) (sphereCoe E y) = M := by
  rw [signedDefect_completedSphereEquiv_coe]
  exact h

end Tingley

end

end OAI
