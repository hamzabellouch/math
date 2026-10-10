import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportPolytope
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolyhedralSymmetries
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

namespace OAI

/-!
# The actual finite group of height labels

The segment support determines a finite spanning body in the dual. A linear
support isometry preserves that body and hence permutes its vertices. This
proves finiteness of the group used to label stationary slopes and profiles.
-/

noncomputable section

namespace PolycyclicRecognition

variable {W I B : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]

/-- Precomposition of continuous covectors by a height automorphism. -/
def heightDualAction (A : W ≃L[ℝ] W) : (W →L[ℝ] ℝ) ≃L[ℝ] (W →L[ℝ] ℝ) :=
  A.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)

omit [FiniteDimensional ℝ W] in
@[simp] theorem heightDualAction_apply (A : W ≃L[ℝ] W) (φ : W →L[ℝ] ℝ) (w : W) :
    heightDualAction A φ w = φ (A w) := rfl

variable (D : SupportDatum W I B)

/-- A support isometry preserves the concrete dual support body. -/
theorem supportBody_preserved (A : W ≃L[ℝ] W)
    (hA : ∀ w, D.segmentSupport (A w) = D.segmentSupport w) :
    heightDualAction A '' convexHull ℝ (D.supportForms : Set (W →L[ℝ] ℝ)) =
      convexHull ℝ (D.supportForms : Set (W →L[ℝ] ℝ)) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨φ, hφ, rfl⟩
    apply (D.mem_supportBody_iff _).mpr
    intro w
    change φ (A w) ≤ D.segmentSupport w
    rw [← hA w]
    exact (D.mem_supportBody_iff φ).mp hφ (A w)
  · intro φ hφ
    refine ⟨heightDualAction A.symm φ, ?_, ?_⟩
    · apply (D.mem_supportBody_iff _).mpr
      intro w
      change φ (A.symm w) ≤ D.segmentSupport w
      have h := (D.mem_supportBody_iff φ).mp hφ (A.symm w)
      simpa only [← hA (A.symm w), A.apply_symm_apply] using h
    · ext w
      simp only [heightDualAction_apply, A.symm_apply_apply]

/-- There are finitely many possible linear labels. The finite set is
determined by the support data, independently of any quasi-isometry. -/
theorem finite_support_isometries :
    Set.Finite {A : W ≃L[ℝ] W | ∀ w, D.segmentSupport (A w) = D.segmentSupport w} := by
  classical
  let Labels := {A : W ≃L[ℝ] W // ∀ w, D.segmentSupport (A w) = D.segmentSupport w}
  let DualLabels := {A : (W →L[ℝ] ℝ) ≃L[ℝ] (W →L[ℝ] ℝ) //
    A '' convexHull ℝ (D.supportForms : Set (W →L[ℝ] ℝ)) =
      convexHull ℝ (D.supportForms : Set (W →L[ℝ] ℝ))}
  have hfinite : Finite DualLabels :=
    (finite_polytope_symmetries D.supportForms D.supportForms_span).to_subtype
  let f : Labels → DualLabels := fun A =>
    ⟨heightDualAction A.val, supportBody_preserved D A.val A.property⟩
  have hinj : Function.Injective f := by
    intro A B h
    apply Subtype.ext
    ext w
    apply sub_eq_zero.mp
    apply D.supportForms_separate
    intro φ _
    have hφ := congrArg (fun T : DualLabels => T.val φ w) h
    change φ (A.val w) = φ (B.val w) at hφ
    simpa only [map_sub] using sub_eq_zero.mpr hφ
  have : Finite Labels := Finite.of_injective f hinj
  exact Set.finite_coe_iff.mp this

/-- The linear labels form a subgroup, with the concrete finite support
isometry condition as membership. -/
def supportSymmetryGroup : Subgroup (W ≃L[ℝ] W) where
  carrier := {A | ∀ w, D.segmentSupport (A w) = D.segmentSupport w}
  one_mem' := by intro w; rfl
  mul_mem' := by
    intro A B hA hB w
    exact (hA (B w)).trans (hB w)
  inv_mem' := by
    intro A hA w
    change D.segmentSupport (A.symm w) = D.segmentSupport w
    have h := hA (A.symm w)
    simpa only [A.apply_symm_apply] using h.symm

instance finite_supportSymmetryGroup : Finite (supportSymmetryGroup D) :=
  (finite_support_isometries D).to_subtype

end PolycyclicRecognition

end

end OAI
