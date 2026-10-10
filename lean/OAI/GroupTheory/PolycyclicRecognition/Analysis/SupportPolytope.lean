import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportNorm
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation

namespace OAI

/-!
# The finite covector body of the segment support norm

The positive-part formula is the maximum of finitely many actual linear
forms, obtained by choosing subsets of the weights in a word basis. This
constructs the support body used to define the finite height-label group.
-/

noncomputable section

namespace PolycyclicRecognition.SupportDatum

open scoped BigOperators

variable {W I B : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]
  (D : PolycyclicRecognition.SupportDatum W I B)

/-- A linear piece in the positive-part expression for segment support. -/
def supportForm (b : B) (S : Finset I) : W →L[ℝ] ℝ :=
  ∑ i ∈ S, (D.multiplicity b i : ℝ) • (D.weight i).toContinuousLinearMap

omit [Nonempty B] in
theorem supportForm_apply (b : B) (S : Finset I) (w : W) :
    D.supportForm b S w = ∑ i ∈ S, (D.multiplicity b i : ℝ) * D.weight i w := by
  simp [supportForm]

/-- The explicitly finite set of all linear pieces. -/
def supportForms : Finset (W →L[ℝ] ℝ) := by
  classical
  exact Finset.univ.image (fun p : B × Finset I => D.supportForm p.1 p.2)

omit [Nonempty B] in
theorem mem_supportForms (b : B) (S : Finset I) : D.supportForm b S ∈ D.supportForms := by
  classical
  exact Finset.mem_image.mpr ⟨(b, S), Finset.mem_univ _, rfl⟩

theorem supportForm_le (b : B) (S : Finset I) (w : W) :
    D.supportForm b S w ≤ D.segmentSupport w := by
  classical
  apply le_trans _ (D.basisSupport_le b w)
  rw [supportForm_apply]
  calc
    (∑ i ∈ S, (D.multiplicity b i : ℝ) * D.weight i w) ≤
        ∑ i ∈ S, (D.multiplicity b i : ℝ) * max 0 (D.weight i w) := by
      exact Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (le_max_right _ _) (Nat.cast_nonneg _))
    _ ≤ ∑ i, (D.multiplicity b i : ℝ) * max 0 (D.weight i w) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun i _ _ => mul_nonneg (Nat.cast_nonneg _) (le_max_left _ _))

/-- Every support value is attained by a member of the finite covector set. -/
theorem exists_supportForm_eq (w : W) :
    ∃ φ ∈ D.supportForms, φ w = D.segmentSupport w := by
  classical
  obtain ⟨b, _, hb⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun b => D.basisSupport b w)
  let S := Finset.univ.filter (fun i => 0 ≤ D.weight i w)
  refine ⟨D.supportForm b S, D.mem_supportForms b S, ?_⟩
  have h : D.supportForm b S w = D.basisSupport b w := by
    rw [supportForm_apply]
    simp only [S, Finset.sum_filter, basisSupport]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs with hi
    · rw [max_eq_right hi]
    · rw [max_eq_left (le_of_not_ge hi), mul_zero]
  exact h.trans hb.symm

theorem supportForms_le (w : W) {φ : W →L[ℝ] ℝ} (hφ : φ ∈ D.supportForms) :
    φ w ≤ D.segmentSupport w := by
  classical
  obtain ⟨⟨b, S⟩, _, rfl⟩ := Finset.mem_image.mp hφ
  exact D.supportForm_le b S w

/-- The finite pieces still separate the entire height space. -/
theorem supportForms_separate (w : W)
    (hw : ∀ φ ∈ D.supportForms, φ w = 0) : w = 0 := by
  obtain ⟨φ, hφ, heq⟩ := D.exists_supportForm_eq w
  exact (D.segmentSupport_eq_zero_iff w).mp (heq.symm.trans (hw φ hφ))

/-- The concrete support forms span the continuous dual height space. -/
theorem supportForms_span : Submodule.span ℝ (D.supportForms : Set (W →L[ℝ] ℝ)) = ⊤ := by
  classical
  let e : Module.Dual ℝ W ≃ₗ[ℝ] (W →L[ℝ] ℝ) := LinearMap.toContinuousLinearMap
  have hspan : Submodule.span ℝ (e ⁻¹' (D.supportForms : Set (W →L[ℝ] ℝ))) = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro w hw
    have hex : ∃ φ ∈ D.supportForms, φ w ≠ 0 := by
      by_contra h
      push Not at h
      exact hw (D.supportForms_separate w h)
    obtain ⟨φ, hφ, hφw⟩ := hex
    refine ⟨e.symm φ, ?_, hφw⟩
    change e (e.symm φ) ∈ D.supportForms
    simpa using hφ
  have hm := congrArg (Submodule.map e.toLinearMap) hspan
  rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at hm
  change Submodule.span ℝ (e '' (e ⁻¹' (D.supportForms : Set (W →L[ℝ] ℝ)))) = ⊤ at hm
  rw [Set.image_preimage_eq _ e.surjective] at hm
  exact hm

/-- The finite convex body is exactly the set of covectors dominated by the
segment support. This is the polarity step used to detect its symmetries. -/
theorem mem_supportBody_iff (φ : W →L[ℝ] ℝ) :
    φ ∈ convexHull ℝ (D.supportForms : Set (W →L[ℝ] ℝ)) ↔
      ∀ w, φ w ≤ D.segmentSupport w := by
  constructor
  · intro hφ w
    have hc : Convex ℝ {ψ : W →L[ℝ] ℝ | ψ w ≤ D.segmentSupport w} := by
      intro f hf g hg a b ha hb hab
      change a * f w + b * g w ≤ D.segmentSupport w
      calc
        a * f w + b * g w ≤ a * D.segmentSupport w + b * D.segmentSupport w :=
          add_le_add (mul_le_mul_of_nonneg_left hf ha) (mul_le_mul_of_nonneg_left hg hb)
        _ = D.segmentSupport w := by rw [← add_mul, hab, one_mul]
    exact (convexHull_min (fun ψ hψ => D.supportForms_le w hψ) hc) hφ
  · intro hφ
    by_contra hn
    obtain ⟨L, r, hbody, hrφ⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ (D.supportForms : Set (W →L[ℝ] ℝ)))
      (D.supportForms.finite_toSet.isClosed_convexHull ℝ) hn
    let e : Module.Dual ℝ W ≃ₗ[ℝ] (W →L[ℝ] ℝ) := LinearMap.toContinuousLinearMap
    let L₀ : Module.Dual ℝ (Module.Dual ℝ W) := L.toLinearMap.comp e.toLinearMap
    let w := (Module.evalEquiv ℝ W).symm L₀
    have heval (ψ : W →L[ℝ] ℝ) : L ψ = ψ w := by
      exact (Module.apply_evalEquiv_symm_apply ℝ W ψ.toLinearMap L₀).symm
    obtain ⟨ψ, hψ, heq⟩ := D.exists_supportForm_eq w
    have hlt := hbody ψ (subset_convexHull ℝ _ hψ)
    rw [heval ψ, heq] at hlt
    rw [heval φ] at hrφ
    exact (not_lt_of_ge (hφ w)) (hlt.trans hrφ)

end PolycyclicRecognition.SupportDatum

end

end OAI
