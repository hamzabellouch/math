import OAI.MeasureTheory.Falconer.Shells.AngularLengthShellCover
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem angular_comparable_shell_union (S : Set (Fin 4 → Plane)) (a h : ℕ)
    (hu : ∀ x ∈ S, max (dist (x 0) (x 1)) (dist (x 2) (x 3)) ≤ 2*(2:ℝ)^(-(a:ℝ)))
    (hf : ∀ x ∈ S, 16*(2:ℝ)^(-(h:ℝ)) < max (dist (x 0) (x 1)) (dist (x 2) (x 3))) :
    S ∩ angularLengthComparable = ⋃ b ∈ Finset.Icc (a+9) (h+5), S ∩ angularLengthShell b := by
  ext x
  constructor
  · intro hx
    obtain ⟨b,hb,hs⟩ := angularLengthShell_cover hx.2 (hu x hx.1) (hf x hx.1)
    exact mem_iUnion.mpr ⟨b,mem_iUnion.mpr ⟨hb,hx.1,hs⟩⟩
  · intro hx
    obtain ⟨b,hx⟩ := mem_iUnion.mp hx
    obtain ⟨_,hx⟩ := mem_iUnion.mp hx
    exact ⟨hx.1,hx.2.1⟩

theorem angular_length_integral_partition (μ : Measure (Fin 4 → Plane))
    (S : Set (Fin 4 → Plane)) (hS : MeasurableSet S) (a h : ℕ)
    (hu : ∀ x ∈ S, max (dist (x 0) (x 1)) (dist (x 2) (x 3)) ≤ 2*(2:ℝ)^(-(a:ℝ)))
    (hf : ∀ x ∈ S, 16*(2:ℝ)^(-(h:ℝ)) < max (dist (x 0) (x 1)) (dist (x 2) (x 3)))
    (F : (Fin 4 → Plane) → ℂ) (hF : IntegrableOn F S μ) :
    (∫ x in S, F x ∂μ) =
      (∫ x in S ∩ angularLengthLeft, F x ∂μ) +
      (∫ x in S ∩ angularLengthRight, F x ∂μ) +
      ∑ b ∈ Finset.Icc (a+9) (h+5), ∫ x in S ∩ angularLengthShell b, F x ∂μ := by
  have hi (T : Set (Fin 4 → Plane)) : IntegrableOn F (S ∩ T) μ := hF.mono_set inter_subset_left
  have hC : (∫ x in S ∩ angularLengthComparable, F x ∂μ) =
      ∑ b ∈ Finset.Icc (a+9) (h+5), ∫ x in S ∩ angularLengthShell b, F x ∂μ := by
    rw [angular_comparable_shell_union S a h hu hf]
    apply integral_biUnion_finset
    · exact fun b _ => hS.inter (measurable_angularLengthShell b)
    · intro b _ c _ hbc
      exact (angularLengthShell_disjoint hbc).mono inter_subset_right inter_subset_right
    · exact fun b _ => hi _
  have htotal : S = ((S ∩ angularLengthLeft) ∪ (S ∩ angularLengthRight)) ∪
      (S ∩ angularLengthComparable) := by
    ext x
    constructor
    · intro hx
      rcases angular_length_trichotomy x with hl | hr | hc
      · exact Or.inl (Or.inl ⟨hx,hl⟩)
      · exact Or.inl (Or.inr ⟨hx,hr⟩)
      · exact Or.inr ⟨hx,hc⟩
    · rintro ((hx | hx) | hx) <;> exact hx.1
  have hd : Disjoint ((S ∩ angularLengthLeft) ∪ (S ∩ angularLengthRight))
      (S ∩ angularLengthComparable) := by
    apply Set.disjoint_left.mpr
    intro x hx hc
    rcases hx with hl | hr
    · exact Set.disjoint_left.mp angular_length_left_comparable_disjoint hl.2 hc.2
    · exact Set.disjoint_left.mp angular_length_right_comparable_disjoint hr.2 hc.2
  calc
    _ = ∫ x in ((S ∩ angularLengthLeft) ∪ (S ∩ angularLengthRight)) ∪
        (S ∩ angularLengthComparable), F x ∂μ := congrArg (fun T => ∫ x in T, F x ∂μ) htotal
    _ = _ := by
      rw [setIntegral_union hd (hS.inter measurable_angularLengthComparable)
        (hF.mono_set (union_subset inter_subset_left inter_subset_left)) (hi _)]
      rw [setIntegral_union (angular_length_left_right_disjoint.mono inter_subset_right inter_subset_right)
        (hS.inter measurable_angularLengthRight) (hi _) (hi _),hC]

end PlanarFalconer

end OAI
