import Mathlib
import OAI.Computability.VertexCover.Reduction.CompatibleSingleton

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.LabelCover

noncomputable def compatibleSelections (Φ : LabelCover) (d : ℕ) :
    Finset (Finset (Φ.Coordinate d)) := by
  classical
  exact Finset.univ.filter Φ.Compatible

@[simp] theorem mem_compatibleSelections (Φ : LabelCover) {d : ℕ}
    (I : Finset (Φ.Coordinate d)) : I ∈ Φ.compatibleSelections d ↔ Φ.Compatible I := by
  classical
  simp [compatibleSelections]

theorem compatible_empty (Φ : LabelCover) (d : ℕ) :
    Φ.Compatible (∅ : Finset (Φ.Coordinate d)) := by
  simp [Compatible]

theorem compatibleSelections_nonempty (Φ : LabelCover) (d : ℕ) :
    (Φ.compatibleSelections d).Nonempty :=
  ⟨∅, (mem_compatibleSelections Φ ∅).mpr (Φ.compatible_empty d)⟩

noncomputable def compatibilityNorm (Φ : LabelCover) {d : ℕ}
    (z : Φ.Coordinate d → ℝ) : ℝ :=
  (Φ.compatibleSelections d).sup' (Φ.compatibleSelections_nonempty d)
    (fun I => |∑ p ∈ I, z p|)

theorem form_le_norm (Φ : LabelCover) {d : ℕ} (z : Φ.Coordinate d → ℝ)
    (I : Finset (Φ.Coordinate d)) (hI : Φ.Compatible I) :
    |∑ p ∈ I, z p| ≤ Φ.compatibilityNorm z := by
  exact Finset.le_sup' (fun J : Finset (Φ.Coordinate d) => |∑ p ∈ J, z p|)
    ((mem_compatibleSelections Φ I).mpr hI)

theorem norm_le_iff (Φ : LabelCover) {d : ℕ} (z : Φ.Coordinate d → ℝ) (b : ℝ) :
    Φ.compatibilityNorm z ≤ b ↔ ∀ I, Φ.Compatible I → |∑ p ∈ I, z p| ≤ b := by
  constructor
  · intro hb I hI
    exact (Φ.form_le_norm z I hI).trans hb
  · intro h
    exact Finset.sup'_le _ _ (fun I hI => h I ((mem_compatibleSelections Φ I).mp hI))

theorem norm_nonneg (Φ : LabelCover) {d : ℕ} (z : Φ.Coordinate d → ℝ) :
    0 ≤ Φ.compatibilityNorm z := by
  simpa using Φ.form_le_norm z ∅ (Φ.compatible_empty d)

theorem norm_zero (Φ : LabelCover) (d : ℕ) :
    Φ.compatibilityNorm (fun _ : Φ.Coordinate d => (0 : ℝ)) = 0 := by
  apply le_antisymm ((Φ.norm_le_iff _ _).mpr ?_) (Φ.norm_nonneg _)
  intro I _
  simp

theorem coordinate_le_norm (Φ : LabelCover) {d : ℕ} (z : Φ.Coordinate d → ℝ)
    (p : Φ.Coordinate d) : |z p| ≤ Φ.compatibilityNorm z := by
  classical
  simpa using Φ.form_le_norm z {p} (Φ.compatible_singleton p)

theorem norm_eq_zero_iff (Φ : LabelCover) {d : ℕ} (z : Φ.Coordinate d → ℝ) :
    Φ.compatibilityNorm z = 0 ↔ z = 0 := by
  constructor
  · intro h
    funext p
    have hh := Φ.coordinate_le_norm z p
    rw [h] at hh
    exact abs_nonpos_iff.mp hh
  · rintro rfl
    exact Φ.norm_zero d

theorem norm_add_le (Φ : LabelCover) {d : ℕ} (z w : Φ.Coordinate d → ℝ) :
    Φ.compatibilityNorm (z + w) ≤ Φ.compatibilityNorm z + Φ.compatibilityNorm w := by
  apply (Φ.norm_le_iff _ _).mpr
  intro I hI
  calc
    |∑ p ∈ I, (z + w) p| = |(∑ p ∈ I, z p) + ∑ p ∈ I, w p| := by
      simp only [Pi.add_apply, Finset.sum_add_distrib]
    _ ≤ |∑ p ∈ I, z p| + |∑ p ∈ I, w p| := abs_add_le _ _
    _ ≤ Φ.compatibilityNorm z + Φ.compatibilityNorm w :=
      add_le_add (Φ.form_le_norm z I hI) (Φ.form_le_norm w I hI)

theorem norm_mul (Φ : LabelCover) {d : ℕ} (a : ℝ) (z : Φ.Coordinate d → ℝ) :
    Φ.compatibilityNorm (fun p => a * z p) = |a| * Φ.compatibilityNorm z := by
  apply le_antisymm
  · apply (Φ.norm_le_iff _ _).mpr
    intro I hI
    rw [← Finset.mul_sum, abs_mul]
    exact mul_le_mul_of_nonneg_left (Φ.form_le_norm z I hI) (abs_nonneg a)
  · obtain ⟨I, hI, hmax⟩ := Finset.exists_mem_eq_sup'
      (Φ.compatibleSelections_nonempty d) (fun I => |∑ p ∈ I, z p|)
    change Φ.compatibilityNorm z = _ at hmax
    rw [hmax]
    have hh := Φ.form_le_norm (fun p => a * z p) I ((mem_compatibleSelections Φ I).mp hI)
    simpa only [← Finset.mul_sum, abs_mul] using hh

theorem norm_neg (Φ : LabelCover) {d : ℕ} (z : Φ.Coordinate d → ℝ) :
    Φ.compatibilityNorm (-z) = Φ.compatibilityNorm z := by
  change Φ.compatibilityNorm (fun p => -z p) = Φ.compatibilityNorm z
  simpa only [neg_one_mul, abs_neg, abs_one, one_mul] using Φ.norm_mul (-1) z

theorem norm_attained_on_support (Φ : LabelCover) {d : ℕ}
    (z : Φ.Coordinate d → ℝ) (B : Finset (Φ.Query d))
    (hz : ∀ p, p.1 ∉ B → z p = 0) :
    ∃ I : Finset (Φ.Coordinate d), Φ.Compatible I ∧
      (∀ p ∈ I, p.1 ∈ B) ∧ Φ.compatibilityNorm z = |∑ p ∈ I, z p| := by
  classical
  obtain ⟨J, hJ, heq⟩ := Finset.exists_mem_eq_sup'
    (Φ.compatibleSelections_nonempty d) (fun I => |∑ p ∈ I, z p|)
  let I := J.filter (fun p => p.1 ∈ B)
  have hIJ : I ⊆ J := Finset.filter_subset _ _
  refine ⟨I, Φ.compatible_mono ((mem_compatibleSelections Φ J).mp hJ) hIJ,
    fun p hp => (Finset.mem_filter.mp hp).2, ?_⟩
  change Φ.compatibilityNorm z = _ at heq
  rw [heq]
  congr 1
  symm
  apply Finset.sum_subset hIJ
  intro p hp hpI
  apply hz p
  intro hpB
  exact hpI (Finset.mem_filter.mpr ⟨hp, hpB⟩)

end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
