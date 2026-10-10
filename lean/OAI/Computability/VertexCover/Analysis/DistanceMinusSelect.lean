import Mathlib
import OAI.Computability.VertexCover.Analysis.BatchGradientForm

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

def affineSign (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem affineSign_true : affineSign true = 1 := rfl
@[simp] theorem affineSign_false : affineSign false = -1 := rfl

theorem norm_select_affine (Φ : LabelCover) {d : ℕ} (x : Φ.Coordinate d → ℝ) :
    ∃ I, Φ.Compatible I ∧ ∃ e : Bool,
      Φ.compatibilityNorm x = affineSign e * Φ.selectionForm I x := by
  obtain ⟨I, hI, heq⟩ := (Φ.compatibleSelections d).exists_mem_eq_sup'
    (Φ.compatibleSelections_nonempty d) (fun I => |∑ p ∈ I, x p|)
  change Φ.compatibilityNorm x = |∑ p ∈ I, x p| at heq
  rw [← Φ.selectionForm_apply] at heq
  refine ⟨I, (Φ.mem_compatibleSelections I).mp hI, ?_⟩
  by_cases h : 0 ≤ Φ.selectionForm I x
  · refine ⟨true, ?_⟩
    simpa only [affineSign_true, one_mul, ← Φ.selectionForm_apply, abs_of_nonneg h] using heq
  · refine ⟨false, ?_⟩
    simpa only [affineSign_false, neg_one_mul, ← Φ.selectionForm_apply,
      abs_of_neg (lt_of_not_ge h)] using heq

abbrev AffineIndex (Φ : LabelCover) {d : ℕ} (A : Finset (Φ.Coordinate d → ℝ)) :=
  A × (Φ.compatibleSelections d) × Bool × Bool

noncomputable def affineSlope (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) {A : Finset (Φ.Coordinate d → ℝ)}
    (i : Φ.AffineIndex A) : Φ.BatchWeights J →L[ℝ] ℝ :=
  affineSign i.2.2.2 • (Φ.selectionForm i.2.1.val).comp (Φ.batchSumCLM seed J)

noncomputable def affineOffset (Φ : LabelCover) {d : ℕ}
    (c0 : Φ.Coordinate d → ℝ) {A : Finset (Φ.Coordinate d → ℝ)}
    (i : Φ.AffineIndex A) : ℝ :=
  affineSign i.2.2.2 * Φ.selectionForm i.2.1.val (c0 - affineSign i.2.2.1 • i.1.val)

theorem affine_value (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (c0 : Φ.Coordinate d → ℝ)
    {A : Finset (Φ.Coordinate d → ℝ)} (i : Φ.AffineIndex A) (s : Φ.BatchWeights J) :
    Φ.affineSlope seed J i s + Φ.affineOffset c0 i =
      affineSign i.2.2.2 * Φ.selectionForm i.2.1.val
        (c0 + Φ.batchSum seed J s - affineSign i.2.2.1 • i.1.val) := by
  simp only [affineSlope, affineOffset, smul_apply,
    ContinuousLinearMap.comp_apply, Φ.batchSumCLM_apply, smul_eq_mul, map_sub, map_add]
  ring

theorem distance_plus_select (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (s : Φ.BatchWeights J) :
    ∃ i : Φ.AffineIndex A, Φ.distanceTo A hA (c0 + Φ.batchSum seed J s) =
      Φ.affineSlope seed J i s + Φ.affineOffset c0 i := by
  classical
  obtain ⟨z, hz, heq⟩ := A.exists_mem_eq_inf' hA
    (fun z => Φ.compatibilityNorm (c0 + Φ.batchSum seed J s - z))
  obtain ⟨I, hI, e, hnorm⟩ := Φ.norm_select_affine (c0 + Φ.batchSum seed J s - z)
  let i : Φ.AffineIndex A := (⟨z,hz⟩, ⟨I,(Φ.mem_compatibleSelections I).mpr hI⟩, true,e)
  change Φ.distanceTo A hA (c0 + Φ.batchSum seed J s) = _ at heq
  refine ⟨i, ?_⟩
  rw [Φ.affine_value]
  simpa only [i, affineSign_true, one_smul] using heq.trans hnorm

theorem distance_minus_select (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (s : Φ.BatchWeights J) :
    ∃ i : Φ.AffineIndex A, Φ.distanceTo A hA (-(c0 + Φ.batchSum seed J s)) =
      Φ.affineSlope seed J i s + Φ.affineOffset c0 i := by
  classical
  obtain ⟨z, hz, heq⟩ := A.exists_mem_eq_inf' hA
    (fun z => Φ.compatibilityNorm (-(c0 + Φ.batchSum seed J s)-z))
  have heq' : Φ.distanceTo A hA (-(c0 + Φ.batchSum seed J s)) =
      Φ.compatibilityNorm (c0 + Φ.batchSum seed J s + z) := by
    change _ = _ at heq
    rw [show -(c0 + Φ.batchSum seed J s)-z =
      -(c0 + Φ.batchSum seed J s + z) by abel, Φ.norm_neg] at heq
    exact heq
  obtain ⟨I, hI, e, hnorm⟩ := Φ.norm_select_affine (c0 + Φ.batchSum seed J s + z)
  let i : Φ.AffineIndex A := (⟨z,hz⟩, ⟨I,(Φ.mem_compatibleSelections I).mpr hI⟩, false,e)
  refine ⟨i, ?_⟩
  rw [Φ.affine_value]
  simpa only [i, affineSign_false, neg_one_smul, sub_neg_eq_add] using heq'.trans hnorm

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
