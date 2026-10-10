import OAI.Analysis.KadisonKastler.FreeProjectionWords
import OAI.Analysis.KadisonKastler.PrescribedTuples
import OAI.Analysis.KadisonKastler.ThroughLabelBounds

namespace OAI

/-! # Actual free-word bounds with the prescribed-multiset indexing -/

namespace KadisonKastler

open Finset

noncomputable section

namespace FreeDiagonalModel

variable {ι α H : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Both cases of the prescribed-multiset word estimate, with the
factorial counting proved for the actual indexing type. -/
theorem norm_prescribed_projectionWords_le (M : FreeDiagonalModel ι α H)
    {r : ℕ} (hr : 1 ≤ r) (hd : freeWordThreshold r ≤ Fintype.card α)
    (s : Sym α r) (position : Fin r → ι) (hposition : Function.Injective position) :
    ‖∑ t : PrescribedLabelTuple s, M.projectionWord position t.val‖ ≤
      projectionWordWeight (freeWordC r) s := by
  unfold projectionWordWeight
  split_ifs with hs
  · rw [sum_prescribedLabelTuple_eq_ordered s hs]
    exact M.norm_sum_distinct_projectionWord_le s.val.toFinset hr hd
      ((Multiset.toFinset_card_of_nodup hs).trans s.property) position hposition
  · exact M.norm_sum_projectionWord_le_repeated_constant (by omega) position hposition
      univ (fun t : PrescribedLabelTuple s => t.val)
      (by simpa only [card_univ] using card_prescribedLabelTuple_le s)

end FreeDiagonalModel

/-- One threshold supplies both all word estimates and the through-label
square-sum estimate for the finitely many lengths in the application. -/
theorem exists_uniform_freeProjection_threshold (N : ℕ) :
    ∃ D : ℕ, 0 < D ∧ ∀ d : ℕ, D ≤ d → ∀ r : ℕ, 1 ≤ r → r ≤ N →
      freeWordThreshold r ≤ d ∧
        ∀ a : Fin d, (∑ s : ThroughLabel a r, projectionWordWeight (freeWordC r) s.val ^ 2) ≤ 64 := by
  obtain ⟨D₁, hD₁, h₁⟩ := exists_uniform_freeWordThreshold N
  obtain ⟨D₂, hD₂, h₂⟩ := exists_uniform_projectionWordWeight_threshold N freeWordC
  refine ⟨max D₁ D₂, lt_of_lt_of_le hD₁ (le_max_left _ _), ?_⟩
  intro d hd r hr hrN
  exact ⟨(h₁ r hrN).trans ((le_max_left _ _).trans hd),
    h₂ d ((le_max_right _ _).trans hd) r hr hrN⟩

end

end KadisonKastler

end OAI
