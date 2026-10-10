import OAI.MeasureTheory.Falconer.Estimates.ScalarUniformTrim
import OAI.MeasureTheory.Falconer.Estimates.ScalarBunchingTotals

namespace OAI

/-! Locality facts for iterating bunch trims from fine to coarse scales. -/
namespace Falconer

 theorem ScalarBunchChain.mem_bounds {N lo : ℕ} {bs : List ScalarBunch}
    (h : ScalarBunchChain N lo bs) :
    ∀ b ∈ bs, lo ≤ b.start ∧ b.stop ≤ N := by
  induction h with
  | nil n => simp
  | @cons b lo bs h ih =>
    intro c hc
    rcases List.mem_cons.mp hc with heq | hc
    · subst c
      exact ⟨h.start_le,le_rfl⟩
    · have hh := ih c hc
      exact ⟨hh.1,hh.2.trans (b.start_lt_cut.le.trans b.cut_le_stop)⟩

namespace Regularization

 theorem prefixChildren_mono {L Q : Finset (CellPath 1)} (hsub : Q ⊆ L)
    (a b : ℕ) (p : CellPath 1) : prefixChildren Q a b p ⊆ prefixChildren L a b p := by
  classical
  apply Finset.image_subset_image
  intro q hq
  exact Finset.mem_filter.mpr ⟨hsub (Finset.mem_filter.mp hq).1,(Finset.mem_filter.mp hq).2⟩

 theorem ScalarPathLevel.of_same_fibers {L Q : Finset (CellPath 1)} {a b K : ℕ} {g : ℝ}
    (h : ScalarPathLevel L a b K g) (hsub : Q ⊆ L)
    (hf : ∀ q ∈ Q, prefixFiber Q a (q.take a) = prefixFiber L a (q.take a)) :
    ScalarPathLevel Q a b K g := by
  classical
  have hc : ∀ p ∈ Q.image (List.take a), prefixChildren Q a b p = prefixChildren L a b p := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    unfold prefixChildren
    rw [hf q hq]
  refine ⟨h.order,?_,?_⟩
  · intro p hp
    rw [hc p hp]
    exact h.card p (Finset.image_subset_image hsub hp)
  · intro p hp
    rw [hc p hp]
    exact h.separated p (Finset.image_subset_image hsub hp)

end Regularization
end Falconer

end OAI
