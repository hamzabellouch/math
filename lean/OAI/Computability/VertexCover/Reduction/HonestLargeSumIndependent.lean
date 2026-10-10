import Mathlib
import OAI.Computability.VertexCover.Reduction.IncrementNorm

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

def gridRational (d : ℕ) (v : Fin (2*d+1)) : ℚ :=
  2 * ((v.val : ℚ) - d) / (2*d+1)

abbrev Vertex (Φ : LabelCover) (d : ℕ) :=
  Φ.Seeds d × (Fin d → Fin (Φ.WeightDimension d) → Fin (2*d+1))

noncomputable def sumVector (Φ : LabelCover) {d : ℕ} (v : Φ.Vertex d) :
    Φ.Coordinate d → ℝ :=
  ∑ j, Φ.increment (Φ.query v.1 j) (fun k => (gridRational d (v.2 j k) : ℝ))

noncomputable def graph (Φ : LabelCover) (d : ℕ) (t : ℝ) : SimpleGraph (Φ.Vertex d) where
  Adj v w := v ≠ w ∧ Φ.compatibilityNorm (Φ.sumVector v + Φ.sumVector w) ≤ 2*t
  symm := ⟨by intro v w h; exact ⟨h.1.symm, by simpa only [add_comm] using h.2⟩⟩
  loopless := ⟨by intro v h; exact h.1 rfl⟩

theorem low_norm_adjacent (Φ : LabelCover) {d : ℕ} {t : ℝ} {v w : Φ.Vertex d}
    (hne : v ≠ w) (hv : Φ.compatibilityNorm (Φ.sumVector v) ≤ t)
    (hw : Φ.compatibilityNorm (Φ.sumVector w) ≤ t) : (Φ.graph d t).Adj v w := by
  refine ⟨hne, (Φ.norm_add_le _ _).trans ?_⟩
  linarith

theorem low_norm_subsingleton (Φ : LabelCover) {d : ℕ} {t : ℝ}
    (A : Set (Φ.Vertex d)) (hA : (Φ.graph d t).IsIndepSet A) :
    {v ∈ A | Φ.compatibilityNorm (Φ.sumVector v) ≤ t}.Subsingleton := by
  intro v hv w hw
  by_contra hne
  exact ((SimpleGraph.isIndepSet_iff _).mp hA hv.1 hw.1 hne)
    (Φ.low_norm_adjacent hne hv.2 hw.2)

theorem honestSelection_form_increment (Φ : LabelCover) {d : ℕ}
    (A : Φ.Labeling) (hA : ∀ c, Φ.Satisfies A c) (i : Φ.Query d)
    (s : Fin (Φ.WeightDimension d) → ℝ) :
    ∑ p ∈ Φ.honestSelection A hA d, Φ.increment i s p =
      s (i.slot (Φ.localOfSatisfying A hA i)) := by
  classical
  unfold honestSelection
  rw [Finset.sum_image]
  · have hz : ∀ j : Φ.Query d, Φ.increment i s ⟨j, Φ.localOfSatisfying A hA j⟩ =
        if j = i then s (i.slot (Φ.localOfSatisfying A hA i)) else 0 := by
      intro j
      split_ifs with h
      · subst j; exact Φ.increment_same _ _ _
      · exact Φ.increment_other _ _ _ h
    simp only [hz]
    simp
  · intro i _ j _ h
    exact congrArg Sigma.fst h

noncomputable def honestSum (Φ : LabelCover) {d : ℕ} (A : Φ.Labeling)
    (hA : ∀ c, Φ.Satisfies A c) (v : Φ.Vertex d) : ℝ :=
  ∑ j, (gridRational d (v.2 j ((Φ.query v.1 j).slot
    (Φ.localOfSatisfying A hA (Φ.query v.1 j)))) : ℝ)

theorem honestSelection_form_sumVector (Φ : LabelCover) {d : ℕ}
    (A : Φ.Labeling) (hA : ∀ c, Φ.Satisfies A c) (v : Φ.Vertex d) :
    ∑ p ∈ Φ.honestSelection A hA d, Φ.sumVector v p = Φ.honestSum A hA v := by
  classical
  simp only [sumVector, Finset.sum_apply]
  rw [Finset.sum_comm]
  simp only [honestSelection_form_increment, honestSum]

theorem honest_large_sum_independent (Φ : LabelCover) {d : ℕ} (t : ℝ)
    (A : Φ.Labeling) (hA : ∀ c, Φ.Satisfies A c) :
    (Φ.graph d t).IsIndepSet {v | t < Φ.honestSum A hA v} := by
  rw [SimpleGraph.isIndepSet_iff]
  intro v hv w hw _ hadj
  have hform := Φ.form_le_norm (Φ.sumVector v + Φ.sumVector w)
    (Φ.honestSelection A hA d) (Φ.honestSelection_compatible A hA d)
  simp only [Pi.add_apply, Finset.sum_add_distrib, honestSelection_form_sumVector] at hform
  have hsum := (le_abs_self (Φ.honestSum A hA v + Φ.honestSum A hA w)).trans
    (hform.trans hadj.2)
  change t < Φ.honestSum A hA v at hv
  change t < Φ.honestSum A hA w at hw
  linarith

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
