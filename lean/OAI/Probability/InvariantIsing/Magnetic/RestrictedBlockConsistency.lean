import OAI.Probability.InvariantIsing.Magnetic.RestrictedPairTies
import OAI.Probability.InvariantIsing.Cavity.CavityFieldSelfConsistency

namespace OAI

/-! Plateau consistency and the L1 self-consistency implication for the
actual constrained block overlap, with arbitrary finite cascade depth. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

private lemma restricted_finite_level_fiber {n : ℕ} (f q : Fin (n + 1) → ℝ)
    (hf : Monotone f)
    (hq : ∀ k : Fin n, f k.castSucc = f k.succ → q k.castSucc = q k.succ)
    (i j : Fin (n + 1)) (he : f i = f j) : q i = q j := by
  have hord : ∀ j i : Fin (n + 1), i ≤ j → f i = f j → q i = q j := by
    intro j
    induction j using Fin.induction with
    | zero =>
      intro i hi _
      have hi0 : i = 0 := le_antisymm hi (Fin.zero_le i)
      subst i
      rfl
    | succ j ih =>
      intro i hij he
      by_cases hi : i = j.succ
      · rw [hi]
      have hij' : i ≤ j.castSucc := by
        change i.val ≤ j.val
        have hil : i.val ≤ j.val + 1 := hij
        have hne : i.val ≠ j.val + 1 := by
          intro hv
          apply hi
          exact Fin.ext hv
        omega
      have hleft := hf hij'
      have hright := hf (show j.castSucc ≤ j.succ by exact Nat.le_succ j.val)
      have he' : f i = f j.castSucc := by linarith
      have hs : f j.castSucc = f j.succ := by linarith
      exact (ih i hij' he').trans (hq j hs)
  rcases le_total i j with hij | hji
  · exact hord j i hij he
  · exact (hord i j hji he.symm).symm


lemma restrictedBlockPairMean_eq_of_height_eq {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) (b : Fin N → ℝ)
    (i j : Fin (h.depth+1)) (he : h.height i = h.height j) :
    restrictedBlockPairMean hN S hS h b i = restrictedBlockPairMean hN S hS h b j :=
  restricted_finite_level_fiber h.height (restrictedBlockPairMean hN S hS h b)
    h.ordered_height (restrictedBlockPairMean_tied hN S hS h b) i j he

lemma restrictedBlockOverlapPath_on_cell {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep)
    (i : Fin (h.depth+1)) {s : ℝ} (hs : s ∈ Ioo (h.cut i.castSucc) (h.cut i.succ)) :
    restrictedBlockOverlapPath hN S hS h s = restrictedBlockPairMean hN S hS h (fun _ => 0) i :=
  fieldLevelPath_on_cell h _ _ _ i hs

lemma restrictedBlockOverlapPath_eq_of_cell_height_eq {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep)
    (i j : Fin (h.depth+1)) {s t : ℝ}
    (hs : s ∈ Ioo (h.cut i.castSucc) (h.cut i.succ))
    (ht : t ∈ Ioo (h.cut j.castSucc) (h.cut j.succ))
    (he : h.height i = h.height j) :
    restrictedBlockOverlapPath hN S hS h s = restrictedBlockOverlapPath hN S hS h t := by
  rw [restrictedBlockOverlapPath_on_cell hN S hS h i hs,
    restrictedBlockOverlapPath_on_cell hN S hS h j ht]
  exact restrictedBlockPairMean_eq_of_height_eq hN S hS h _ i j he

theorem restricted_block_self_consistency_l1 {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (p : OverlapPath)
    (q : ℕ → OverlapPath) (h : ℕ → FieldStep) (height : ℕ → ℝ → ℝ)
    (hheight : ∀ a i s, s ∈ Ioo ((h a).cut i.castSucc) ((h a).cut i.succ) →
      (h a).height i = height a (p s))
    (hq : ∀ᵐ s ∂pathMeasure, Tendsto (fun a => q a s) atTop (𝓝 (p s)))
    (htest : ∀ Φ : ℝ →ᵇ ℝ, Tendsto
      (fun a => ∫ s, Φ (q a s) * (restrictedBlockOverlapPath hN S hS (h a) s - q a s) ∂pathMeasure)
      atTop (𝓝 0)) :
    Tendsto (fun a => ∫ s, |restrictedBlockOverlapPath hN S hS (h a) s - p s| ∂pathMeasure)
      atTop (𝓝 0) := by
  let D := {s | ∀ a, ∃ i : Fin ((h a).depth+1),
    s ∈ Ioo ((h a).cut i.castSucc) ((h a).cut i.succ)}
  have hDae : ∀ᵐ s ∂pathMeasure, s ∈ D :=
    ae_all_iff.mpr (fun a => ae_finite_overlap_cell (h a).cut (h a).first (h a).last)
  apply cavity_rounded_self_consistency_l1_on p q (fun a => restrictedBlockOverlapPath hN S hS (h a))
    hq D hDae ?_ htest
  intro a x hx y hy hxy
  obtain ⟨i,hi⟩ := hx a
  obtain ⟨j,hj⟩ := hy a
  apply restrictedBlockOverlapPath_eq_of_cell_height_eq hN S hS (h a) i j hi hj
  rw [hheight a i x hi, hheight a j y hj, hxy]

end InvariantIsing

end

end OAI
