import OAI.Probability.FreeIsing.Trees.Escape
import OAI.Probability.FreeIsing.Trees.Parents

namespace OAI

noncomputable section

namespace Problem367.LocalSupportGeometry

def prefixVertex {d : ℕ} (v : TreeVertex d) (n : ℕ) : TreeVertex d :=
  ⟨v.1.take n, v.2.take n⟩

@[simp] theorem prefixVertex_length {d : ℕ} (v : TreeVertex d) (n : ℕ) :
    (prefixVertex v n).1.length = min n v.1.length := by
  simp [prefixVertex]

theorem prefixVertex_prefix {d : ℕ} (v : TreeVertex d) (n : ℕ) :
    (prefixVertex v n).1 <+: v.1 := List.take_prefix n v.1

theorem prefix_image_of_root_prefix {d : ℕ} (g : TreeAut d)
    {c : TreeVertex d} (hc : c.1 <+: (g.toEquiv TreeEscape.root).1)
    (v : TreeVertex d)
    (hdepth : c.1.length + v.1.length ≤ (g.toEquiv TreeEscape.root).1.length) :
    c.1 <+: (g.toEquiv v).1 := by
  rcases v with ⟨w, hw⟩
  induction w using List.reverseRecOn with
  | nil => exact hc
  | append_singleton w a ih =>
    have hw' : w.IsChain (· ≠ ·) := hw.left_of_append
    have hlength : c.1.length + (w.length + 1) ≤
        (g.toEquiv TreeEscape.root).1.length := by
      simpa only [List.length_append, List.length_singleton] using hdepth
    have hprevious : c.1.length + w.length ≤
        (g.toEquiv TreeEscape.root).1.length := by omega
    have hp := ih hw' hprevious
    have hne : g.toEquiv (⟨w, hw'⟩ : TreeVertex d) ≠ c := by
      intro heq
      have hh := TreeEscape.root_depth_le g (⟨w, hw'⟩ : TreeVertex d)
      rw [heq] at hh
      change (g.toEquiv TreeEscape.root).1.length ≤ c.1.length + w.length at hh
      omega
    have hadj : treeAdj (⟨w, hw'⟩ : TreeVertex d) ⟨w ++ [a], hw⟩ :=
      Or.inl ⟨a, rfl⟩
    exact treeAdj_preserves_prefix hp ((g.map_adj _ _).2 hadj) hne

theorem image_ball_prefix {d : ℕ} (g : TreeAut d) (R : ℕ)
    (hR : R ≤ (g.toEquiv TreeEscape.root).1.length)
    (v : TreeVertex d) (hv : v.1.length ≤ R) :
    (prefixVertex (g.toEquiv TreeEscape.root)
      ((g.toEquiv TreeEscape.root).1.length - R)).1 <+: (g.toEquiv v).1 := by
  apply prefix_image_of_root_prefix g (prefixVertex_prefix _ _) v
  rw [prefixVertex_length, Nat.min_eq_left (Nat.sub_le _ _)]
  omega

theorem separated_ball_endpoints {d : ℕ} (g : TreeAut d) (R : ℕ)
    (hR : R + R < (g.toEquiv TreeEscape.root).1.length) :
    ∃ a b c : TreeVertex d,
      a.1.length = R ∧ b.1.length = R + 1 ∧
      c.1.length = (g.toEquiv TreeEscape.root).1.length - R ∧
      treeAdj a b ∧ b.1 <+: c.1 ∧
      (∀ v : TreeVertex d, v.1.length ≤ R → ¬ b.1 <+: v.1) ∧
      (∀ v : TreeVertex d, v.1.length ≤ R → c.1 <+: (g.toEquiv v).1) ∧
      ∃ middle : List (Fin d), c.1 = a.1 ++ middle ∧
        middle.length = (g.toEquiv TreeEscape.root).1.length - (R + R) := by
  let w := g.toEquiv TreeEscape.root
  let a := prefixVertex w R
  let b := prefixVertex w (R + 1)
  let c := prefixVertex w (w.1.length - R)
  have hRk : R ≤ w.1.length := by dsimp [w]; omega
  have hR1k : R + 1 ≤ w.1.length := by dsimp [w]; omega
  have ha : a.1.length = R := by simp [a, Nat.min_eq_left hRk]
  have hb : b.1.length = R + 1 := by simp [b, Nat.min_eq_left hR1k]
  have hc : c.1.length = w.1.length - R := by
    simp [c]
  have hab : a.1 <+: b.1 := List.take_prefix_take_left (by omega)
  have hbc : b.1 <+: c.1 := List.take_prefix_take_left (by dsimp [w]; omega)
  have hadj : treeAdj a b := by
    obtain ⟨tail, htail⟩ := hab
    have hlen : tail.length = 1 := by
      have h := congrArg List.length htail
      simp only [List.length_append, ha, hb] at h
      omega
    obtain ⟨z, rfl⟩ := List.length_eq_one_iff.mp hlen
    exact Or.inl ⟨z, htail.symm⟩
  refine ⟨a, b, c, ha, hb, hc, hadj, hbc, ?_, ?_, ?_⟩
  · intro v hv hprefix
    have := hprefix.length_le
    omega
  · intro v hv
    exact image_ball_prefix g R hRk v hv
  · obtain ⟨middle, hmiddle⟩ := hab.trans hbc
    refine ⟨middle, hmiddle.symm, ?_⟩
    have h := congrArg List.length hmiddle
    simp only [List.length_append, ha, hc] at h
    dsimp [w] at h ⊢
    omega

end Problem367.LocalSupportGeometry

end

end OAI
