import OAI.MeasureTheory.DyadicAvoidance.FiniteLocalPredicate
import OAI.MeasureTheory.DyadicAvoidance.WindowTableModel
import OAI.MeasureTheory.DyadicAvoidance.MonotoneRepresentatives

namespace OAI

universe u_Ω

noncomputable section

namespace Problem310.WindowLocalFactor

open RoutingPath GridSeparation LocalPredicateFactor

/-- Padded equal-length child windows provide a common representative set for
all outcomes and all local predicates factoring through their subtree grids.
The representatives are selected before the outcome or predicates. -/
theorem exists_uniform_window_representatives {Ω : Type u_Ω} (M r : ℕ)
    (a B : Fin M → ℕ) (hpadding : ∀ i, B i + 1 ≤ a i + 2 * r)
    (x : ℝ) :
    ∃ R : Finset ℝ,
      (∀ t ∈ R, t ∈ Set.Icc (1 : ℝ) 2) ∧
      R.card ≤ 1 + M * r * 2 ^ (2 * r + 2) ∧
      ∀ t ∈ Set.Icc (1 : ℝ) 2, ∃ t' ∈ R,
        ∀ Q : Ω → Fin M → ℝ → Bool,
          (∀ ω i y z, ⌊(2 : ℝ) ^ (B i + 2) * Int.fract y⌋ =
            ⌊(2 : ℝ) ^ (B i + 2) * Int.fract z⌋ → Q ω i y = Q ω i z) →
          ∀ ω (i : Fin M) (j : Fin r),
            Q ω i (x + t' * ((2 : ℝ)⁻¹) ^ (a i + j.val)) =
              Q ω i (x + t * ((2 : ℝ)⁻¹) ^ (a i + j.val)) := by
  have hspan (ij : Fin M × Fin r) : B ij.1 + 2 ≤
      (a ij.1 + ij.2.val) + (2 * r + 2) := by
    have h := hpadding ij.1
    omega
  obtain ⟨R, hR, hcard, hrep⟩ := ScaleDiscretization.exists_local_predicate_representatives
    x (fun ij : Fin M × Fin r => B ij.1 + 2)
    (fun ij : Fin M × Fin r => a ij.1 + ij.2.val) (2 * r + 2) hspan
  refine ⟨R, hR, ?_, ?_⟩
  · simpa only [Fintype.card_prod, Fintype.card_fin] using hcard
  · intro t ht
    obtain ⟨t', ht', hsame⟩ := hrep t ht
    refine ⟨t', ht', ?_⟩
    intro Q hQ ω i j
    exact hsame (fun ij z => Q ω ij.1 z) (fun ij y z h => hQ ω ij.1 y z h) (i, j)

/-- Canonical window data discharges the padding hypothesis for all nondefault
children of an internal node, whose incoming windows have the same length. -/
theorem exists_window_data_representatives {Ω : Type u_Ω} {M d g r₀ : ℕ}
    (W : WindowData (M + 1) d g r₀) (U : FiniteTableModel.Node M d) (x : ℝ) :
    ∃ R : Finset ℝ,
      (∀ t ∈ R, t ∈ Set.Icc (1 : ℝ) 2) ∧
      R.card ≤ 1 + M * W.r (d - U.val.length) * 2 ^ (2 * W.r (d - U.val.length) + 2) ∧
      ∀ t ∈ Set.Icc (1 : ℝ) 2, ∃ t' ∈ R,
        ∀ Q : Ω → Fin M → ℝ → Bool,
          (∀ ω i y z,
            ⌊(2 : ℝ) ^ (W.bstar (U.val ++ [i.castSucc]) + 2) * Int.fract y⌋ =
            ⌊(2 : ℝ) ^ (W.bstar (U.val ++ [i.castSucc]) + 2) * Int.fract z⌋ →
              Q ω i y = Q ω i z) →
          ∀ ω (i : Fin M) (j : Fin (W.r (d - U.val.length))),
            Q ω i (x + t' * ((2 : ℝ)⁻¹) ^ (W.a (U.val ++ [i.castSucc]) + j.val)) =
              Q ω i (x + t * ((2 : ℝ)⁻¹) ^ (W.a (U.val ++ [i.castSucc]) + j.val)) := by
  apply exists_uniform_window_representatives M (W.r (d - U.val.length))
    (fun i => W.a (U.val ++ [i.castSucc]))
    (fun i => W.bstar (U.val ++ [i.castSucc]))
  intro i
  have hP : ValidWindowEdge d (U.val ++ [i.castSucc]) := by
    refine ⟨by simp, ?_⟩
    simp only [List.length_append, List.length_singleton]
    exact Nat.succ_le_of_lt U.property
  have hpad := W.padding _ hP
  simpa only [List.length_append, List.length_singleton, Nat.add_sub_add_right] using hpad

/-- The concrete finite-table local predicate inherits its common grid from
WindowData's bound on endpoints of descendant edges. -/
theorem window_local_predicate_factors {M d g r₀ : ℕ}
    (W : WindowData (M + 1) d g r₀)
    (bS : FiniteTableModel.Node M d → Fin M → ℕ)
    (bT : FiniteTableModel.Leaf M d → ℕ)
    (hbS : ∀ Q j, bS Q j = W.b (Q.val ++ [j.castSucc]))
    (hbT : ∀ L, bT L = W.b L.val)
    (ωS : FiniteTableModel.SelectorTable bS) (ωT : FiniteTableModel.TerminalTable bT)
    (choose : List (FiniteTableModel.Child M) → ℝ → FiniteTableModel.Child M)
    (rule : List (FiniteTableModel.Child M) → (Fin M → Bool) → FiniteTableModel.Child M)
    (hchoose : ∀ Q x, choose Q x = rule Q (fun j => FiniteTableModel.selectorValue bS ωS Q j x))
    (U : FiniteTableModel.Node M d) (i : Fin M) (r : ℕ)
    (hdepth : (U.val ++ [i.castSucc]).length + r = d)
    {x y : ℝ}
    (hxy : ⌊(2 : ℝ) ^ (W.bstar (U.val ++ [i.castSucc]) + 2) * Int.fract x⌋ =
      ⌊(2 : ℝ) ^ (W.bstar (U.val ++ [i.castSucc]) + 2) * Int.fract y⌋) :
    (ωS (FiniteTableModel.selectorAddress bS U i x) &&
      ωT (FiniteTableModel.terminalAddress bT
        (FiniteLocalPredicate.localLeaf choose r (U.val ++ [i.castSucc]) hdepth x) x)) =
    (ωS (FiniteTableModel.selectorAddress bS U i y) &&
      ωT (FiniteTableModel.terminalAddress bT
        (FiniteLocalPredicate.localLeaf choose r (U.val ++ [i.castSucc]) hdepth y) y)) := by
  have hP : ValidWindowEdge d (U.val ++ [i.castSucc]) := by
    refine ⟨by simp, ?_⟩
    simp only [List.length_append, List.length_singleton]
    exact Nat.succ_le_of_lt U.property
  apply FiniteLocalPredicate.finite_local_predicate_factors
    bS bT ωS ωT choose rule hchoose r (U.val ++ [i.castSucc]) hdepth U i
    (W.bstar (U.val ++ [i.castSucc]))
  · intro Q hPQ j
    rw [hbS]
    apply (W.descendant_bounds _ _ hP ?_ (hPQ.trans (List.prefix_append _ _))).2
    refine ⟨by simp, ?_⟩
    simp only [List.length_append, List.length_singleton]
    exact Nat.succ_le_of_lt Q.property
  · intro L hPL
    rw [hbT]
    apply (W.descendant_bounds _ _ hP ?_ hPL).2
    refine ⟨?_, L.property.le⟩
    intro hL
    have hD := L.property
    rw [hL] at hD
    simp only [List.length_nil] at hD
    have hU := U.property
    omega
  · rw [hbS]
    exact (W.descendant_bounds _ _ hP hP (List.prefix_refl _)).2
  · exact hxy

/-- Complete concrete representative adapter. Here `Q` is the actual local test,
with only its defining equality retained as an input for convenient rewriting.
No grid-factorization or numerical span hypotheses remain. -/
theorem exists_concrete_local_representatives {M d g r₀ : ℕ}
    (W : WindowData (M + 1) d g r₀) (U : FiniteTableModel.Node M d) (x : ℝ)
    (choose : FiniteTableModel.SelectorTable (FiniteTableModel.selectorEndpoints W) →
      List (FiniteTableModel.Child M) → ℝ → FiniteTableModel.Child M)
    (rule : List (FiniteTableModel.Child M) → (Fin M → Bool) → FiniteTableModel.Child M)
    (hchoose : ∀ ωS P y, choose ωS P y = rule P (fun j =>
      FiniteTableModel.selectorValue (FiniteTableModel.selectorEndpoints W) ωS P j y))
    (r : ℕ) (hdepth : ∀ i : Fin M, (U.val ++ [i.castSucc]).length + r = d)
    (Q : (FiniteTableModel.SelectorTable (FiniteTableModel.selectorEndpoints W) ×
      FiniteTableModel.TerminalTable (FiniteTableModel.terminalEndpoints W)) →
        Fin M → ℝ → Bool)
    (hQ : ∀ ω i y, Q ω i y =
      (ω.1 (FiniteTableModel.selectorAddress (FiniteTableModel.selectorEndpoints W) U i y) &&
        ω.2 (FiniteTableModel.terminalAddress (FiniteTableModel.terminalEndpoints W)
          (FiniteLocalPredicate.localLeaf (choose ω.1) r (U.val ++ [i.castSucc]) (hdepth i) y) y))) :
    ∃ R : Finset ℝ,
      (∀ t ∈ R, t ∈ Set.Icc (1 : ℝ) 2) ∧
      R.card ≤ 1 + M * W.r (d - U.val.length) * 2 ^ (2 * W.r (d - U.val.length) + 2) ∧
      ∀ t ∈ Set.Icc (1 : ℝ) 2, ∃ t' ∈ R,
        ∀ ω (i : Fin M) (j : Fin (W.r (d - U.val.length))),
          Q ω i (x + t' * ((2 : ℝ)⁻¹) ^ (W.a (U.val ++ [i.castSucc]) + j.val)) =
            Q ω i (x + t * ((2 : ℝ)⁻¹) ^ (W.a (U.val ++ [i.castSucc]) + j.val)) := by
  obtain ⟨R, hR, hcard, hrep⟩ := exists_window_data_representatives (Ω :=
    FiniteTableModel.SelectorTable (FiniteTableModel.selectorEndpoints W) ×
      FiniteTableModel.TerminalTable (FiniteTableModel.terminalEndpoints W)) W U x
  refine ⟨R, hR, hcard, ?_⟩
  intro t ht
  obtain ⟨t', ht', hsame⟩ := hrep t ht
  refine ⟨t', ht', hsame Q ?_⟩
  intro ω i y z hyz
  rw [hQ ω i y, hQ ω i z]
  exact window_local_predicate_factors W
    (FiniteTableModel.selectorEndpoints W) (FiniteTableModel.terminalEndpoints W)
    (fun _ _ => rfl) (fun _ => rfl) ω.1 ω.2 (choose ω.1) rule (hchoose ω.1)
    U i r (hdepth i) hyz

end Problem310.WindowLocalFactor

end

end OAI
