import OAI.Probability.SwitchChain.PairGeneratorSquare
import OAI.Probability.SwitchChain.PairProjectionCell

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairResampling

attribute [local instance] Classical.propDecidable

variable {n : ℕ} {d : Fin n → ℕ}

theorem restrictCell_sum {ι : Type*} (C : GraphState n d → Prop)
    (s : Finset ι) (f : ι → StateSpace n d) :
    restrictCell C (∑ i ∈ s, f i) = ∑ i ∈ s, restrictCell C (f i) := by
  ext G
  by_cases hG : C G <;> simp [restrictCell, hG]

theorem square_bound_of_cells {β : Type*} [Fintype β]
    (k : GraphState n d → β) (L : StateSpace n d → StateSpace n d)
    (hcomm : ∀ b f, L (restrictCell (fun G => k G = b) f) =
      restrictCell (fun G => k G = b) (L f))
    (hlocal : ∀ b (f : StateSpace n d), (∀ G, k G ≠ b → f G = 0) →
      ⟪f, L f⟫ ≤ ⟪L f, L f⟫) (f : StateSpace n d) :
    ⟪f, L f⟫ ≤ ⟪L f, L f⟫ := by
  rw [inner_eq_sum_cell_inner k f (L f), inner_eq_sum_cell_inner k (L f) (L f)]
  apply Finset.sum_le_sum
  intro b hb
  rw [← hcomm b f]
  apply hlocal b
  intro G hG
  simp [restrictCell_apply, hG]

theorem tripleGenerator_restrictCell (T : Finset (Fin n))
    (C : GraphState n d → Prop)
    (hC : ∀ a ∈ T.powersetCard 2, CellInvariant a C) (f : StateSpace n d) :
    tripleGenerator n d T (restrictCell C f) =
      restrictCell C (tripleGenerator n d T f) := by
  simp only [tripleGenerator_apply, restrictCell_sum]
  apply Finset.sum_congr rfl
  intro a ha
  exact fluctuation_restrictCell a C (hC a ha) f

theorem tripleGenerator_square_of_cellwise {β : Type*} [Fintype β]
    (T : Finset (Fin n)) (k : GraphState n d → β)
    (hC : ∀ a ∈ T.powersetCard 2, ∀ b, CellInvariant a (fun G => k G = b))
    (hlocal : ∀ b (f : StateSpace n d), (∀ G, k G ≠ b → f G = 0) →
      ⟪f, tripleGenerator n d T f⟫ ≤
        ⟪tripleGenerator n d T f, tripleGenerator n d T f⟫)
    (f : StateSpace n d) :
    ⟪f, tripleGenerator n d T f⟫ ≤
      ⟪tripleGenerator n d T f, tripleGenerator n d T f⟫ := by
  apply square_bound_of_cells k (tripleGenerator n d T) _ hlocal f
  intro b g
  exact tripleGenerator_restrictCell T _ (fun a ha => hC a ha b) g

theorem tripleGenerator_square_of_key {β : Type*}
    (T : Finset (Fin n)) (k : GraphState n d → β)
    (hC : ∀ a ∈ T.powersetCard 2, ∀ b, CellInvariant a (fun G => k G = b))
    (hlocal : ∀ b (f : StateSpace n d), (∀ G, k G ≠ b → f G = 0) →
      ⟪f, tripleGenerator n d T f⟫ ≤
        ⟪tripleGenerator n d T f, tripleGenerator n d T f⟫)
    (f : StateSpace n d) :
    ⟪f, tripleGenerator n d T f⟫ ≤
      ⟪tripleGenerator n d T f, tripleGenerator n d T f⟫ := by
  let k' : GraphState n d → Set.range k := fun G => ⟨k G, G, rfl⟩
  let : Fintype (Set.range k) := (Set.finite_range k).fintype
  apply tripleGenerator_square_of_cellwise T k' _ _ f
  · intro a ha b G H hGH
    simpa only [k', Subtype.ext_iff] using hC a ha b.val G H hGH
  · intro b g hg
    apply hlocal b.val g
    intro G hG
    apply hg G
    intro he
    exact hG (congrArg Subtype.val he)

theorem tripleGenerator_square_of_reference_cells {β : Type*}
    (T : Finset (Fin n)) (k : GraphState n d → β)
    (hpres : ∀ a ∈ T.powersetCard 2, ∀ G H : GraphState n d,
      SameFiber a G.val H.val → k G = k H)
    (hlocal : ∀ G₀ (f : StateSpace n d),
      (∀ G, k G ≠ k G₀ → f G = 0) →
      ⟪f, tripleGenerator n d T f⟫ ≤
        ⟪tripleGenerator n d T f, tripleGenerator n d T f⟫)
    (f : StateSpace n d) :
    ⟪f, tripleGenerator n d T f⟫ ≤
      ⟪tripleGenerator n d T f, tripleGenerator n d T f⟫ := by
  apply tripleGenerator_square_of_key T k _ _ f
  · intro a ha b G H hGH
    change k G = b ↔ k H = b
    rw [hpres a ha G H hGH]
  · intro b g hg
    by_cases hb : b ∈ Set.range k
    · obtain ⟨G₀, rfl⟩ := hb
      exact hlocal G₀ g hg
    · have hz : g = 0 := by
        ext G
        apply hg G
        intro he
        exact hb ⟨G, he⟩
      simp [hz]

end Problem315.PairResampling

end

end OAI
