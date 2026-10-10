import OAI.MeasureTheory.Falconer.Graphs.GraphRetainedEdges

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem uniform_regularized_original_graph_removal {sig : ℝ} (hsig : 0 < sig)
    (K : ℕ) (lam T : ℝ) {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {c₀ : ℝ} (hc : 0 < c₀) (hcap : c₀ ≤ 2*Real.pi) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 4 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, (∑ t ∈ S l, k l t) ≤ K) →
    ∀ L : ℕ, (∀ l t, t ∈ S l → descriptorLength (d l t) ≤ L) →
    ∀ Q : Fin 4 → DyadicSquare, (∀ l, 0 < (Q l).side) → (∀ l, (Q l).side ≤ 1) →
    ∀ (ρ : Fin 4 → Measure Plane) (mass : Fin 4 → ℝ → ℝ) (B : ℕ) (δ : ℝ),
    (∀ l, RegularizedProfileData (Q l) (ρ l) N B δ lam (mass l)) →
    ∀ (J i : ℕ) (h : Fin 4 → Plane → ℂ), (∀ l, Measurable (h l)) → (∀ l x, ‖h l x‖ ≤ 1) →
    ∀ (a : ℝ) (p : ℕ) (v : ℝ), 0 ≤ a → a ≤ p → p ≤ N →
    0 ≤ v-p → (p:ℝ)-a ≤ v-p+2*sig*(N:ℝ) → (L:ℝ) ≤ v-p+2*sig*(N:ℝ) → v-a ≤ N →
    ∀ (distance : Bool) (X Y : DyadicSquare), 0 < X.side → 0 < Y.side →
    X.side ≤ (2:ℝ)^(-a) → Y.side ≤ (2:ℝ)^(-a) →
    (distance = true → dist X.center Y.center ≤ 2000*(2:ℝ)^(-a)) →
    ∀ (axis : ℝ) (I : Finset GraphNonedgeIndex),
    I ⊆ graphNonedgeIndices p (angularBinCount (graphAngularScale N sig ((p:ℝ)-a) c₀)) →
    (∀ e ∈ I, ∀ l, (graphQuadCells Q e.1 l).carrier ⊆ (graphSlotParent distance X Y l).carrier) →
    let q := fun e : (ℕ × ℕ) × Bool => graphChosenRepresentative
      (graphAngularScale_pos N sig ((p:ℝ)-a) hc) ((min_le_left _ _).trans hcap) distance e.2 axis e.1.1 e.1.2
    let b := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
    let M := fun l => ((2:ℝ)^N)^(-mass l p)
    let F := fun e : GraphNonedgeIndex => graphOriginalTerm ρ (fun l => (graphQuadCells Q e.1 l).carrier) M b
      distance e.2.2 axis (graphAngularScale N sig ((p:ℝ)-a) c₀) v e.2.1.1 e.2.1.2 Ψ
    ‖((2:ℝ)^(2*(v-a))) • (graphProfileCoefficient N mass a p • (∑ e ∈ I, F e)) -
      ((2:ℝ)^(2*(v-a))) • (graphProfileCoefficient N mass a p •
        (∑ e ∈ graphRetainedIndices I N sig p distance Q q, F e))‖ ≤ ((2:ℝ)^N)^(-T) := by
  classical
  obtain ⟨N₀,hbound⟩ := uniform_regularized_original_nonedge_sum hsig K lam T hΨ hsupp hc hcap
  refine ⟨N₀,?_⟩
  intro N hN ι inst S d k hcard hK L hL Q hQ hQside ρ mass B δ hd J i h hh hhbound
    a p v ha hap hp hu ht hLu hv distance X Y hX hY hXa hYa hsep axis I hI hparent
  let q := fun e : (ℕ × ℕ) × Bool => graphChosenRepresentative
    (graphAngularScale_pos N sig ((p:ℝ)-a) hc) ((min_le_left _ _).trans hcap) distance e.2 axis e.1.1 e.1.2
  let keep := fun e : GraphNonedgeIndex => GraphRetainedEdge N sig p distance e.2.2 (graphQuadCells Q e.1) (q e.2)
  let bad := I.filter (fun e => ¬keep e)
  have hbad : bad ⊆ graphNonedgeIndices p (angularBinCount (graphAngularScale N sig ((p:ℝ)-a) c₀)) :=
    (Finset.filter_subset _ _).trans hI
  have hparents : ∀ e ∈ bad, ∀ l, (graphQuadCells Q e.1 l).carrier ⊆ (graphSlotParent distance X Y l).carrier :=
    fun e he => hparent e (Finset.mem_of_mem_filter e he)
  have hlabels : ∀ e ∈ bad,
      (GraphSourceRepresentative distance e.2.2 axis (graphAngularScale N sig ((p:ℝ)-a) c₀)
          e.2.1.1 e.2.1.2 (q e.2) ∧
        GraphNonedge N sig p (graphSourceSign distance e.2.2) (graphRepresentativeZ distance e.2.2 (q e.2))
          (graphRepresentativeAxis distance e.2.2 (q e.2))
          ((graphQuadCells Q e.1 0).center-(graphQuadCells Q e.1 1).center)
          ((graphQuadCells Q e.1 2).center-(graphQuadCells Q e.1 3).center)) ∨
      ¬(tsupport (graphSourceWeight distance e.2.2 axis
        (angularBinCount (graphAngularScale N sig ((p:ℝ)-a) c₀)) e.2.1.1 e.2.1.2)).Nonempty := by
    intro e he
    rcases graphChosenRepresentative_spec (graphAngularScale_pos N sig ((p:ℝ)-a) hc)
      ((min_le_left _ _).trans hcap) distance e.2.2 axis e.2.1.1 e.2.1.2 with hrep | hempty
    · exact Or.inl ⟨hrep,graph_nonedge_of_not_retained N sig p distance e.2.2 (graphQuadCells Q e.1)
        (q e.2) (Finset.mem_filter.mp he).2⟩
    · exact Or.inr hempty
  have he := hbound N hN S d k hcard hK L hL Q hQ hQside ρ mass B δ hd J i h hh hhbound
    a p v ha hap hp hu ht hLu hv distance X Y hX hY hXa hYa hsep axis q bad hbad hparents hlabels
  dsimp only
  rw [graphRetainedIndices,graph_sum_minus_retained]
  exact he

end PlanarFalconer

end OAI
