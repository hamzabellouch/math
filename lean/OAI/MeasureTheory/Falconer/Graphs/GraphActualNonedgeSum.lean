import OAI.MeasureTheory.Falconer.Graphs.GraphOriginalNonedgePower
import OAI.MeasureTheory.Falconer.Graphs.GraphNonedgeFiniteSum
import OAI.MeasureTheory.Falconer.Graphs.GraphActualQuadCells
import OAI.MeasureTheory.Falconer.Graphs.GraphProfileCoefficient

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem graphOriginalTerm_zero_of_empty_weight_support
    (ρ : Fin 4 → Measure Plane) (X : Fin 4 → Set Plane) (M : Fin 4 → ℝ)
    (b : Fin 4 → Plane → UnitCircle → ℂ) (distance plus : Bool) (axis δ v : ℝ)
    (j k : ℕ) (Ψ : ℝ → ℝ)
    (hS : ¬(tsupport (graphSourceWeight distance plus axis (angularBinCount δ) j k)).Nonempty) :
    graphOriginalTerm ρ X M b distance plus axis δ v j k Ψ = 0 := by
  have hw (u w : UnitCircle) : graphSourceWeight distance plus axis (angularBinCount δ) j k (u,w) = 0 := by
    by_contra hn
    exact hS ⟨(u,w),subset_closure hn⟩
  simp [graphOriginalTerm,sourceGraphFourTransform,hw]

theorem uniform_regularized_original_nonedge_sum {sig : ℝ} (hsig : 0 < sig)
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
    ∀ (axis : ℝ) (q : (ℕ × ℕ) × Bool → UnitCircle × UnitCircle) (I : Finset GraphNonedgeIndex),
    I ⊆ graphNonedgeIndices p (angularBinCount (graphAngularScale N sig ((p:ℝ)-a) c₀)) →
    (∀ e ∈ I, ∀ l, (graphQuadCells Q e.1 l).carrier ⊆ (graphSlotParent distance X Y l).carrier) →
    (∀ e ∈ I,
      (GraphSourceRepresentative distance e.2.2 axis (graphAngularScale N sig ((p:ℝ)-a) c₀)
          e.2.1.1 e.2.1.2 (q e.2) ∧
        GraphNonedge N sig p (graphSourceSign distance e.2.2) (graphRepresentativeZ distance e.2.2 (q e.2))
          (graphRepresentativeAxis distance e.2.2 (q e.2))
          ((graphQuadCells Q e.1 0).center-(graphQuadCells Q e.1 1).center)
          ((graphQuadCells Q e.1 2).center-(graphQuadCells Q e.1 3).center)) ∨
      ¬(tsupport (graphSourceWeight distance e.2.2 axis
        (angularBinCount (graphAngularScale N sig ((p:ℝ)-a) c₀)) e.2.1.1 e.2.1.2)).Nonempty) →
    let b := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
    let M := fun l => ((2:ℝ)^N)^(-mass l p)
    ‖((2:ℝ)^(2*(v-a))) • (graphProfileCoefficient N mass a p •
      (∑ e ∈ I, graphOriginalTerm ρ (fun l => (graphQuadCells Q e.1 l).carrier) M b distance e.2.2 axis
        (graphAngularScale N sig ((p:ℝ)-a) c₀) v e.2.1.1 e.2.1.2 Ψ))‖ ≤ ((2:ℝ)^N)^(-T) := by
  obtain ⟨N₁,hterm⟩ := uniform_actual_original_nonedge_power hsig K lam (T+13) hΨ hsupp hc hcap
  obtain ⟨N₂,hsum⟩ := uniform_graph_nonedge_sum_power hsig.le hc hcap
  refine ⟨max N₁ N₂,?_⟩
  intro N hN ι inst S d k hcard hK L hL Q hQ hQside ρ mass B δ hd J i h hh hhbound
    a p v ha hap hp hu ht hLu hv distance X Y hX hY hXa hYa hsep axis q I hI hparent hlabel
  let : ∀ l, IsProbabilityMeasure (ρ l) := fun l => (hd l).probability
  let b := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
  let M := fun l => ((2:ℝ)^N)^(-mass l p)
  let F := fun e : GraphNonedgeIndex => graphOriginalTerm ρ (fun l => (graphQuadCells Q e.1 l).carrier)
    M b distance e.2.2 axis (graphAngularScale N sig ((p:ℝ)-a) c₀) v e.2.1.1 e.2.1.2 Ψ
  have hcoeff := graphProfileCoefficient_bounds Q ρ N B δ lam mass hd ha hap (Nat.cast_le.mpr hp)
  have hpoint : ∀ e ∈ I, ‖F e‖ ≤ ((2:ℝ)^N)^(-(T+13)) := by
    intro e he
    have hquad : e.1 ∈ graphCellQuadIndices p := by
      have hh := hI he
      simp only [graphNonedgeIndices,Finset.product_eq_sprod,Finset.mem_product] at hh
      exact hh.1
    rcases hlabel e he with ⟨hq,hfail⟩ | hempty
    · exact hterm N ((le_max_left _ _).trans hN) S d k hcard hK L hL Q hQ ρ mass J i h hh hhbound
        a p v hu ht hLu distance e.2.2 X Y hX hY hXa hYa hsep (graphQuadCells Q e.1)
        (graphQuadCells_pos Q hQ e.1) (graphQuadCells_side_le Q hQside hquad) (hparent e he) M
        (fun _ => by dsimp [M]; positivity) (graphQuadCells_profile_mass_le Q ρ N B δ lam mass hd hp hquad)
        axis e.2.1.1 e.2.1.2 (q e.2) hq hfail
    · have hz := graphOriginalTerm_zero_of_empty_weight_support ρ (fun l => (graphQuadCells Q e.1 l).carrier)
        M b distance e.2.2 axis (graphAngularScale N sig ((p:ℝ)-a) c₀) v e.2.1.1 e.2.1.2 Ψ hempty
      change ‖F e‖ ≤ _
      rw [show F e = 0 from hz,norm_zero]
      positivity
  have he := hsum N ((le_max_right _ _).trans hN) p hp ((p:ℝ)-a)
    (by have hp' : (p:ℝ) ≤ N := Nat.cast_le.mpr hp; linarith) T ((2:ℝ)^(2*(v-a))) I hI F
    (fun _ => graphProfileCoefficient N mass a p)
    (fun _ _ => by rw [abs_of_nonneg hcoeff.1]; exact hcoeff.2) (graph_original_outer_le N hv) hpoint
  simpa only [← Finset.smul_sum] using he

end PlanarFalconer

end OAI
