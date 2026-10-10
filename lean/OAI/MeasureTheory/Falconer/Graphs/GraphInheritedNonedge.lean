import OAI.MeasureTheory.Falconer.Graphs.GraphNonedgeIntegralErrors
import OAI.MeasureTheory.Falconer.Graphs.GraphNonedgeAmplitude

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem uniform_actual_graph_nonedge_bound {sig : ℝ} (hsig : 0 < sig) (K n : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {c₀ : ℝ} (hc : 0 < c₀) (hcap : c₀ ≤ 2*Real.pi) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 4 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, (∑ t ∈ S l, k l t) ≤ K) →
    ∀ L : ℕ, (∀ l t, t ∈ S l → descriptorLength (d l t) ≤ L) →
    ∀ Q : Fin 4 → DyadicSquare, (∀ l, 0 < (Q l).side) →
    ∀ (ρ : Fin 4 → Measure Plane) (mass : Fin 4 → ℝ → ℝ)
    (lam : ℝ) (J i : ℕ) (h : Fin 4 → Plane → ℂ) (x : Fin 4 → Plane),
    (∀ l, ‖h l (x l)‖ ≤ 1) →
    ∀ a p v : ℝ, 0 ≤ v-p → p-a ≤ v-p+2*sig*(N:ℝ) → (L:ℝ) ≤ v-p+2*sig*(N:ℝ) →
    ∀ (distance plus : Bool) (X Y : DyadicSquare), 0 < X.side → 0 < Y.side →
    X.side ≤ (2:ℝ)^(-a) → Y.side ≤ (2:ℝ)^(-a) →
    (distance = true → dist X.center Y.center ≤ 2000*(2:ℝ)^(-a)) →
    ∀ P : Fin 4 → DyadicSquare, (∀ l, 0 < (P l).side) →
    (∀ l, (P l).side ≤ (2:ℝ)^(-p)) →
    (∀ l, (P l).carrier ⊆ (graphSlotParent distance X Y l).carrier) → (∀ l, x l ∈ (P l).carrier) →
    ∀ (axis : ℝ) (j₁ j₂ : ℕ) (q : UnitCircle × UnitCircle),
    GraphSourceRepresentative distance plus axis (graphAngularScale N sig (p-a) c₀) j₁ j₂ q →
    GraphNonedge N sig p (graphSourceSign distance plus) (graphRepresentativeZ distance plus q)
      (graphRepresentativeAxis distance plus q) ((P 0).center-(P 1).center) ((P 2).center-(P 3).center) →
    let b := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l)
      N lam sig J i (h l)
    ‖graphPointIntegral
      (graphAmplitudePullback b x distance plus axis (graphAngularScale N sig (p-a) c₀) j₁ j₂ Ψ)
      v (graphSourceSign distance plus) (x 0-x 1) (x 2-x 3)‖ ≤
      8*A*volume.real (Metric.closedBall (0:Plane) 8)*16^n*((2:ℝ)^N)^(-26*sig*(n:ℝ)) := by
  obtain ⟨A,hA,N₁,hamp⟩ := uniform_actual_graph_amplitude_E hsig K n hΨ hc hcap
  obtain ⟨N₂,hgeom⟩ := uniform_graph_actual_nonedge_geometry hsig
  refine ⟨A,hA,max N₁ N₂,?_⟩
  intro N hN ι inst S d k hcard hK L hL Q hQ ρ mass lam J i h x hx a p v hu ht hLu
    distance plus X Y hX hY hXa hYa hsep P hP hPp hparent hxp axis j₁ j₂ q hq hfail
  let b := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l)
    N lam sig J i (h l)
  have hf := hamp N ((le_max_left _ _).trans hN) S d k hcard hK L hL Q hQ ρ mass lam J i h x hx
    (p-a) (v-p) hu ht hLu distance plus axis j₁ j₂
  have hs := graphAmplitudePullback_tsupport b x distance plus axis (graphAngularScale N sig (p-a) c₀) j₁ j₂ hsupp
  have hcent := graph_source_parent_center_bounds distance X Y P hX hY hXa hYa hsep hP hparent
  have hg := hgeom N ((le_max_right _ _).trans hN) a p c₀ hc
    P hP hPp hcent.1 hcent.2 distance plus axis j₁ j₂ q hq b x hxp Ψ hsupp
  exact graphPointIntegral_nonedge_of_errors n N sig v p _ _ _ _ _ _ _ hf hs hA hg hfail

end PlanarFalconer

end OAI
