import OAI.MeasureTheory.Falconer.Graphs.GraphInheritedNonedge

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem uniform_actual_graph_nonedge_power {sig : ℝ} (hsig : 0 < sig) (K : ℕ) (T : ℝ)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {c₀ : ℝ} (hc : 0 < c₀) (hcap : c₀ ≤ 2*Real.pi) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
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
      ((2:ℝ)^N)^(-T) := by
  obtain ⟨n,hn⟩ := exists_nat_gt ((T+1)/(26*sig))
  have hn' : T+1 < 26*sig*(n:ℝ) := by
    simpa only [mul_comm (n:ℝ) (26*sig)] using
      (div_lt_iff₀ (by positivity : (0:ℝ) < 26*sig)).mp hn
  have hgap : 0 < 26*sig*(n:ℝ)-T := by linarith
  obtain ⟨A,hA,N₁,hbound⟩ := uniform_actual_graph_nonedge_bound hsig K n hΨ hsupp hc hcap
  obtain ⟨N₂,hconst⟩ := fixed_constant_absorbed hgap
    (8*A*volume.real (Metric.closedBall (0:Plane) 8)*16^n)
  refine ⟨max N₁ N₂,?_⟩
  intro N hN ι inst S d k hcard hK L hL Q hQ ρ mass lam J i h x hx a p v hu ht hLu
    distance plus X Y hX hY hXa hYa hsep P hP hPp hparent hxp axis j₁ j₂ q hq hfail
  have hi := hbound N ((le_max_left _ _).trans hN) S d k hcard hK L hL Q hQ ρ mass lam J i h x hx
    a p v hu ht hLu distance plus X Y hX hY hXa hYa hsep P hP hPp hparent hxp axis j₁ j₂ q hq hfail
  apply hi.trans
  calc
    _ ≤ ((2:ℝ)^N)^(26*sig*(n:ℝ)-T)*((2:ℝ)^N)^(-26*sig*(n:ℝ)) :=
      mul_le_mul_of_nonneg_right (hconst N ((le_max_right _ _).trans hN)) (by positivity)
    _ = ((2:ℝ)^N)^(-T) := by
      rw [← Real.rpow_add (by positivity : (0:ℝ) < (2:ℝ)^N)]
      congr 1
      ring

end PlanarFalconer

end OAI
