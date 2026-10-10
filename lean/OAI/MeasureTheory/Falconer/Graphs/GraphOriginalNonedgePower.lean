import OAI.MeasureTheory.Falconer.Graphs.GraphInheritedNonedgePower
import OAI.MeasureTheory.Falconer.Graphs.GraphFourTransformPointIntegral
import OAI.MeasureTheory.Falconer.Graphs.GraphFourMassBound

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

noncomputable def graphOriginalTerm (ρ : Fin 4 → Measure Plane) (X : Fin 4 → Set Plane)
    (M : Fin 4 → ℝ) (b : Fin 4 → Plane → UnitCircle → ℂ)
    (distance plus : Bool) (axis δ v : ℝ) (j k : ℕ) (Ψ : ℝ → ℝ) : ℂ :=
  ((2:ℝ)^v)⁻¹ • (∫ r : ℝ, ∫ u, ∫ w, Ψ (r/(2:ℝ)^v) •
    sourceGraphFourTransform ρ X M b (graphSourceWeight distance plus axis (angularBinCount δ) j k) r u w
      ∂sourceArcLength ∂sourceArcLength)

theorem uniform_actual_original_nonedge_power {sig : ℝ} (hsig : 0 < sig) (K : ℕ) (lam T : ℝ)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {c₀ : ℝ} (hc : 0 < c₀) (hcap : c₀ ≤ 2*Real.pi) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 4 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, (∑ t ∈ S l, k l t) ≤ K) →
    ∀ L : ℕ, (∀ l t, t ∈ S l → descriptorLength (d l t) ≤ L) →
    ∀ Q : Fin 4 → DyadicSquare, (∀ l, 0 < (Q l).side) →
    ∀ (ρ : Fin 4 → Measure Plane) [∀ l, IsFiniteMeasure (ρ l)],
    ∀ (mass : Fin 4 → ℝ → ℝ) (J i : ℕ) (h : Fin 4 → Plane → ℂ),
    (∀ l, Measurable (h l)) → (∀ l x, ‖h l x‖ ≤ 1) →
    ∀ a p v : ℝ, 0 ≤ v-p → p-a ≤ v-p+2*sig*(N:ℝ) → (L:ℝ) ≤ v-p+2*sig*(N:ℝ) →
    ∀ (distance plus : Bool) (X Y : DyadicSquare), 0 < X.side → 0 < Y.side →
    X.side ≤ (2:ℝ)^(-a) → Y.side ≤ (2:ℝ)^(-a) →
    (distance = true → dist X.center Y.center ≤ 2000*(2:ℝ)^(-a)) →
    ∀ P : Fin 4 → DyadicSquare, (∀ l, 0 < (P l).side) →
    (∀ l, (P l).side ≤ (2:ℝ)^(-p)) →
    (∀ l, (P l).carrier ⊆ (graphSlotParent distance X Y l).carrier) →
    ∀ M : Fin 4 → ℝ, (∀ l, 0 < M l) →
    (∀ l, (ρ l (P l).carrier).toReal / M l ≤ ((2:ℝ)^N)^(3*lam)) →
    ∀ (axis : ℝ) (j₁ j₂ : ℕ) (q : UnitCircle × UnitCircle),
    GraphSourceRepresentative distance plus axis (graphAngularScale N sig (p-a) c₀) j₁ j₂ q →
    GraphNonedge N sig p (graphSourceSign distance plus) (graphRepresentativeZ distance plus q)
      (graphRepresentativeAxis distance plus q) ((P 0).center-(P 1).center) ((P 2).center-(P 3).center) →
    let b := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l)
      N lam sig J i (h l)
    ‖graphOriginalTerm ρ (fun l => (P l).carrier) M b distance plus axis
      (graphAngularScale N sig (p-a) c₀) v j₁ j₂ Ψ‖ ≤ ((2:ℝ)^N)^(-T) := by
  obtain ⟨N₀,hbound⟩ := uniform_actual_graph_nonedge_power hsig K (T+12*lam) hΨ hsupp hc hcap
  refine ⟨N₀,?_⟩
  intro N hN ι inst S d k hcard hK L hL Q hQ ρ instρ mass J i h hh hhbound a p v hu ht hLu
    distance plus X Y hX hY hXa hYa hsep P hP hPp hparent M hM hmass axis j₁ j₂ q hq hfail
  let b := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
  change ‖graphOriginalTerm ρ (fun l => (P l).carrier) M b distance plus axis
    (graphAngularScale N sig (p-a) c₀) v j₁ j₂ Ψ‖ ≤ _
  rw [graphOriginalTerm,actual_inherited_fourTransform_pointIntegral S d k Q hQ ρ mass N lam sig J i
    h hh hhbound K hK (fun l => (P l).carrier) M distance plus axis
    (graphAngularScale N sig (p-a) c₀) v j₁ j₂ hΨ.continuous hsupp]
  have hp : ∀ x : Fin 4 → Plane, (∀ l, x l ∈ (P l).carrier) →
      ‖graphPointIntegral (graphAmplitudePullback b x distance plus axis
        (graphAngularScale N sig (p-a) c₀) j₁ j₂ Ψ) v (graphSourceSign distance plus)
        (x 0-x 1) (x 2-x 3)‖ ≤ ((2:ℝ)^N)^(-(T+12*lam)) := by
    intro x hx
    exact hbound N hN S d k hcard hK L hL Q hQ ρ mass lam J i h x (fun l => hhbound l (x l))
      a p v hu ht hLu distance plus X Y hX hY hXa hYa hsep P hP hPp hparent hx axis j₁ j₂ q hq hfail
  have he := normalized_four_integral_power_le ρ (fun l => (P l).carrier)
    (fun l => (P l).measurable) M hM _ (by positivity : (0:ℝ) < (2:ℝ)^N) hp hmass
  convert he using 1
  congr 1
  ring

end PlanarFalconer

end OAI
