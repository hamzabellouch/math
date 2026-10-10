import OAI.MeasureTheory.Falconer.Estimates.ProductMatrix

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def activeProductMatrixNeighbors (I : Finset GraphNonedgeIndex)
    (p j b : ℕ) (θ : ℝ) (plus reverse : Bool) (row : CellPath × CellPath) :
    Finset (CellPath × CellPath) := by
  classical
  exact if (tsupport (graphSourceWeight false plus 0 (angularBinCount θ) j b)).Nonempty
    then productMatrixNeighbors I p j b plus reverse row else ∅

noncomputable def graphSupportedProductIndices (I : Finset GraphNonedgeIndex) (θ : ℝ) :
    Finset GraphNonedgeIndex := by
  classical
  exact I.filter (fun e => (tsupport (graphSourceWeight false e.2.2 0
    (angularBinCount θ) e.2.1.1 e.2.1.2)).Nonempty)

theorem graphOriginalProductSum_supported (I : Finset GraphNonedgeIndex)
    (ρ : Fin 4 → Measure Plane) (Q : Fin 4 → DyadicSquare) (M : Fin 4 → ℝ)
    (β : Fin 4 → Plane → UnitCircle → ℂ) (θ v : ℝ) (Ψ : ℝ → ℝ) :
    (∑ e ∈ I, graphOriginalTerm ρ (fun l => (graphQuadCells Q e.1 l).carrier) M β
      false e.2.2 0 θ v e.2.1.1 e.2.1.2 Ψ) =
    ∑ e ∈ graphSupportedProductIndices I θ,
      graphOriginalTerm ρ (fun l => (graphQuadCells Q e.1 l).carrier) M β
        false e.2.2 0 θ v e.2.1.1 e.2.1.2 Ψ := by
  classical
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro e he hn
  apply graphOriginalTerm_zero_of_empty_weight_support
  intro hs
  exact hn (Finset.mem_filter.mpr ⟨he,hs⟩)

theorem activeProductMatrixNeighbors_eq_supported (I : Finset GraphNonedgeIndex)
    (p j b : ℕ) (θ : ℝ) (plus reverse : Bool) (row : CellPath × CellPath) :
    activeProductMatrixNeighbors I p j b θ plus reverse row =
      productMatrixNeighbors (graphSupportedProductIndices I θ) p j b plus reverse row := by
  classical
  ext c
  cases reverse <;> by_cases hs : (tsupport (graphSourceWeight false plus 0 (angularBinCount θ) j b)).Nonempty <;>
    simp [activeProductMatrixNeighbors,productMatrixNeighbors,graphSupportedProductIndices,productMatrixIndex,hs]

theorem uniform_actual_product_degrees {sig : ℝ} (hsig : 0 < sig)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {ι : Type} [DecidableEq ι],
    ∀ (S : Finset ι) (d : ι → PolicyDescriptor) (k : ι → ℕ),
    ∀ Q₁ Q₂ : DyadicSquare, Q₁.side = 1 → Q₂.side = 1 →
    ∀ (ρ ν : Measure Plane) (mass : ℝ → ℝ) (lam : ℝ) (i : ℕ), i < J →
    ∀ (h : Plane → ℂ) (γ : Plane → UnitCircle → ℂ), ∀ e ∈ S, ∀ a g n : ℕ,
    d e = .parallel g (a+n) → a ≤ g → g ≤ a+n → a+n ≤ N → (g:ℝ)-a ≤ 2*sig*N →
    ∀ A B : CellPath, A.length = a → B.length = a →
    ∀ c₀ : ℝ, ∀ hc : 0 < c₀, ∀ hcap : c₀ ≤ 2*Real.pi,
    let θ := graphAngularScale N sig (((a+n:ℕ):ℝ)-a) c₀
    let rep := fun e : (ℕ × ℕ) × Bool => graphChosenRepresentative
      (graphAngularScale_pos N sig (((a+n:ℕ):ℝ)-a) hc) ((min_le_left _ _).trans hcap) false e.2 0 e.1.1 e.1.2
    let β := inheritedCircleSymbol S d k Q₁ ρ mass N lam sig J i h
    let I := sourceRetainedProductIndices Q₁ Q₂ ρ ν β γ A B a n (angularBinCount θ) N sig rep
    ∀ (j b : ℕ) (plus reverse : Bool) (row : CellPath × CellPath),
    ((activeProductMatrixNeighbors I (a+n) j b θ plus reverse row).card : ℝ) ≤
      144*((2:ℝ)^N)^(height (fun t : ℕ => mass t-(t:ℝ)/(N:ℝ)) a (a+n)+2000*(lam+sig)+64*sig) := by
  classical
  obtain ⟨N₀,hcount⟩ := uniform_inherited_product_pair_degree hsig hJ
  refine ⟨N₀,?_⟩
  intro N hN ι inst S d k Q₁ Q₂ hQ₁ hQ₂ ρ ν mass lam i hi h γ e he a g n hd hag hgp hp hgap A B hA hB c₀ hc hcap
  dsimp only
  let θ := graphAngularScale N sig (((a+n:ℕ):ℝ)-a) c₀
  let rep := fun e : (ℕ × ℕ) × Bool => graphChosenRepresentative
    (graphAngularScale_pos N sig (((a+n:ℕ):ℝ)-a) hc) ((min_le_left _ _).trans hcap) false e.2 0 e.1.1 e.1.2
  let β := inheritedCircleSymbol S d k Q₁ ρ mass N lam sig J i h
  let I := sourceRetainedProductIndices Q₁ Q₂ ρ ν β γ A B a n (angularBinCount θ) N sig rep
  intro j b plus reverse row
  change ((activeProductMatrixNeighbors I (a+n) j b θ plus reverse row).card : ℝ) ≤ _
  by_cases hs : (tsupport (graphSourceWeight false plus 0 (angularBinCount θ) j b)).Nonempty
  · rw [activeProductMatrixNeighbors,ite_eq_left hs]
    have hq : GraphSourceRepresentative false plus 0 θ j b (rep ((j,b),plus)) := by
      rcases graphChosenRepresentative_spec (graphAngularScale_pos N sig (((a+n:ℕ):ℝ)-a) hc)
        ((min_le_left _ _).trans hcap) false plus 0 j b with hq | hn
      · exact hq
      · exact (hn hs).elim
    have hdata (col : CellPath × CellPath) (hc : col ∈ productMatrixNeighbors I (a+n) j b plus reverse row) :=
      productMatrixNeighbors_data Q₁ Q₂ ρ ν β γ A B a n (angularBinCount θ) N sig hA hB rep I
        (fun _ hi => (sourceRetainedProductIndices_data Q₁ Q₂ ρ ν β γ A B a n _ N sig rep hi).1)
        (fun _ hi => (sourceRetainedProductIndices_data Q₁ Q₂ ρ ν β γ A B a n _ N sig rep hi).2.1)
        (fun _ hi => (sourceRetainedProductIndices_data Q₁ Q₂ ρ ν β γ A B a n _ N sig rep hi).2.2)
        j b plus reverse row col hc
    exact hcount N hN S d k Q₁ Q₂ hQ₁ hQ₂ ρ mass lam i hi h e he a g (a+n) hd hag hgp hp hgap
      A row (productMatrixNeighbors I (a+n) j b plus reverse row)
      (fun c hc => (hdata c hc).1) (fun c hc => (hdata c hc).2.1)
      (fun c hc => (hdata c hc).2.2.1) c₀ hc hcap j b plus (rep ((j,b),plus)) hq
      (fun c hc => by simpa only [Nat.cast_add] using (hdata c hc).2.2.2.1) (fun c hc => (hdata c hc).2.2.2.2)
  · rw [activeProductMatrixNeighbors,ite_eq_right hs,Finset.card_empty,Nat.cast_zero]
    positivity

end PlanarFalconer

end OAI
