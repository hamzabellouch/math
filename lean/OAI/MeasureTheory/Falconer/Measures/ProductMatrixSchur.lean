import OAI.MeasureTheory.Falconer.Graphs.ActualProductDegrees
import OAI.MeasureTheory.Falconer.Graphs.FinsetSchur

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

theorem product_matrix_schur (I : Finset GraphNonedgeIndex) (p j b : ℕ) (θ : ℝ)
    (plus : Bool) (u v : CellPath × CellPath → ℝ) (d : ℝ)
    (hdegree : ∀ (reverse : Bool) (row : CellPath × CellPath),
      ((activeProductMatrixNeighbors I p j b θ plus reverse row).card : ℝ) ≤ d) :
    let V := (dyadicPaths p) ×ˢ (dyadicPaths p)
    let H := graphSupportedProductIndices I θ
    (∑ row ∈ V, ∑ col ∈ V, if productMatrixIndex row col j b plus ∈ H then u row*v col else 0) ≤
      d/2*((∑ row ∈ V, u row^2)+(∑ col ∈ V, v col^2)) := by
  classical
  dsimp only
  apply finset_bipartite_schur
  · intro row _
    simpa only [activeProductMatrixNeighbors_eq_supported,productMatrixNeighbors,Bool.false_eq_true,↓reduceIte]
      using hdegree false row
  · intro col _
    simpa only [activeProductMatrixNeighbors_eq_supported,productMatrixNeighbors,↓reduceIte]
      using hdegree true col

theorem uniform_actual_product_matrix_schur {sig : ℝ} (hsig : 0 < sig)
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
    ∀ (j b : ℕ) (plus : Bool) (u v : CellPath × CellPath → ℝ),
    let V := (dyadicPaths (a+n)) ×ˢ (dyadicPaths (a+n))
    let H := graphSupportedProductIndices I θ
    (∑ row ∈ V, ∑ col ∈ V, if productMatrixIndex row col j b plus ∈ H then u row*v col else 0) ≤
      (144*((2:ℝ)^N)^(height (fun t : ℕ => mass t-(t:ℝ)/(N:ℝ)) a (a+n)+2000*(lam+sig)+64*sig))/2*
        ((∑ row ∈ V, u row^2)+(∑ col ∈ V, v col^2)) := by
  classical
  obtain ⟨N₀,hdegree⟩ := uniform_actual_product_degrees hsig hJ
  refine ⟨N₀,?_⟩
  intro N hN ι inst S d k Q₁ Q₂ hQ₁ hQ₂ ρ ν mass lam i hi h γ e he a g n hd hag hgp hp hgap A B hA hB c₀ hc hcap
  have hh := hdegree N hN S d k Q₁ Q₂ hQ₁ hQ₂ ρ ν mass lam i hi h γ e he a g n hd hag hgp hp hgap A B hA hB c₀ hc hcap
  dsimp only at hh ⊢
  intro j b plus u v
  exact product_matrix_schur _ _ j b _ plus u v _ (hh j b plus)

end PlanarFalconer

end OAI
