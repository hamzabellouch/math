import OAI.MeasureTheory.Falconer.Measures.ProductMatrixSchur

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate
attribute [local instance] Classical.propDecidable

theorem product_matrix_complex_bound (I : Finset GraphNonedgeIndex) (p j b : ℕ) (θ : ℝ)
    (plus : Bool) (U V : CellPath → ℂ) (W : ℂ) (d : ℝ)
    (hdegree : ∀ (reverse : Bool) (row : CellPath × CellPath),
      ((activeProductMatrixNeighbors I p j b θ plus reverse row).card : ℝ) ≤ d) :
    let C := (dyadicPaths p) ×ˢ (dyadicPaths p)
    let H := graphSupportedProductIndices I θ
    ‖∑ row ∈ C, ∑ col ∈ C, if productMatrixIndex row col j b plus ∈ H
      then W*(U row.1*conj (U col.1))*(V row.2*conj (V col.2)) else 0‖ ≤
    ‖W‖*d*(∑ row ∈ C, ‖U row.1‖^2*‖V row.2‖^2) := by
  classical
  dsimp only
  let C := (dyadicPaths p) ×ˢ (dyadicPaths p)
  let H := graphSupportedProductIndices I θ
  let f := fun row : CellPath × CellPath => ‖U row.1‖*‖V row.2‖
  have hh := product_matrix_schur I p j b θ plus f f d hdegree
  dsimp only at hh
  have he : (∑ row ∈ C, ∑ col ∈ C,
      ‖if productMatrixIndex row col j b plus ∈ H
        then W*(U row.1*conj (U col.1))*(V row.2*conj (V col.2)) else 0‖) =
      ‖W‖*(∑ row ∈ C, ∑ col ∈ C, if productMatrixIndex row col j b plus ∈ H
        then f row*f col else 0) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro row _
    apply Finset.sum_congr rfl
    intro col _
    split_ifs
    · simp only [norm_mul,Complex.norm_conj,f]
      ring
    · simp only [norm_zero,mul_zero]
  calc
    _ ≤ ∑ row ∈ C, ‖∑ col ∈ C, if productMatrixIndex row col j b plus ∈ H
        then W*(U row.1*conj (U col.1))*(V row.2*conj (V col.2)) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ row ∈ C, ∑ col ∈ C, ‖if productMatrixIndex row col j b plus ∈ H
        then W*(U row.1*conj (U col.1))*(V row.2*conj (V col.2)) else 0‖ :=
      Finset.sum_le_sum (fun _ _ => norm_sum_le _ _)
    _ = _ := he
    _ ≤ ‖W‖*(d/2*((∑ row ∈ C, f row^2)+(∑ row ∈ C, f row^2))) :=
      mul_le_mul_of_nonneg_left hh (norm_nonneg _)
    _ = _ := by simp only [f,mul_pow]; ring

theorem sourceGraphFourTransform_product_matrix
    (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane) (M₁ M₂ : ℝ)
    (β γ : Plane → UnitCircle → ℂ) (W : UnitCircle × UnitCircle → ℂ)
    (r : ℝ) (u w : UnitCircle) (row col : CellPath × CellPath) :
    sourceGraphFourTransform ![ρ,ρ,ν,ν]
      (fun l => (productPairCells Q₁ Q₂ row col l).carrier) ![M₁,M₁,M₂,M₂] ![β,β,γ,γ] W r u w =
    W (u,w)*
      (sourceAngularTransform ρ (Q₁.descendant row.1).carrier M₁ β r u *
        conj (sourceAngularTransform ρ (Q₁.descendant col.1).carrier M₁ β r u))*
      (sourceAngularTransform ν (Q₂.descendant row.2).carrier M₂ γ r w *
        conj (sourceAngularTransform ν (Q₂.descendant col.2).carrier M₂ γ r w)) := rfl

theorem uniform_actual_product_matrix_integrand {sig : ℝ} (hsig : 0 < sig)
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
    ∀ (j b : ℕ) (plus : Bool) (U V : CellPath → ℂ) (W : ℂ),
    let C := (dyadicPaths (a+n)) ×ˢ (dyadicPaths (a+n))
    let H := graphSupportedProductIndices I θ
    ‖∑ row ∈ C, ∑ col ∈ C, if productMatrixIndex row col j b plus ∈ H
      then W*(U row.1*conj (U col.1))*(V row.2*conj (V col.2)) else 0‖ ≤
    ‖W‖*(144*((2:ℝ)^N)^(height (fun t : ℕ => mass t-(t:ℝ)/(N:ℝ)) a (a+n)+2000*(lam+sig)+64*sig))*
      (∑ row ∈ C, ‖U row.1‖^2*‖V row.2‖^2) := by
  classical
  obtain ⟨N₀,hdegree⟩ := uniform_actual_product_degrees hsig hJ
  refine ⟨N₀,?_⟩
  intro N hN ι inst S d k Q₁ Q₂ hQ₁ hQ₂ ρ ν mass lam i hi h γ e he a g n hd hag hgp hp hgap A B hA hB c₀ hc hcap
  have hh := hdegree N hN S d k Q₁ Q₂ hQ₁ hQ₂ ρ ν mass lam i hi h γ e he a g n hd hag hgp hp hgap A B hA hB c₀ hc hcap
  dsimp only at hh ⊢
  intro j b plus U V W
  exact product_matrix_complex_bound _ _ j b _ plus U V W _ (hh j b plus)

end PlanarFalconer

end OAI
