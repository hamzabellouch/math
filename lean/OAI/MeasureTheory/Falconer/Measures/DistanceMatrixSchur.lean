import OAI.MeasureTheory.Falconer.Graphs.DistanceSupportedGraph
import OAI.MeasureTheory.Falconer.Measures.ProductMatrixSchur

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable
open scoped ComplexConjugate

theorem distance_matrix_schur_on (I : Finset GraphNonedgeIndex) (p j b : ℕ) (θ axis : ℝ)
    (plus : Bool) (A B : Finset (CellPath × CellPath))
    (hA : A ⊆ (dyadicPaths p) ×ˢ (dyadicPaths p))
    (hB : B ⊆ (dyadicPaths p) ×ˢ (dyadicPaths p))
    (u v : CellPath × CellPath → ℝ) (d : ℝ)
    (hdegree : ∀ reverse row,
      ((activeDistanceMatrixNeighbors I p j b θ axis plus reverse row).card : ℝ) ≤ d) :
    let H := graphSupportedDistanceIndices I θ axis
    (∑ row ∈ A, ∑ col ∈ B, if distanceMatrixIndex row col j b plus ∈ H then u row*v col else 0) ≤
      d/2*((∑ row ∈ A, u row^2)+(∑ col ∈ B, v col^2)) := by
  classical
  dsimp only
  apply finset_bipartite_schur
  · intro row _
    apply (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset_filter _ hB))).trans
    simpa only [activeDistanceMatrixNeighbors_eq_supported,distanceMatrixNeighbors,Bool.false_eq_true,↓reduceIte]
      using hdegree false row
  · intro col _
    apply (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset_filter _ hA))).trans
    simpa only [activeDistanceMatrixNeighbors_eq_supported,distanceMatrixNeighbors,↓reduceIte]
      using hdegree true col

theorem distance_matrix_complex_bound_on (I : Finset GraphNonedgeIndex) (p j b : ℕ) (θ axis : ℝ)
    (plus : Bool) (A B : Finset (CellPath × CellPath))
    (hA : A ⊆ (dyadicPaths p) ×ˢ (dyadicPaths p))
    (hB : B ⊆ (dyadicPaths p) ×ˢ (dyadicPaths p))
    (u v : CellPath × CellPath → ℂ) (weight : ℂ) (d : ℝ)
    (hdegree : ∀ reverse row,
      ((activeDistanceMatrixNeighbors I p j b θ axis plus reverse row).card : ℝ) ≤ d) :
    let H := graphSupportedDistanceIndices I θ axis
    ‖∑ row ∈ A, ∑ col ∈ B, if distanceMatrixIndex row col j b plus ∈ H
      then weight*(u row*conj (v col)) else 0‖ ≤
      ‖weight‖*(d/2*((∑ row ∈ A, ‖u row‖^2)+(∑ col ∈ B, ‖v col‖^2))) := by
  classical
  dsimp only
  have hh := distance_matrix_schur_on I p j b θ axis plus A B hA hB
    (fun row => ‖u row‖) (fun col => ‖v col‖) d hdegree
  calc
    _ ≤ ∑ row ∈ A, ∑ col ∈ B, ‖if distanceMatrixIndex row col j b plus ∈ graphSupportedDistanceIndices I θ axis
        then weight*(u row*conj (v col)) else 0‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ = ‖weight‖*(∑ row ∈ A, ∑ col ∈ B,
        if distanceMatrixIndex row col j b plus ∈ graphSupportedDistanceIndices I θ axis
        then ‖u row‖*‖v col‖ else 0) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro row _
      apply Finset.sum_congr rfl
      intro col _
      split_ifs <;> simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (norm_nonneg _)

theorem uniform_actual_distance_matrix_schur {sig κ c₀ : ℝ} (hsig : 0 < sig)
    (hgap : 10*sig < κ) (hc : 0 < c₀) (hcap : c₀ ≤ 2*Real.pi) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 2 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
    ∀ Q : Fin 2 → DyadicSquare, (∀ l, (Q l).side = 1) →
    ∀ (ρ : Fin 2 → Measure Plane) (m : Fin 2 → ℝ → ℝ) (lam : ℝ) (i : ℕ), i < J →
    ∀ (h : Fin 2 → Plane → ℂ) (e : ∀ l, ι l), (∀ l, e l ∈ S l) →
    ∀ a n : ℕ, (∀ l, d l (e l) = .parallel a (a+n)) → a+n ≤ N → κ*N ≤ (n:ℝ) →
    ∀ A B : CellPath, A.length = a → B.length = a →
    dist ((Q 0).descendant A).center ((Q 1).descendant B).center ≤ 2000*(2:ℝ)^(-(a:ℝ)) →
    let t : ℝ := (a+n:ℕ)-a
    let θ := graphAngularScale N sig t c₀
    let axis := sourceParentAxis ((Q 0).descendant A) ((Q 1).descendant B)
    let rep := fun e : (ℕ × ℕ) × Bool => graphChosenRepresentative
      (graphAngularScale_pos N sig t hc) ((min_le_left _ _).trans hcap) true e.2 axis e.1.1 e.1.2
    let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (m l) N lam sig J i (h l)
    let I := sourceRetainedDistanceIndices (Q 0) (Q 1) (ρ 0) (ρ 1) (β 0) (β 1) A B a n N sig t θ rep
    ∀ (j b : ℕ) (plus : Bool) (U V : Finset (CellPath × CellPath)),
    U ⊆ (dyadicPaths (a+n)) ×ˢ (dyadicPaths (a+n)) →
    V ⊆ (dyadicPaths (a+n)) ×ˢ (dyadicPaths (a+n)) →
    ∀ u v : CellPath × CellPath → ℝ,
    let H := graphSupportedDistanceIndices I θ axis
    (∑ row ∈ U, ∑ col ∈ V, if distanceMatrixIndex row col j b plus ∈ H then u row*v col else 0) ≤
      (144*((2:ℝ)^N)^(min (height (fun t : ℕ => m 0 t-(t:ℝ)/(N:ℝ)) a (a+n))
        (height (fun t : ℕ => m 1 t-(t:ℝ)/(N:ℝ)) a (a+n))+2000*(lam+sig)+60*sig))/2*
      ((∑ row ∈ U, u row^2)+(∑ col ∈ V, v col^2)) := by
  classical
  obtain ⟨N₀,hdegree⟩ := uniform_actual_distance_degrees hsig hgap hc hcap hJ
  refine ⟨N₀,?_⟩
  intro N hN ι inst S d k Q hQ ρ m lam i hi h e he a n hd hp hlow A B hA hB hsep
  have hh := hdegree N hN S d k Q hQ ρ m lam i hi h e he a n hd hp hlow A B hA hB hsep
  dsimp only at hh ⊢
  intro j b plus U V hU hV u v
  exact distance_matrix_schur_on _ _ j b _ _ plus U V hU hV u v _ (hh j b plus)

end PlanarFalconer

end OAI
