import OAI.MeasureTheory.Falconer.Graphs.WeakUnbalancedGraph
import OAI.MeasureTheory.Falconer.Estimates.ScalarUnbalancedRefinement
import OAI.MeasureTheory.Falconer.Graphs.DenseGraphComparableParameters

namespace OAI

/-! Dense original graph obstruction for actual, comparable coordinate
sets and a weakly growing coordinate ratio bound. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 theorem dense_unbalanced_graph_obstruction {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    :
    ∃ γ : ℝ, ∃ N0 : ℕ, 0 < γ ∧ 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      let δ := (1/2:ℝ)^N
      let S := Real.exp (γ*(N:ℝ)*Real.log 2)
      ∀ (M : ℕ), 1 ≤ M → (M:ℝ) ≤ S →
      ∀ (Q : ℝ), 1 ≤ Q → Q ≤ S →
      ∀ (t : ℝ) (I X Y : Finset ℝ) (e : ℝ → ℝ → ℝ → Prop) (D : ℝ → Finset ℤ)
        (G : Finset (Space 2)),
      2*κ ≤ t → t ≤ 2 → I.Nonempty → X.Nonempty → Y.Nonempty → (X.card:ℝ) ≤ Q*(Y.card:ℝ) →
      (∀ x ∈ X, |x| ≤ 1) →
      (∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x-y|) →
      (∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → δ ≤ |x-y|) →
      (∀ i ∈ I, ∀ x ∈ Y.image (fun y => i*y), ∀ y ∈ Y.image (fun y => i*y), x ≠ y → δ ≤ |x-y|) →
      (∀ i ∈ I, i ≠ 0 ∧ |i| ≤ M ∧ |i⁻¹| ≤ M) →
      (∀ i ∈ I, S⁻¹*(X.card:ℝ)*(Y.card:ℝ) ≤ ∑ x ∈ X, ((Y.filter fun y => e i x y).card:ℝ)) →
      (∀ i ∈ I, ∀ x ∈ X, ∀ y ∈ Y, e i x y → ⌊(x+i*y)/δ⌋ ∈ D i) →
      (∀ i ∈ I, ((D i).card:ℝ) ≤ S*(X.card:ℝ)) →
      NormalizedFiniteBallBound δ t S G →
      (∀ i ∈ I, ∀ x ∈ X, ∀ y ∈ Y, e i x y → rowPoint x y ∈ G) →
      (G.card:ℝ) ≤ S*(X.card:ℝ)*(Y.card:ℝ) →
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass I u r ≤ S*r^(2*κ)*(I.card:ℝ)) →
      Real.log (X.card:ℝ) ≤ (1-κ)*(N:ℝ)*Real.log 2 → False := by
  classical
  obtain ⟨θ,N0,hθ,hN0,hweak⟩ := weak_unbalanced_graph_obstruction hκ hκ1
  obtain ⟨γ,N1,hγ,hN1,hparameters⟩ := dense_graph_comparable_parameters hθ
  refine ⟨γ,max N0 N1,hγ,lt_of_lt_of_le hN0 (le_max_left _ _),?_⟩
  intro N hN
  dsimp only
  intro M hM hMS Q hQ1 hQS t I X Y e D G ht ht2 hI hX hY hXY hXbound hXsep hYsep hcYsep hc hdense hlabels
    hDcard hreg hgraph hGsize hIball hXsize
  let δ := (1/2:ℝ)^N
  let S := Real.exp (γ*(N:ℝ)*Real.log 2)
  let R := Real.exp (θ*(N:ℝ)*Real.log 2)
  have hδ : 0 < δ := by positivity
  obtain ⟨hS,hSR,hprojcost,hdegreecost⟩ := hparameters N ((le_max_right _ _).trans hN)
  have hprojcost' : 67108864*S^13*Q^2 ≤ R := by
    have hQ2 : Q^2 ≤ S^2 := pow_le_pow_left₀ (zero_le_one.trans hQ1) hQS 2
    calc
      _ ≤ 67108864*S^13*S^2 := mul_le_mul_of_nonneg_left hQ2 (by positivity)
      _ = 67108864*S^15 := by ring
      _ ≤ R := hprojcost
  have hex : ∀ i : ℝ, ∃ A B : Finset ℝ, i ∈ I →
      A ⊆ X ∧ B ⊆ Y ∧ R⁻¹*(X.card:ℝ) ≤ (A.card:ℝ) ∧
      R⁻¹*(Y.card:ℝ) ≤ (B.card:ℝ) ∧
      ((scalarCells δ (A+B.image (fun y => i*y))).card:ℝ) ≤ R*(X.card:ℝ) ∧
      ∀ x ∈ A, R⁻¹*(B.card:ℝ) ≤ ((B.filter fun y => e i x y).card:ℝ) := by
    intro i
    by_cases hi : i ∈ I
    · obtain ⟨A,hAX,B,hBY,hA,hB,hproj,hdegree⟩ := scalar_dilated_unbalanced_refinement
        hδ hS (hc i hi).1 X Y hX hY hXY hXsep (hcYsep i hi) (e i) (D i)
        (hdense i hi) (hlabels i hi) (hDcard i hi)
      refine ⟨A,B,fun _ => ⟨hAX,hBY,?_,?_,?_,?_⟩⟩
      · exact (mul_le_mul_of_nonneg_right hdegreecost (Nat.cast_nonneg _)).trans hA
      · exact (mul_le_mul_of_nonneg_right hdegreecost (Nat.cast_nonneg _)).trans hB
      · exact hproj.trans (mul_le_mul_of_nonneg_right hprojcost' (Nat.cast_nonneg _))
      · intro x hx
        exact (mul_le_mul_of_nonneg_right hdegreecost (Nat.cast_nonneg _)).trans (hdegree x hx)
    · exact ⟨∅,∅,fun h => (hi h).elim⟩
  choose A B hAB using hex
  have hRreg : NormalizedFiniteBallBound δ t R G := by
    intro z r hr hr1
    have hh := mul_le_mul_of_nonneg_right hSR
      (mul_nonneg (Real.rpow_nonneg (hδ.le.trans hr) t) (Nat.cast_nonneg G.card))
    exact (hreg z r hr hr1).trans (by nlinarith)
  have hRball : ∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass I u r ≤ R*r^(2*κ)*(I.card:ℝ) := by
    intro u r hr hr1
    have hh := mul_le_mul_of_nonneg_right hSR
      (mul_nonneg (Real.rpow_nonneg (hδ.le.trans hr) (2*κ)) (Nat.cast_nonneg I.card))
    exact (hIball u r hr hr1).trans (by nlinarith)
  apply hweak N ((le_max_left _ _).trans hN) M hM (hMS.trans hSR) Q hQ1 (hQS.trans hSR) t I X Y A B ht ht2 hI hX hY hXY
    hXbound hXsep hYsep
    (fun i hi => (hAB i hi).1) (fun i hi => (hAB i hi).2.1)
    (fun i hi => (hAB i hi).2.2.1) (fun i hi => (hAB i hi).2.2.2.1) hc
    (fun i hi => (hAB i hi).2.2.2.2.1) e G hRreg
    (fun i hi => (hAB i hi).2.2.2.2.2)
    (fun i hi x hx y hy he => hgraph i hi x ((hAB i hi).1 hx) y ((hAB i hi).2.1 hy) he)
    (hGsize.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSR
      (Nat.cast_nonneg X.card)) (Nat.cast_nonneg Y.card))) hRball hXsize

end Falconer

end OAI
