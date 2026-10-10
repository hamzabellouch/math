import OAI.MeasureTheory.Falconer.Geometry.CommonUnbalancedProjections
import OAI.MeasureTheory.Falconer.Graphs.GraphScalarRegularity

namespace OAI

/-! The actual regular common reference with comparable coordinate counts. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 theorem common_unbalanced_regular_reference {α : Type*} {δ ρ K η t Kreg L Q : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hK : 0 ≤ K) (hQ : 1 ≤ Q) (hη : 0 < η)
    (ht : 0 ≤ t) (hKreg : 1 ≤ Kreg) (hL : 0 ≤ L)
    (I : Finset α) (X Y : Finset ℝ) (A B : α → Finset ℝ) (c : α → ℝ)
    (hI : I.Nonempty) (hX : X.Nonempty) (hY : Y.Nonempty) (hXY : (X.card:ℝ) ≤ Q*(Y.card:ℝ))
    (hXsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x-y|)
    (hYsep : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → δ ≤ |x-y|)
    (hA : ∀ i ∈ I, A i ⊆ X) (hB : ∀ i ∈ I, B i ⊆ Y)
    (hsizeA : ∀ i ∈ I, ρ*(X.card:ℝ) ≤ ((A i).card:ℝ))
    (hsizeB : ∀ i ∈ I, ρ*(Y.card:ℝ) ≤ ((B i).card:ℝ))
    (M : ℕ) (hc : ∀ i ∈ I, c i ≠ 0 ∧ |c i| ≤ M ∧ |(c i)⁻¹| ≤ M)
    (hproj : ∀ i ∈ I, ((scalarCells δ (A i+(B i).image (fun y => c i*y))).card:ℝ) ≤
      K*(X.card:ℝ))
    (e : α → ℝ → ℝ → Prop) (G : Finset (Space 2))
    (hreg : NormalizedFiniteBallBound δ t Kreg G)
    (hdegree : ∀ i ∈ I, ∀ x ∈ A i,
      η*((B i).card:ℝ) ≤ (((B i).filter fun y => e i x y).card:ℝ))
    (hgraph : ∀ i ∈ I, ∀ x ∈ A i, ∀ y ∈ B i, e i x y → rowPoint x y ∈ G)
    (hGsize : (G.card:ℝ) ≤ L*(X.card:ℝ)*(Y.card:ℝ)) :
    ∃ i₀ ∈ I, ∃ J ⊆ I,
      ρ^4*(I.card:ℝ) ≤ 2*(J.card:ℝ) ∧ (A i₀).Nonempty ∧
      ((scalarCells δ (A i₀+A i₀)).card:ℝ) ≤
        (1024*(2*M+3)^2*K^4*Q^2/ρ^6)*(scalarCells δ (A i₀)).card ∧
      (∀ j ∈ J,
        ((scalarCells δ (A i₀-(A i₀).image (fun x => (c j/c i₀)*x))).card:ℝ) ≤
          (4096*(2*(M*M)+3)*(2*M+3)^2*K^4*Q^2/ρ^13)*(scalarCells δ (A i₀)).card) ∧
      ∀ u r : ℝ, δ ≤ r → scalarBallMass (A i₀) u r ≤
        Real.sqrt ((2*(K/ρ)*Kreg*(L/ρ^2)/η)*(1+4*(M:ℝ))^t)*
          r^(t/2)*((A i₀).card:ℝ) := by
  classical
  obtain ⟨i₀,hi₀,J,hJI,hJ,hAi,hd,hr⟩ := common_unbalanced_ratio_projections
    hδ hρ hK hQ I X Y A B c hI hX hY hXY hXsep hYsep hA hB hsizeA hsizeB M hc hproj
  refine ⟨i₀,hi₀,J,hJI,hJ,hAi,hd,hr,?_⟩
  have hYpos : 0 < (Y.card:ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hY)
  have hBi : (B i₀).Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp
    ((mul_pos hρ hYpos).trans_le (hsizeB i₀ hi₀)))
  have hXA : (X.card:ℝ) ≤ ((A i₀).card:ℝ)/ρ :=
    (le_div_iff₀ hρ).2 (by simpa only [mul_comm] using hsizeA i₀ hi₀)
  have hYB : (Y.card:ℝ) ≤ ((B i₀).card:ℝ)/ρ :=
    (le_div_iff₀ hρ).2 (by simpa only [mul_comm] using hsizeB i₀ hi₀)
  have hGp : (G.card:ℝ) ≤ (L/ρ^2)*((A i₀).card:ℝ)*((B i₀).card:ℝ) := by
    calc
      _ ≤ L*(X.card:ℝ)*(Y.card:ℝ) := hGsize
      _ = L*((X.card:ℝ)*(Y.card:ℝ)) := by ring
      _ ≤ L*((((A i₀).card:ℝ)/ρ)*(((B i₀).card:ℝ)/ρ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hXA hYB (Nat.cast_nonneg _)
          (by positivity)) hL
      _ = _ := by ring
  have hsmall : ((scalarCells δ (A i₀+(B i₀).image (fun y => c i₀*y))).card:ℝ) ≤
      (K/ρ)*((A i₀).card:ℝ) := by
    calc
      _ ≤ K*(X.card:ℝ) := hproj i₀ hi₀
      _ ≤ K*(((A i₀).card:ℝ)/ρ) := mul_le_mul_of_nonneg_left hXA hK
      _ = _ := by ring
  exact scalar_graph_ball_bound hδ ht (hc i₀ hi₀).1 (hc i₀ hi₀).2.2
    (div_nonneg hK hρ.le) hKreg hη (div_nonneg hL (sq_nonneg _))
    (A i₀) (B i₀) hAi hBi
    (fun x hx y hy hne => hXsep x (hA i₀ hi₀ hx) y (hA i₀ hi₀ hy) hne)
    (e i₀) G hreg (hdegree i₀ hi₀) (hgraph i₀ hi₀) hGp hsmall

end Falconer

end OAI
