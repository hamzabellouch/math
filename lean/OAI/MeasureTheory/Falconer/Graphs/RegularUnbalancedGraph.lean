import OAI.MeasureTheory.Falconer.Estimates.CommonUnbalancedReference
import OAI.MeasureTheory.Falconer.Estimates.ScalarWeakReference

namespace OAI

/-! Refined-graph obstruction with comparable coordinate cardinalities. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 theorem regular_unbalanced_graph_obstruction {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    :
    ∃ ε : ℝ, ∃ N0 : ℕ, 0 < ε ∧ 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      let δ := (1/2:ℝ)^N
      let W := Real.exp (ε*(N:ℝ)*Real.log 2)
      ∀ (M : ℕ), 1 ≤ M → (M:ℝ)^2 ≤ W →
      ∀ (Q ρ K η t Kreg L KI : ℝ) (I X Y : Finset ℝ) (A B : ℝ → Finset ℝ),
      1 ≤ Q → 0 < ρ → 0 ≤ K → 0 < η → 2*κ ≤ t → 1 ≤ Kreg → 0 ≤ L → 1 ≤ KI →
      I.Nonempty → X.Nonempty → Y.Nonempty → (X.card:ℝ) ≤ Q*(Y.card:ℝ) →
      (∀ x ∈ X, |x| ≤ 1) →
      (∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x-y|) →
      (∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → δ ≤ |x-y|) →
      (∀ i ∈ I, A i ⊆ X) → (∀ i ∈ I, B i ⊆ Y) →
      (∀ i ∈ I, ρ*(X.card:ℝ) ≤ ((A i).card:ℝ)) →
      (∀ i ∈ I, ρ*(Y.card:ℝ) ≤ ((B i).card:ℝ)) →
      (∀ i ∈ I, i ≠ 0 ∧ |i| ≤ M ∧ |i⁻¹| ≤ M) →
      (∀ i ∈ I, ((scalarCells δ (A i+(B i).image (fun y => i*y))).card:ℝ) ≤ K*(X.card:ℝ)) →
      ∀ (e : ℝ → ℝ → ℝ → Prop) (G : Finset (Space 2)),
      NormalizedFiniteBallBound δ t Kreg G →
      (∀ i ∈ I, ∀ x ∈ A i, η*((B i).card:ℝ) ≤ (((B i).filter fun y => e i x y).card:ℝ)) →
      (∀ i ∈ I, ∀ x ∈ A i, ∀ y ∈ B i, e i x y → rowPoint x y ∈ G) →
      (G.card:ℝ) ≤ L*(X.card:ℝ)*(Y.card:ℝ) →
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass I u r ≤ KI*r^(2*κ)*(I.card:ℝ)) →
      Real.log (X.card:ℝ) ≤ (1-κ)*(N:ℝ)*Real.log 2 →
      1024*(2*M+3)^2*K^4*Q^2/ρ^6 ≤ W →
      4096*(2*(M*M)+3)*(2*M+3)^2*K^4*Q^2/ρ^13 ≤ W →
      Real.sqrt ((2*(K/ρ)*Kreg*(L/ρ^2)/η)*(1+4*(M:ℝ))^t) ≤ W →
      (2/ρ^4)*KI*(M:ℝ)^(2*κ) ≤ W → False := by
  obtain ⟨ε,N0,hε,hN0,hobstruction⟩ := scalar_weak_reference_obstruction hκ hκ1
  refine ⟨ε,N0,hε,hN0,?_⟩
  intro N hN
  dsimp only
  intro M hM hMcost Q ρ K η t Kreg L KI I X Y A B hQ hρ hK hη ht hKreg hL hKI hI hX hY hXY
    hXbound hXsep hYsep hA hB hsizeA hsizeB hc hproj e G hreg hdegree hgraph hGsize
    hIball hXsize hDcost hQcost hPcost hIcost
  let δ := (1/2:ℝ)^N
  let W := Real.exp (ε*(N:ℝ)*Real.log 2)
  have hδ : 0 < δ := by positivity
  obtain ⟨i₀,hi₀,J,hJI,hJ,hAi,hd,hq,hpoint⟩ := common_unbalanced_regular_reference hδ hρ hK hQ hη
    (by linarith : 0 ≤ t) hKreg hL I X Y A B id hI hX hY hXY hXsep hYsep
    hA hB hsizeA hsizeB M hc hproj e G hreg hdegree hgraph hGsize
  have hJne : J.Nonempty := by
    apply Finset.card_pos.mp
    have hpos : 0 < ρ^4*(I.card:ℝ) := mul_pos (pow_pos hρ _)
      (Nat.cast_pos.mpr (Finset.card_pos.mpr hI))
    have : 0 < (J.card:ℝ) := by linarith
    exact_mod_cast this
  have hIJ : (I.card:ℝ) ≤ (2/ρ^4)*(J.card:ℝ) := by
    have hh : (I.card:ℝ) ≤ (2*(J.card:ℝ))/ρ^4 :=
      (le_div_iff₀ (pow_pos hρ 4)).2 (by simpa only [mul_comm] using hJ)
    convert hh using 1; ring
  have hAc : (scalarCells δ (A i₀)).card = (A i₀).card :=
    Finset.card_image_of_injOn (scalarCells_injective hδ
      (fun x hx y hy hne => hXsep x (hA i₀ hi₀ hx) y (hA i₀ hi₀ hy) hne))
  rw [hAc] at hd hq
  have hd' : ((scalarCells δ (A i₀+A i₀)).card:ℝ) ≤ W*((A i₀).card:ℝ) :=
    hd.trans (mul_le_mul_of_nonneg_right hDcost (Nat.cast_nonneg _))
  have hq' : ∀ a ∈ J, ((scalarCells δ (A i₀-(A i₀).image (fun x => (a/i₀)*x))).card:ℝ) ≤
      W*((A i₀).card:ℝ) := fun a ha =>
    (hq a ha).trans (mul_le_mul_of_nonneg_right hQcost (Nat.cast_nonneg _))
  have hAiSize : Real.log ((A i₀).card:ℝ) ≤ (1-κ)*(N:ℝ)*Real.log 2 :=
    (Real.log_le_log (Nat.cast_pos.mpr (Finset.card_pos.mpr hAi))
      (Nat.cast_le.mpr (Finset.card_le_card (hA i₀ hi₀)))).trans hXsize
  have hpoint' : ∀ u r : ℝ, δ ≤ r → r ≤ 1 →
      scalarBallMass (A i₀) u r ≤ W*r^κ*((A i₀).card:ℝ) := by
    intro u r hr hr1
    have hp : r^(t/2) ≤ r^κ := Real.rpow_le_rpow_of_exponent_ge
      (hδ.trans_le hr) hr1 (by linarith)
    have hh := mul_le_mul hPcost hp (Real.rpow_nonneg (hδ.le.trans hr) _) (Real.exp_pos _).le
    exact (hpoint u r hr).trans (mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg _))
  exact hobstruction N hN M hM hMcost (A i₀) I J i₀ (2/ρ^4) KI hAi hJne hJI
    (hc i₀ hi₀).1 (hc i₀ hi₀).2.1 (hc i₀ hi₀).2.2 hKI hIJ
    (fun x hx => hXbound x (hA i₀ hi₀ hx))
    (fun x hx y hy hne => hXsep x (hA i₀ hi₀ hx) y (hA i₀ hi₀ hy) hne)
    (fun i hi => (hc i hi).2.1) hAiSize hd' hpoint' hIball hIcost hq'

end Falconer

end OAI
