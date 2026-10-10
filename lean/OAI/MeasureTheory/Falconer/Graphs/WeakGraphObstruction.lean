import OAI.MeasureTheory.Falconer.Graphs.RegularGraphCosts

namespace OAI

/-! The regular graph obstruction with all polynomial constants absorbed
at sufficiently fine dyadic scales. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 theorem weak_graph_obstruction {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (M : ℕ) (hM : 1 ≤ M) :
    ∃ γ : ℝ, ∃ N0 : ℕ, 0 < γ ∧ 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      let δ := (1/2:ℝ)^N
      let R := Real.exp (γ*(N:ℝ)*Real.log 2)
      ∀ (t : ℝ) (I X Y : Finset ℝ) (A B : ℝ → Finset ℝ),
      2*κ ≤ t → t ≤ 2 → I.Nonempty → X.Nonempty → Y.Nonempty → X.card = Y.card →
      (∀ x ∈ X, |x| ≤ 1) →
      (∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x-y|) →
      (∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → δ ≤ |x-y|) →
      (∀ i ∈ I, A i ⊆ X) → (∀ i ∈ I, B i ⊆ Y) →
      (∀ i ∈ I, R⁻¹*(X.card:ℝ) ≤ ((A i).card:ℝ)) →
      (∀ i ∈ I, R⁻¹*(Y.card:ℝ) ≤ ((B i).card:ℝ)) →
      (∀ i ∈ I, i ≠ 0 ∧ |i| ≤ M ∧ |i⁻¹| ≤ M) →
      (∀ i ∈ I, ((scalarCells δ (A i+(B i).image (fun y => i*y))).card:ℝ) ≤ R*(X.card:ℝ)) →
      ∀ (e : ℝ → ℝ → ℝ → Prop) (G : Finset (Space 2)),
      NormalizedFiniteBallBound δ t R G →
      (∀ i ∈ I, ∀ x ∈ A i, R⁻¹*((B i).card:ℝ) ≤ (((B i).filter fun y => e i x y).card:ℝ)) →
      (∀ i ∈ I, ∀ x ∈ A i, ∀ y ∈ B i, e i x y → rowPoint x y ∈ G) →
      (G.card:ℝ) ≤ R*(X.card:ℝ)*(Y.card:ℝ) →
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass I u r ≤ R*r^(2*κ)*(I.card:ℝ)) →
      Real.log (X.card:ℝ) ≤ (1-κ)*(N:ℝ)*Real.log 2 → False := by
  obtain ⟨ε,N0,hε,hN0,hobs⟩ := regular_graph_obstruction hκ hκ1 M hM
  obtain ⟨N1,hN1,hloss⟩ := scalar_fixed_losses hε
    (zero_lt_one.trans_le (regularGraphCost_one_le M)) zero_lt_one
  let γ := ε/80
  have hγ : 0 < γ := by dsimp [γ]; positivity
  refine ⟨γ,max N0 N1,hγ,lt_of_lt_of_le hN0 (le_max_left _ _),?_⟩
  intro N hN
  dsimp only
  intro t I X Y A B ht ht2 hI hX hY hXY hXbound hXsep hYsep hA hB hsizeA hsizeB
    hc hproj e G hreg hdegree hgraph hGsize hIball hXsize
  let R := Real.exp (γ*(N:ℝ)*Real.log 2)
  let W := Real.exp (ε*(N:ℝ)*Real.log 2)
  have hR : 1 ≤ R := Real.one_le_exp_iff.mpr (by positivity)
  have hRpos : 0 < R := Real.exp_pos _
  have hcost : regularGraphCost M*R^20 ≤ W := by
    have he : R^20 = Real.exp ((ε/4)*(N:ℝ)*Real.log 2) := by
      rw [show R = Real.exp (γ*(N:ℝ)*Real.log 2) from rfl,← Real.exp_nat_mul]
      congr 1
      dsimp [γ]
      ring
    rw [he]
    exact (hloss N ((le_max_right _ _).trans hN)).1
  obtain ⟨hD,hQ,hP,hC⟩ := regular_graph_weak_costs hκ1 ht2 M hM hR
  exact hobs N ((le_max_left _ _).trans hN) R⁻¹ R R⁻¹ t R R R I X Y A B
    (inv_pos.mpr hRpos) hRpos.le (inv_pos.mpr hRpos) ht hR hRpos.le hR
    hI hX hY hXY hXbound hXsep hYsep hA hB hsizeA hsizeB hc hproj e G hreg
    hdegree hgraph hGsize hIball hXsize (hD.trans hcost) (by simpa only [Nat.cast_mul] using hQ.trans hcost)
    (hP.trans hcost) (hC.trans hcost)

end Falconer

end OAI
