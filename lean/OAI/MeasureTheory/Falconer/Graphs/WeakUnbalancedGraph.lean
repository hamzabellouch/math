import OAI.MeasureTheory.Falconer.Graphs.RegularUnbalancedGraph
import OAI.MeasureTheory.Falconer.Graphs.RegularGraphRadiusCosts

namespace OAI

/-! Scale-absorbed graph obstruction for comparable coordinate sets and
weakly growing coefficient radius. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 theorem weak_unbalanced_graph_obstruction {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    :
    ∃ γ : ℝ, ∃ N0 : ℕ, 0 < γ ∧ 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      let δ := (1/2:ℝ)^N
      let R := Real.exp (γ*(N:ℝ)*Real.log 2)
      ∀ (M : ℕ), 1 ≤ M → (M:ℝ) ≤ R →
      ∀ (Q : ℝ), 1 ≤ Q → Q ≤ R →
      ∀ (t : ℝ) (I X Y : Finset ℝ) (A B : ℝ → Finset ℝ),
      2*κ ≤ t → t ≤ 2 → I.Nonempty → X.Nonempty → Y.Nonempty → (X.card:ℝ) ≤ Q*(Y.card:ℝ) →
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
  obtain ⟨ε,N0,hε,hN0,hobs⟩ := regular_unbalanced_graph_obstruction hκ hκ1
  obtain ⟨N1,hN1,hloss⟩ := scalar_fixed_losses hε
    (by norm_num : (0:ℝ) < 1048576) zero_lt_one
  let γ := ε/104
  have hγ : 0 < γ := by dsimp [γ]; positivity
  refine ⟨γ,max N0 N1,hγ,lt_of_lt_of_le hN0 (le_max_left _ _),?_⟩
  intro N hN
  dsimp only
  intro M hM hMR Q hQ1 hQR t I X Y A B ht ht2 hI hX hY hXY hXbound hXsep hYsep hA hB hsizeA hsizeB
    hc hproj e G hreg hdegree hgraph hGsize hIball hXsize
  let R := Real.exp (γ*(N:ℝ)*Real.log 2)
  let W := Real.exp (ε*(N:ℝ)*Real.log 2)
  have hR : 1 ≤ R := Real.one_le_exp_iff.mpr (by positivity)
  have hRpos : 0 < R := Real.exp_pos _
  have hcost : regularGraphCost M*R^22 ≤ W := by
    have hb := mul_le_mul_of_nonneg_right (regular_graph_radius_cost hR M hMR)
      (show 0 ≤ R^22 by positivity)
    have he : R^26 = Real.exp ((ε/4)*(N:ℝ)*Real.log 2) := by
      rw [show R = Real.exp (γ*(N:ℝ)*Real.log 2) from rfl,← Real.exp_nat_mul]
      congr 1
      dsimp [γ]
      ring
    calc
      _ ≤ 1048576*R^4*R^22 := hb
      _ = 1048576*R^26 := by ring
      _ ≤ W := by rw [he]; exact (hloss N ((le_max_right _ _).trans hN)).1
  have hMcost : (M:ℝ)^2 ≤ W := by
    apply (pow_le_pow_left₀ (Nat.cast_nonneg M) hMR 2).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hlog : 0 ≤ (N:ℝ)*Real.log 2 := by positivity
    dsimp [γ]
    nlinarith
  obtain ⟨hD,hRatio,hP,hC⟩ := regular_graph_weak_costs hκ1 ht2 M hM hR
  have hbase : regularGraphCost M*R^20 ≤ W :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR (show 20 ≤ (22:ℕ) by omega))
      (zero_le_one.trans (regularGraphCost_one_le M))).trans hcost
  have hQ2 : Q^2 ≤ R^2 := pow_le_pow_left₀ (zero_le_one.trans hQ1) hQR 2
  have hD' : (1024*(2*(M:ℝ)+3)^2*R^4/(R⁻¹)^6)*Q^2 ≤ W := by
    have hh := mul_le_mul hD hQ2 (sq_nonneg Q) (mul_nonneg (zero_le_one.trans (regularGraphCost_one_le M)) (by positivity))
    apply le_trans _ hcost
    convert hh using 1; ring
  have hRatio' : (4096*(2*((M*M:ℕ):ℝ)+3)*(2*(M:ℝ)+3)^2*R^4/(R⁻¹)^13)*Q^2 ≤ W := by
    have hh := mul_le_mul hRatio hQ2 (sq_nonneg Q) (mul_nonneg (zero_le_one.trans (regularGraphCost_one_le M)) (by positivity))
    apply le_trans _ hcost
    convert hh using 1; ring
  exact hobs N ((le_max_left _ _).trans hN) M hM hMcost Q R⁻¹ R R⁻¹ t R R R I X Y A B
    hQ1 (inv_pos.mpr hRpos) hRpos.le (inv_pos.mpr hRpos) ht hR hRpos.le hR
    hI hX hY hXY hXbound hXsep hYsep hA hB hsizeA hsizeB hc hproj e G hreg
    hdegree hgraph hGsize hIball hXsize
    (by convert hD' using 1; ring)
    (by
      have hh := hRatio'
      push_cast at hh
      convert hh using 1; ring)
    (hP.trans hbase) (hC.trans hbase)

end Falconer

end OAI
