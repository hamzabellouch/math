import OAI.Analysis.CircleDomains.Selection.TrackedTestSequence

namespace OAI

/-! Every saved tolerance stays in the actual finite history. Thus each
later test change is bounded by its geometric share of that tolerance. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace AppendingSequence
variable {G : Set Sphere} {a ε : ℝ}
variable (hsupply : FiniteAppendingSupply G a)
  (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
  (hTD : IsTotallyDisconnected Gᶜ) (ha : 0 < a)
  (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ Metric.ball 0 a) (hε : 0 < ε)
  (T : FiniteCompactTests G)
local notation "states" => appendingStates hsupply hsard hsch hG hinf hTD ha hBa hε T

 def savedTolerance (n : ℕ) : ℝ :=
  ((states n).chooseStep hsupply hsard hsch hG hinf hTD ha hBa hε n).saved.tolerance

local notation "τ" => savedTolerance hsupply hsard hsch hG hinf hTD ha hBa hε T

 theorem savedTolerance_pos (n : ℕ) : 0 < τ n :=
  ((states n).chooseStep hsupply hsard hsch hG hinf hTD ha hBa hε n).saved.tolerance_pos

 theorem history_mono {n k : ℕ} (hnk : n ≤ k) {t : ℝ}
    (ht : t ∈ (states n).tolerances) : t ∈ (states k).tolerances := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hnk
  induction r with
  | zero => exact ht
  | succ r ih =>
    change t ∈ _ :: (states (n+r)).tolerances
    exact List.mem_cons_of_mem _ (ih (Nat.le_add_right _ _))

 theorem savedTolerance_mem (n : ℕ) : τ n ∈ (states (n+1)).tolerances :=
  List.mem_cons_self

 theorem later_budget_le_saved {n k : ℕ} (hnk : n+1 ≤ k) :
    recursiveTestBudget ε k (states k).tolerances ≤ (1/2 : ℝ)^(k+3)*τ n := by
  exact recursiveTestBudget_le_saved k
    (history_mono hsupply hsard hsch hG hinf hTD ha hBa hε T hnk
      (savedTolerance_mem hsupply hsard hsch hG hinf hTD ha hBa hε T n))

end AppendingSequence
end CircleDomainRigidity

end

end OAI
