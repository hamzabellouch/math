import OAI.NumberTheory.TotientAsymptotic.GoodTuples
import OAI.NumberTheory.TotientAsymptotic.CollisionGridScale

namespace OAI

/-! The original good-witness slack at a nearby counting endpoint. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma good_slack_endpoint_budget {x Y δ : ℝ} {H i p : ℕ}
    {η : RemainderDatum (L x H)} (hg : GoodWitnessConditions p η) (hi : i≤ R x H)
    (hh : 1≤ m x-i) (hY : 0< Y) (hcoord : remainderCoord x η i≤ Y+1)
    (hδ : 1/Y≤δ) :
    (∑ r ∈ Finset.Icc (i+1) (L x H), a (r-i)*remainderCoord x η r) ≤
      (1-(1/((m x-i : ℕ) : ℝ)^4-δ))*Y := by
  have hhR : (1 : ℝ)≤(m x-i : ℕ) := by exact_mod_cast hh
  have hp : (1 : ℝ)≤((m x-i : ℕ) : ℝ)^4 := one_le_pow₀ hhR
  have hs : 1/((m x-i : ℕ) : ℝ)^4≤1 := (div_le_one (by positivity)).mpr hp
  have hslack := (hg i (Finset.mem_Icc.mpr ⟨Nat.zero_le _,hi⟩)).1
  have hu := mul_le_mul_of_nonneg_left hcoord (show 0≤1-1/((m x-i : ℕ) : ℝ)^4 by linarith)
  have hd := (div_le_iff₀ hY).mp hδ
  have hs0 : 0≤1/((m x-i : ℕ) : ℝ)^4 := by positivity
  nlinarith

lemma inverse_le_collisionMesh {x y : ℝ} {i : ℕ}
    (hS : 1≤ B (normalityScale x i)) (hY : 1≤ B y) :
    1/B y≤ collisionMesh x y i := by
  have hBy : 0< B y := zero_lt_one.trans_le hY
  have hp : 1≤ B (normalityScale x i)*B y := by nlinarith
  have hs : 1≤ Real.sqrt (B (normalityScale x i)*B y) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    simpa using hp
  exact div_le_div_of_nonneg_right hs hBy.le

end TotientAsymptotic

end

end OAI
