import Mathlib
import OAI.Geometry.HyperbolicGroups.StarCoupling
import OAI.Geometry.HyperbolicGroups.Distinct
import OAI.Geometry.HyperbolicGroups.StarError

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction

lemma ratio_error_bound {M Z D ε : ℝ} (hM : 0 < M) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hZ : (1-ε)*M ≤ Z) (hD : D ≤ ε*M) : D/Z ≤ ε/(1-ε) := by
  have hp : 0 < 1-ε := sub_pos.mpr hε1
  have hZp := lt_of_lt_of_le (mul_pos hp hM) hZ
  apply (div_le_div_iff₀ hZp hp).mpr
  have h₁ := mul_le_mul_of_nonneg_right hD hp.le
  have h₂ := mul_le_mul_of_nonneg_left hZ hε0
  nlinarith

namespace StarModel
variable {F R A : Type*} [Fintype F] [Fintype R] [Fintype A]
  [DecidableEq F] [DecidableEq R] [DecidableEq A] [Nonempty A] {k : ℕ}

/-- The error statistic constructs the source coupling on the very same table.
There is no independent choice of a table for different branch marginals. -/
lemma coupling_of_error (support : R → Finset F) (U I : Finset F) (hI : I ⊆ U)
    (e : F) (he : e ∉ U) (p : R → ℝ) (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1)
    (a₀ : A) (b₀ : Fin (k+1) ↪ A) (w : TableModel.Entry (A := A) support → Bool)
    [Nonempty (Stars (B := Fin (k+1)) support U w)] [Nonempty (Matches support w)]
    {ε : ℝ} (hε1 : ε < 1)
    (hM : 0 < (TableModel.law (A := A) support p hp).expect
      (fun w => (starCount (B := Fin (k+1)) support U w : ℝ)))
    (hε : normalizedError support U e p hp a₀ b₀ w ≤ ε) :
    (∀ j : Fin (k+1), ((coupling (k := k) support U I hI w).map (ConditionalStar.branch j)).totalVariation
      FiniteLaw.uniform ≤ ε/(1-ε)) ∧
    ((coupling (k := k) support U I hI w).map (fun z j => (ConditionalStar.branch j z).val e)).totalVariation
      (FiniteLaw.uniform : FiniteLaw (Fin (k+1) → A)) ≤ ε/(1-ε) +
        (1 - ((Fintype.card A).descFactorial (k+1) : ℝ) / (Fintype.card A : ℝ)^(k+1)) := by
  let : Nonempty (Fin (k+1) ↪ A) := ⟨b₀⟩
  let μ := TableModel.law (A := A) support p hp
  let M := μ.expect (fun w => (starCount (B := Fin (k+1)) support U w : ℝ))
  let Z : ℝ := starCount (B := Fin (k+1)) support U w
  have hε0 := (normalizedError_nonneg support U e p hp a₀ b₀ w).trans hε
  obtain ⟨hE,hL⟩ := deviations_le_of_error support U e p hp a₀ b₀ w hM hε
  have hZ : (1-ε)*M ≤ Z := by
    have hl := starCount_lower support U e he p hp a₀ b₀ w
    change M - _ ≤ Z at hl
    change _ ≤ ε*M at hL
    linarith
  constructor
  · intro j
    apply (coupling_branch_bound support U I hI w j
      (μ.expect (fun w => (extensionCount support U j (fun _ => a₀) w : ℝ)))).trans
    rw [← branchDeviation_subtype]
    exact ratio_error_bound hM hε0 hε1 hZ (hE j)
  · have hh := coupling_leaves_bound (k := k) support U I hI e he w a₀
      (μ.expect (fun w => (leafCount support U e (leafValues U b₀ a₀) w : ℝ)))
    rw [FiniteLaw.distinct_tv] at hh
    simp only [Fintype.card_fin] at hh
    apply hh.trans
    exact add_le_add (ratio_error_bound hM hε0 hε1 hZ hL) le_rfl

end StarModel
end HyperbolicObstruction
end
end

section

end
end

end OAI
