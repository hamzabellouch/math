import Mathlib
import OAI.Geometry.HyperbolicGroups.Moment
import OAI.Geometry.HyperbolicGroups.Cost

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace TableModel
variable {F R A : Type*} [Fintype F] [Fintype R] [Fintype A]
  [DecidableEq F] [DecidableEq R] [DecidableEq A]

lemma powerProbability_mem {N : ℝ} (hN : 1 ≤ N) {c : ℝ} (hc : 0 ≤ c) :
    N ^ (-c) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact (Real.rpow_pos_of_pos (by linarith) _).le
  · simpa using Real.rpow_le_rpow_of_exponent_le hN (show -c ≤ 0 by linarith)

lemma powerProbability_pos {N : ℝ} (hN : 1 ≤ N) (c : ℝ) : 0 < N ^ (-c) :=
  Real.rpow_pos_of_pos (by linarith) _

omit [Fintype R] [DecidableEq R] in
lemma inverse_cost_product {N : ℝ} (hN : 1 ≤ N) (c : R → ℝ) (hc : ∀ r, 0 ≤ c r)
    (J : Finset R) :
    (∏ r ∈ J, ((N ^ (-c r))⁻¹ - 1)) ≤ N ^ (∑ r ∈ J, c r) := by
  have hN0 : 0 < N := by linarith
  have he (r : R) : (N ^ (-c r))⁻¹ = N ^ (c r) := by
    rw [Real.rpow_neg hN0.le, inv_inv]
  simp_rw [he]
  rw [Real.rpow_sum_of_pos hN0]
  apply Finset.prod_le_prod₀
  · intro r _
    exact sub_nonneg.mpr (Real.one_le_rpow hN (hc r))
  · intro r _
    linarith

omit [Fintype R] [DecidableEq R] in
lemma cost_term_bound {N ε : ℝ} (hN : 1 ≤ N) (c : R → ℝ) (hc : ∀ r, 0 ≤ c r)
    (support : R → Finset F) (I : Finset F) (J : Finset R)
    (gap : ε ≤ ((J.biUnion support \ I).card : ℝ) - ∑ r ∈ J, c r) :
    N ^ (Fintype.card F - (J.biUnion support ∪ I).card) *
      (∏ r ∈ J, ((N ^ (-c r))⁻¹ - 1)) ≤
        N ^ (Fintype.card F - I.card) * N ^ (-ε) := by
  have hN0 : 0 < N := by linarith
  have hi := Finset.card_le_univ I
  have hu := Finset.card_le_univ (J.biUnion support ∪ I)
  have hcard := Finset.card_union_add_card_inter (J.biUnion support) I
  have hs := Finset.card_sdiff_add_card_inter (J.biUnion support) I
  have he : (Fintype.card F - (J.biUnion support ∪ I).card) +
      (J.biUnion support \ I).card = Fintype.card F - I.card := by omega
  have he' : ((Fintype.card F - (J.biUnion support ∪ I).card : ℕ) : ℝ) +
      (J.biUnion support \ I).card = (Fintype.card F - I.card : ℕ) := by exact_mod_cast he
  calc
    _ ≤ N ^ (Fintype.card F - (J.biUnion support ∪ I).card) * N ^ (∑ r ∈ J, c r) :=
      mul_le_mul_of_nonneg_left (inverse_cost_product hN c hc J) (by positivity)
    _ = N ^ (((Fintype.card F - (J.biUnion support ∪ I).card : ℕ) : ℝ) + ∑ r ∈ J, c r) := by
      rw [Real.rpow_add hN0, Real.rpow_natCast]
    _ ≤ N ^ (((Fintype.card F - I.card : ℕ) : ℝ) + -ε) :=
      Real.rpow_le_rpow_of_exponent_le hN (by linarith)
    _ = _ := by rw [Real.rpow_add hN0, Real.rpow_natCast]

/-- A uniform, explicit finite relative-variance bound for pinned master matches.
No numerical values of the pinned letters occur in this bound. -/
theorem variance_pinned_power [Nonempty A] (support : R → Finset F) (c : R → ℝ)
    (hc : ∀ r, 0 ≤ c r) (I : Finset F) (ξ : F → A) {ε : ℝ}
    (gap : ∀ J : Finset R, J.Nonempty →
      ε ≤ ((J.biUnion support \ I).card : ℝ) - ∑ r ∈ J, c r) :
    let N : ℝ := Fintype.card A
    let hp := fun r => powerProbability_mem (show 1 ≤ N by change (1 : ℝ) ≤ Fintype.card A; exact_mod_cast (show 1 ≤ Fintype.card A from Fintype.card_pos)) (hc r)
    let μ := law support (fun r => N ^ (-c r)) hp
    let X := fun w => (candidateCount support (pinCandidates I ξ) w : ℝ)
    μ.variance X ≤ Fintype.card (Finset R) * N ^ (-ε) * μ.expect X ^ 2 := by
  classical
  dsimp only
  have hn : (1 : ℝ) ≤ Fintype.card A := by
    exact_mod_cast (show 1 ≤ Fintype.card A from Fintype.card_pos)
  let p (r : R) := (Fintype.card A : ℝ) ^ (-c r)
  let hp := fun r => powerProbability_mem hn (hc r)
  change (law support p hp).variance _ ≤ _
  rw [variance_pinCount support p hp (fun r => powerProbability_pos hn (c r)),
    expect_candidateCount, card_pinCandidates]
  have hs : (∑ J ∈ (Finset.univ : Finset (Finset R)).erase ∅,
      (Fintype.card A : ℝ) ^ (Fintype.card F - (J.biUnion support ∪ I).card) *
        ∏ r ∈ J, ((p r)⁻¹ - 1)) ≤
      Fintype.card (Finset R) * (Fintype.card A : ℝ) ^ (Fintype.card F - I.card) *
        (Fintype.card A : ℝ) ^ (-ε) := by
    calc
      _ ≤ ∑ _J ∈ (Finset.univ : Finset (Finset R)).erase ∅,
          (Fintype.card A : ℝ) ^ (Fintype.card F - I.card) * (Fintype.card A : ℝ) ^ (-ε) := by
        apply Finset.sum_le_sum
        intro J hJ
        exact cost_term_bound hn c hc support I J
          (gap J (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hJ).1))
      _ ≤ ∑ _J : Finset R,
          (Fintype.card A : ℝ) ^ (Fintype.card F - I.card) * (Fintype.card A : ℝ) ^ (-ε) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun _ _ _ => by positivity)
      _ = _ := by simp; ring
  calc
    _ ≤ (∏ r, p r) ^ 2 * (Fintype.card A : ℝ) ^ (Fintype.card F - I.card) *
      (Fintype.card (Finset R) * (Fintype.card A : ℝ) ^ (Fintype.card F - I.card) *
        (Fintype.card A : ℝ) ^ (-ε)) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by dsimp [p]; ring

end TableModel
namespace IncidenceTemplate

/-- Source single-copy concentration, also for every singleton-pinned count,
with a common actual-parameter half-unit margin. -/
theorem master_variance_bound {A : Type*} [Fintype A] [Nonempty A] [DecidableEq A]
    {α β δ : ℝ} (ha : 0 ≤ α) (hb : 7 * α ≤ β) (hd : 0 ≤ δ)
    (hsmall : β + 90 * δ ≤ 1 / 2) (I : Finset Field) (hI : I.card ≤ 1) (ξ : Field → A) :
    let N : ℝ := Fintype.card A
    let c := actualRowCost α β δ
    let hp := fun r => TableModel.powerProbability_mem
      (show 1 ≤ N by change (1 : ℝ) ≤ Fintype.card A; exact_mod_cast (show 1 ≤ Fintype.card A from Fintype.card_pos)) (actualRowCost_nonneg ha hb hd r)
    let μ := TableModel.law rowSupport (fun r => N ^ (-c r)) hp
    let X := fun w => (TableModel.candidateCount rowSupport (TableModel.pinCandidates I ξ) w : ℝ)
    μ.variance X ≤ Fintype.card (Finset Row) * N ^ (-(1 / 2 : ℝ)) * μ.expect X ^ 2 := by
  apply TableModel.variance_pinned_power rowSupport (actualRowCost α β δ)
    (actualRowCost_nonneg ha hb hd) I ξ
  intro J hJ
  have hh := actual_pinned_overlap ha hb hd hJ I hI
  linarith

end IncidenceTemplate
end HyperbolicObstruction
end
end

section

end
end

end OAI
