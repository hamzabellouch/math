import OAI.Probability.SATComputability.IncidentObstruction

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped NNReal

noncomputable def clauseAtomRate (n : ℕ) : ℝ≥0 := (8*((n+1 : ℕ) : ℝ≥0)^3)⁻¹

theorem clause_atom_normalization (n : ℕ) :
    clauseAtomRate n * Fintype.card (Fin 3 → SignedLiteral (n+1)) = 1 := by
  have hc : (Fintype.card (Fin 3 → SignedLiteral (n+1)) : ℝ≥0) =
      8*((n+1 : ℕ) : ℝ≥0)^3 := by
    simp only [Fintype.card_fun, SignedLiteral, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_bool, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [hc, clauseAtomRate, inv_mul_cancel₀ (by positivity)]

theorem incident_pair_card (n : ℕ) : Fintype.card (Fin 2 → SignedLiteral n) = 4*n^2 := by
  simp [SignedLiteral, Fintype.card_prod]
  ring

theorem incident_bad_card (n : ℕ) : Fintype.card (BadIncident n) = 6*n+1 := by
  simp [BadIncident, SignedLiteral, Fintype.card_sum, Fintype.card_prod]
  ring

theorem clause_base_rate {n : ℕ} (hn : 0 < n) :
    (1 : ℝ)/8 ≤ (clauseAtomRate n * Fintype.card (Triple (SignedLiteral n)) : ℝ≥0) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ)+1 := by positivity
  have hr : (1 : ℝ)/2 ≤ (n : ℝ)/((n : ℝ)+1) :=
    (le_div_iff₀ hpos).mpr (by linarith)
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1/2) hr 3
  rw [clauseClasses_base_card]
  change (1 : ℝ)/8 ≤ ((clauseAtomRate n : ℝ) * (8*n^3 : ℕ))
  simp only [clauseAtomRate, NNReal.coe_inv, NNReal.coe_mul, NNReal.coe_ofNat,
    NNReal.coe_pow, Nat.cast_add, Nat.cast_one, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_pow]
  push_cast
  convert hp using 1 <;> first | (solve | norm_num) | (solve | field_simp)

theorem incident_single_rate (n : ℕ) :
    3*(((20*(n+1) : ℕ) : ℝ≥0)*clauseAtomRate n)*
      Fintype.card (Fin 2 → SignedLiteral n) ≤ 60 := by
  apply NNReal.coe_le_coe.mp
  rw [incident_pair_card]
  simp only [clauseAtomRate, NNReal.coe_inv, NNReal.coe_mul, NNReal.coe_ofNat,
    NNReal.coe_pow, Nat.cast_add, Nat.cast_one, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_pow]
  push_cast
  have hp : (0 : ℝ) < (n : ℝ)+1 := by positivity
  have he : (3 : ℝ)*(20*((n : ℝ)+1)*(8*((n : ℝ)+1)^3)⁻¹)*(4*(n : ℝ)^2) =
      30*(n : ℝ)^2/((n : ℝ)+1)^2 := by field_simp; ring
  rw [he, div_le_iff₀ (sq_pos_of_pos hp)]
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem incident_bad_rate (n : ℕ) :
    (Fintype.card (BadIncident n) : ℝ)*
      ((((20*(n+1) : ℕ) : ℝ≥0)*clauseAtomRate n) : ℝ) ≤ 60/((n : ℝ)+1) := by
  rw [incident_bad_card]
  simp only [clauseAtomRate, NNReal.coe_inv, NNReal.coe_mul, NNReal.coe_ofNat,
    NNReal.coe_pow, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat]
  push_cast
  have hp : (0 : ℝ) < (n : ℝ)+1 := by positivity
  have he : (6*(n : ℝ)+1)*(20*((n : ℝ)+1)*(8*((n : ℝ)+1)^3)⁻¹) =
      (15*(n : ℝ)+(5/2 : ℝ))/((n : ℝ)+1)^2 := by field_simp; ring
  rw [he, div_le_div_iff₀ (sq_pos_of_pos hp) hp]
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem incident_grid_obstruction {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) :
    (finiteMap (gridMaskLaw (20*(n+1)) (clauseAtomRate n) incidentMask) frontloadMask).expect
      (fun I => if U ∩ I = ∅ then 1 else 0) ≤
      poissonKillProbability U 2 60 + 60/((n : ℝ)+1) := by
  rw [finiteMap_expect, gridMaskLaw_frontload _ _
    (fun I => if U ∩ I = ∅ then 1 else 0)]
  exact (incident_killing_bound _ U).trans
    (add_le_add (poissonKillProbability_mono_rate U 2 (incident_single_rate n))
      (incident_bad_rate n))

theorem incident_restored_uniform_moment {n : ℕ} [NeZero n] (r : ℕ) :
    let M := 20*(n+1)
    let P := gridMaskLaw M (clauseAtomRate n) (incidentMask (n := n))
    let rate := clauseAtomRate n * Fintype.card (Triple (SignedLiteral n))
    P.expect (fun f => P.expect (fun t =>
      (FiniteLaw.pi (fun _ : Fin M => candidateBlock rate 3 Finset.univ)).expect (fun base =>
        (maskLifetime M (deletionBudgetMask n r) base -
          maskLifetime M (deletionBudgetMask (n+1) r)
            (fun j => restoredMask (base j) (f j) (t j)))^(6/5 : ℝ)))) ≤
      deletionMomentConstant := by
  dsimp only
  have h := restored_process_moment (20*(n+1)) r
    (clauseAtomRate n * Fintype.card (Triple (SignedLiteral n)))
    (clause_base_rate (NeZero.pos n))
    (gridMaskLaw (20*(n+1)) (clauseAtomRate n) incidentMask)
    (60/((n : ℝ)+1)) incident_grid_obstruction
  apply h.trans
  unfold deletionMomentConstant
  apply add_le_add le_rfl
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 12/5)
  simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
    capped_incident_error (Nat.succ_pos n)

end FixedClauseThreshold.Computability

end OAI
