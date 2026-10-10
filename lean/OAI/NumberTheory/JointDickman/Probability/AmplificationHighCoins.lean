import OAI.NumberTheory.JointDickman.Amplification.SubsetPartition
import OAI.NumberTheory.JointDickman.Amplification.AmplificationScaleSum

namespace OAI

/-! # The exact high-prime no-change probability -/

namespace JointDickman

open Finset

noncomputable def highPrimePart (Y : ℝ) (S : Finset ℕ) : Finset ℕ :=
  S.filter (fun p => Y < Real.log p)

open Classical in
noncomputable def highCoinAgreement (Y : ℝ) (S : Finset ℕ) (keep : Bool) : ℝ :=
  ∑ A ∈ S.powerset,
    if A ∩ highPrimePart Y S = (if keep then highPrimePart Y S else ∅) then
      bernoulliSubsetMass S (fun _ => (1 / 2 : ℝ)) A else 0

/-- Fair coins preserve every specified high-prime assignment with this exact probability. -/
theorem highCoinAgreement_eq (Y : ℝ) (S : Finset ℕ) (keep : Bool) :
    highCoinAgreement Y S keep = (1 / 2 : ℝ)^(highPrimePart Y S).card := by
  unfold highCoinAgreement
  rw [bernoulliSubsetMass_projection S (highPrimePart Y S)
    (if keep then highPrimePart Y S else ∅) (filter_subset _ _)
    (by cases keep <;> simp)]
  apply bernoulliSubsetMass_half
  cases keep <;> simp

/-- Four independent sets of fair second coins, for two selected and two
remaining subsets. The high-prime lower cutoffs give the full exponent 1.6 log 2. -/
theorem regular_four_high_coin_bound {B L i : ℕ} {τ C : ℝ} {A D R Q : Finset ℕ}
    (hB : 0 < (B : ℝ)) (hY : 0 < primeTailEndpoint B i)
    (hA : RegularPrimeSet B L τ C A) (hD : RegularPrimeSet B L τ C D)
    (hR : RegularPrimeSet B L τ C R) (hQ : RegularPrimeSet B L τ C Q) :
    highCoinAgreement (primeTailEndpoint B i) A true *
      highCoinAgreement (primeTailEndpoint B i) D true *
      highCoinAgreement (primeTailEndpoint B i) R false *
      highCoinAgreement (primeTailEndpoint B i) Q false ≤
      (2 : ℝ)^(4 * C) * (primeTailEndpoint B i / B)^amplificationExponent := by
  simp_rw [highCoinAgreement_eq, ← pow_add]
  apply four_tail_coin_bound hB hY
  have ha := hA.2 i
  have hd := hD.2 i
  have hr := hR.2 i
  have hq := hQ.2 i
  simp only [Nat.cast_add]
  change 4 * ((2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C) ≤
    (((A.filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)).card : ℝ) +
      ((D.filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)).card : ℝ) +
      ((R.filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)).card : ℝ)) +
      ((Q.filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)).card : ℝ)
  linarith only [ha, hd, hr, hq]

end JointDickman

end OAI
