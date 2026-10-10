import OAI.NumberTheory.TotientAsymptotic.CofactorPrimePairMass

namespace OAI

/-! A logarithmic endpoint for the cofactor prime-pair sieve. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma floor_log_endpoint {L z : ℝ} (hL : 1 ≤ L) (hz : Real.exp (2*L) ≤ z) :
    2 ≤ ⌊z⌋₊ ∧ L ≤ Real.log (⌊z⌋₊:ℝ) := by
  have he : 2 ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hz0 : 0 ≤ z := (Real.exp_pos _).le.trans hz
  have htwo : 2*Real.exp L ≤ z := by
    have heq : Real.exp (2*L) = (Real.exp L)^2 := by
      rw [show 2*L=L+L by ring,Real.exp_add,pow_two]
    rw [heq] at hz
    nlinarith
  have hf := Nat.lt_floor_add_one z
  have heFloor : Real.exp L ≤ (⌊z⌋₊:ℝ) := by linarith
  have hN : 2 ≤ ⌊z⌋₊ := by exact_mod_cast he.trans heFloor
  refine ⟨hN,?_⟩
  exact (Real.le_log_iff_exp_le (by exact_mod_cast (show 0 < ⌊z⌋₊ by omega))).mpr heFloor

lemma cofactor_sieve_cutoff_mass : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
    Real.exp 2 ≤ x → 0 < B x → 1 ≤ Real.log x/(200*B x) → ∀ Q : Finset ℕ,
    (∀ b ∈ Q,0 < b ∧ (b:ℝ)*Real.exp (Real.log x/(100*B x)) ≤ x) →
    (∑ b ∈ Q,((allShiftedPrimePairs b ⌊x/b⌋₊).card:ℝ)) ≤
      C*x*(B x)^3/(Real.log x)^2*(∑ b ∈ Q,(b:ℝ)⁻¹) := by
  obtain ⟨C,hC,hbound⟩ := cofactor_prime_pair_mass
  refine ⟨40000*C,by positivity,?_⟩
  intro x hx hB hL Q hQ
  let L := Real.log x/(200*B x)
  have hL0 : 0 < L := by dsimp [L]; linarith
  have hQ' : ∀ b ∈ Q,0 < b ∧ (b:ℝ) ≤ x ∧ 2 ≤ ⌊x/b⌋₊ ∧ L ≤ Real.log (⌊x/b⌋₊:ℝ) := by
    intro b hb
    obtain ⟨hb0,hbc⟩ := hQ b hb
    have hbR : (0:ℝ) < b := by exact_mod_cast hb0
    have hcut : Real.exp (2*L) ≤ x/b := by
      apply (le_div_iff₀ hbR).mpr
      rw [show 2*L=Real.log x/(100*B x) by dsimp [L]; ring,mul_comm]
      exact hbc
    have hf := floor_log_endpoint hL hcut
    have hbx : (b:ℝ) ≤ x := by
      have he : 1 ≤ Real.exp (2*L) := Real.one_le_exp (by positivity)
      have hh := mul_le_mul_of_nonneg_left he hbR.le
      have hbc' := (le_div_iff₀ hbR).mp hcut
      nlinarith
    exact ⟨hb0,hbx,hf⟩
  have hh := hbound x L hx hL0 Q hQ'
  have hlog : 0 < Real.log x := by
    have hx0 := (Real.exp_pos 2).trans_le hx
    have ht := (Real.le_log_iff_exp_le hx0).mpr hx
    linarith
  convert hh using 1
  simp only [L]
  field_simp [ne_of_gt hB,ne_of_gt hlog]
  ring

end TotientAsymptotic

end

end OAI
