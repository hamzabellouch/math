import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.UniformHubbardParameters

namespace OAI

/-! The finite Hubbard approximation uses exact Coulomb target amplitudes;
the negative sign agrees with the manufactured well matrix. Its spatial
implementation can then be approximated entrywise. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem target_hopping_sum_bound {Edge : Type*} [Fintype Edge]
    (freq τ B : ℝ) (hτ : 0 ≤ τ) (distance K : Edge → ℝ)
    (hK : ∀ e, 0 ≤ K e) (hB : ∀ e, K e ≤ B) :
    4 * ∑ e, |coulombHoppingTarget freq τ (K e) (distance e)| ≤
      4 * (Fintype.card Edge : ℝ) * (τ * Real.sqrt (B * localizedCoulombProfile freq 0)) := by
  have hpoint (e : Edge) : |coulombHoppingTarget freq τ (K e) (distance e)| ≤
      τ * Real.sqrt (B * localizedCoulombProfile freq 0) := by
    rw [coulombHoppingTarget, abs_of_nonneg (mul_nonneg hτ (Real.sqrt_nonneg _))]
    apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hτ
    calc
      _ ≤ K e * localizedCoulombProfile freq 0 := mul_le_mul_of_nonneg_left
        (sub_le_self _ (localizedCoulombProfile_nonnegative freq (distance e))) (hK e)
      _ ≤ _ := mul_le_mul_of_nonneg_right (hB e) (localizedCoulombProfile_nonnegative freq 0)
  have h := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (s := Finset.univ) (fun e _ => hpoint e)) (by norm_num : (0 : ℝ) ≤ 4)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc] using h

theorem polynomial_target_hopping_smallness {Edge : Type*} [Fintype Edge]
    {freq N : ℝ} (hN : 2 ≤ N) (R A L E : ℕ)
    (hc : (N ^ L)⁻¹ ≤ localizedGramConstant freq)
    (hU : Real.sqrt (localizedCoulombProfile freq 0) ≤ N ^ L)
    (hr : (Fintype.card Edge : ℝ) ≤ N ^ R) (distance K : Edge → ℝ)
    (hK : ∀ e, 0 ≤ K e) (hKhi : ∀ e, K e ≤ N ^ A) :
    4 * ∑ e, |coulombHoppingTarget freq (N ^ (E + (R + A + 2 * L + 2)))⁻¹ (K e) (distance e)| ≤ (N ^ E)⁻¹ * localizedGramConstant freq := by
  have hNp : 0 < N := by linarith
  have hN₁ : 1 ≤ N := by linarith
  let B := E + (R + A + 2 * L + 2)
  have hτ : 0 ≤ (N ^ B)⁻¹ := inv_nonneg.mpr (pow_nonneg hNp.le B)
  have hsqrt : Real.sqrt (N ^ A * localizedCoulombProfile freq 0) ≤ N ^ (A + L) := by
    rw [Real.sqrt_mul (pow_nonneg hNp.le A), pow_add]
    apply mul_le_mul ?_ hU (Real.sqrt_nonneg _) (pow_nonneg hNp.le A)
    apply Real.sqrt_le_iff.mpr
    have hp : 1 ≤ N ^ A := one_le_pow₀ hN₁
    exact ⟨by positivity, by nlinarith only [hp]⟩
  have hb := target_hopping_sum_bound freq (N ^ B)⁻¹ (N ^ A) hτ distance K hK hKhi
  have hbound : 4 * (Fintype.card Edge : ℝ) * ((N ^ B)⁻¹ *
      Real.sqrt (N ^ A * localizedCoulombProfile freq 0)) ≤ 4 * (N ^ (E + L + 2))⁻¹ := by
    calc
      _ ≤ 4 * N ^ R * ((N ^ B)⁻¹ * N ^ (A + L)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hr (by norm_num))
          (mul_le_mul_of_nonneg_left hsqrt hτ)
          (mul_nonneg hτ (Real.sqrt_nonneg _)) (by positivity)
      _ = 4 * (N ^ (R + (A + L)) * (N ^ B)⁻¹) := by rw [pow_add]; ring
      _ = _ := by
        rw [show B = (R + (A + L)) + (E + L + 2) by dsimp [B]; omega,
          pow_mul_inverse_add hNp]
  have hfour : 4 * (N ^ (E + L + 2))⁻¹ ≤ (N ^ (E + L))⁻¹ := by
    have hsq : (4 : ℝ) ≤ N ^ 2 := by nlinarith
    have h := mul_le_mul_of_nonneg_left hsq (pow_nonneg hNp.le (E + L))
    have hratio : 4 / N ^ (E + L + 2) ≤ 1 / N ^ (E + L) :=
      (div_le_div_iff₀ (pow_pos hNp (E + L + 2)) (pow_pos hNp (E + L))).mpr
        (by simpa only [pow_add, one_mul, mul_one, mul_comm] using h)
    simpa only [div_eq_mul_inv, one_mul] using hratio
  have hlast : (N ^ (E + L))⁻¹ ≤ (N ^ E)⁻¹ * localizedGramConstant freq := by
    have h := mul_le_mul_of_nonneg_left hc (inv_nonneg.mpr (pow_nonneg hNp.le E))
    simpa only [pow_add, mul_inv_rev, mul_comm] using h
  exact hb.trans (hbound.trans (hfour.trans hlast))

theorem exists_uniform_target_hubbard_parameters {freq : ℝ} (hfreq : 0 < freq) (R A g : ℕ) :
    ∃ E B : ℕ, 2 ≤ E ∧ 0 < B ∧ ∀ N : ℝ, 2 ≤ N → ∀ (r : ℕ), (r:ℝ) ≤ N^R →
      ∀ D : ℝ, 5 ≤ D → ∀ (m : ℕ) (u : Fin (m+1) → PlanarPosition),
      (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
      (m+1:ℕ)*localLeakageBound freq D ≤ localDualMass freq/2 →
      ∀ (left right : Fin r → Fin (m+1)) (K : Fin r → ℝ),
      (∀ e, 0 ≤ K e) → (∀ e, K e ≤ N^A) →
      (∀ e, left e ≠ right e) →
      (∀ e f, e ≠ f → ¬(left e=left f ∧ right e=right f) ∧ ¬(left e=right f ∧ right e=left f)) →
      |HubbardGlobal.hubbardFermionBottom m (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u)
        left right (fun e => -coulombHoppingTarget freq (N^B)⁻¹ (K e) ‖u (left e)-u (right e)‖)-
        HubbardGlobal.graphSourceBottom m left right (fun e => ((N^B)⁻¹)^2*K e)| ≤
          (N^g)⁻¹*((N^B)⁻¹)^2 := by
  obtain ⟨L,_,hconstants⟩ := exists_polynomial_constant_bounds (localizedGramConstant_positive hfreq)
    (max (2*localizedGramConstant freq) (Real.sqrt (localizedCoulombProfile freq 0)))
  let C := R+A+2*L+2
  let E := g+2*C+L
  let B := E+C
  have hE : 2 ≤ E := by dsimp [E,C]; omega
  refine ⟨E,B,hE,by dsimp [B,E,C]; omega,?_⟩
  intro N hN r hr D hD m u hsep hleak left right K hK hKhi hloop hsimple
  have hNp : 0 < N := by linarith
  obtain ⟨hc,hupper⟩ := hconstants N hN
  have hc₂ : 2*localizedGramConstant freq ≤ N^L := (le_max_left _ _).trans hupper
  have hU : Real.sqrt (localizedCoulombProfile freq 0) ≤ N^L := (le_max_right _ _).trans hupper
  have ht := polynomial_target_hopping_smallness hN R A L E hc hU (by simpa using hr)
    (fun e => ‖u (left e)-u (right e)‖) K hK hKhi
  have hcal (e : Fin r) :
      (-coulombHoppingTarget freq (N^B)⁻¹ (K e) ‖u (left e)-u (right e)‖)^2 =
      (((N^B)⁻¹)^2*K e)*(localizedCoulombProfile freq 0-localizedCoulombCoeff freq (u (left e)) (u (right e))) := by
    have hg := chargeTransfer_Gram_denominator (localizedCoulombProfile freq 0)
      (localizedGramConstant freq) (localizedOffsiteCoulomb freq u)
      (localizedCoulomb_charge_condition hfreq hD u hsep hleak) (left e) (right e) (hloop e)
      (localizedOffsiteCoulomb_symmetric hfreq u) (localizedOffsiteCoulomb_diagonal freq u)
    simp only [localizedOffsiteCoulomb,ite_eq_right (hloop e)] at hg
    have hn := (localizedGramConstant_positive hfreq).le.trans hg
    rw [localizedCoulombCoeff_distance] at hn ⊢
    rw [neg_sq,coulombHoppingTarget,mul_pow,Real.sq_sqrt (mul_nonneg (hK e) hn)]
    ring
  have he := HubbardGlobal.localized_hubbard_Heisenberg hfreq hD m u hsep hleak left right
    (fun e => -coulombHoppingTarget freq (N^B)⁻¹ (K e) ‖u (left e)-u (right e)‖)
    (fun e => ((N^B)⁻¹)^2*K e) hloop hsimple hcal (by positivity : 0 ≤ (N^E)⁻¹)
    (inverse_power_lt_half hN hE) (by simpa only [abs_neg] using ht)
  exact he.trans (polynomial_hubbard_error_budget hNp R A L g hc₂)

end ContinuumCoulomb

end

end OAI
