import OAI.NumberTheory.TotientAsymptotic.OmegaRemainderLayer
import OAI.NumberTheory.TotientAsymptotic.OmegaDiscardDecay
import OAI.NumberTheory.TotientAsymptotic.NormalInternalDiscard

namespace OAI

/-! Finite layer summation for the remaining-factor exclusion. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def omegaInternalRemainders (x : ℝ) (H : ℕ) : Finset (RemainderDatum (L x H)) :=
  (Finset.Icc 0 (R x H)).biUnion (fun i =>
    (Finset.Icc (collisionLastIndex x i+1) (L x H)).biUnion (omegaExceptionalRemainders x H i))

/-- Sum all exceptional factor-count coordinates after each actual collision cutoff. -/
theorem omega_internal_reciprocal_discard (hbox : FordUnitPrimeBoxInput)
    (hren : FordRenewalInput) (hmertens : MertensProductInput) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
        (∑ η ∈ omegaInternalRemainders x H, remainderReciprocalWeight η) ≤ ε H*G x (m x) := by
  obtain ⟨C,D,hC,hD,hlayer⟩ := omega_remainder_layer_mass hbox hren hmertens
  obtain ⟨E,hE,hcof⟩ := tail_cofactor_sum hmertens
  let ε := fun H => E*Real.exp ((4*(lam/rho))*cofactorScale H)*polynomialGeometricTail 0 rho H
  refine ⟨ε,?_,?_⟩
  · have hh := (cofactor_polynomialGeometricTail_tendsto (4*(lam/rho)) 0 rho_pos.le rho_lt_one).const_mul E
    simpa only [ε,mul_assoc,mul_zero] using hh
  obtain ⟨H₀,hH₀⟩ := eventually_atTop.mp (omega_discard_geometric hC hD)
  filter_upwards [hlayer,ford_band_polynomial_lower 12,eventually_ge_atTop H₀,eventually_ge_atTop 2,eventually_collision_indices,
    P_tendsto.eventually (eventually_ge_atTop 1)]
    with H hL hpoly hH0 hH hind hP
  filter_upwards [hL,hpoly,ford_band_log_upper,m_tendsto.eventually (eventually_ge_atTop H),
    B_tendsto.eventually (eventually_gt_atTop (1 : ℝ))] with x hl hp hlog hHm hB
  let W : ℝ := ∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹
  have hW : 0 ≤ W := Finset.sum_nonneg (fun _ _ => by positivity)
  have hG : 0 ≤ G x (m x) := (G_pos (zero_lt_one.trans hB) _).le
  have hiBound (i : ℕ) (hi : i ∈ Finset.Icc 0 (R x H)) :
      (∑ η ∈ (Finset.Icc (collisionLastIndex x i+1) (L x H)).biUnion (omegaExceptionalRemainders x H i),
        remainderReciprocalWeight η) ≤ W*G x (m x)*rho^(m x-i) := by
    have hiR := (Finset.mem_Icc.mp hi).2
    have him : i < m x := by unfold R at hiR; omega
    have hHi : H ≤ m x-i := by unfold R at hiR; omega
    let h := m x-i
    let b := fordBandScale x i
    let d := fordBandScale x (collisionLastIndex x i)
    let A := C*Real.exp (6*d-b/(2*(h : ℝ)^9)*Real.log (3/2))*(D*(2*b+2))^(L x H-i-1)
    have hb0 : 0 ≤ b := (pow_nonneg (Nat.cast_nonneg (m x-i)) 12).trans (hp i him hHi)
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hbr := fordBandScale_pos (zero_lt_one.trans hB) him
    have hr := (ford_collision_layer_ratio hB him (hind x hHm i hiR).2.1).2
    have hd : d ≤ b/(h : ℝ)^18 := by
      have hh := (div_le_iff₀ hbr).mp hr
      simpa only [d,b,h,one_div,mul_comm,div_eq_mul_inv,one_mul] using hh
    have hk := hH₀ h (hH0.trans hHi) b d (hp i him hHi) (hlog i him) hd
      (L x H-i-1) (by dsimp [h]; unfold L; omega)
    have hk' : (h : ℝ)^2*A ≤ rho^h := by simpa only [A,mul_assoc] using hk
    have hc : ((Finset.Icc (collisionLastIndex x i+1) (L x H)).card : ℝ) ≤ (h : ℝ)^2 := by
      have hcn : (Finset.Icc (collisionLastIndex x i+1) (L x H)).card ≤ h := by
        simp only [Nat.card_Icc]
        dsimp [h]
        unfold L collisionLastIndex
        omega
      have hh : (1 : ℝ) ≤ h := by exact_mod_cast (show 1 ≤ h by dsimp [h]; omega)
      have hcR : ((Finset.Icc (collisionLastIndex x i+1) (L x H)).card : ℝ) ≤ h := by exact_mod_cast hcn
      nlinarith
    calc
      _ ≤ ∑ j ∈ Finset.Icc (collisionLastIndex x i+1) (L x H),
          ∑ η ∈ omegaExceptionalRemainders x H i j, remainderReciprocalWeight η :=
        nonnegative_sum_biUnion_le _ _ _ (fun η => mul_nonneg (by positivity : (0 : ℝ) ≤ (η.cofactor.totient : ℝ)⁻¹) (reciprocalShiftWeight_nonneg η.primes))
      _ ≤ ∑ _j ∈ Finset.Icc (collisionLastIndex x i+1) (L x H), W*G x (m x)*A := by
        apply Finset.sum_le_sum
        intro j hj
        obtain ⟨hj1,hjL⟩ := Finset.mem_Icc.mp hj
        have he := hl i j hiR (by omega) hjL
        simpa only [W,A,b,d,h,mul_assoc] using he
      _ = W*G x (m x)*(((Finset.Icc (collisionLastIndex x i+1) (L x H)).card : ℝ)*A) := by simp; ring
      _ ≤ W*G x (m x)*((h : ℝ)^2*A) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc hA) (mul_nonneg hW hG)
      _ ≤ _ := mul_le_mul_of_nonneg_left hk' (mul_nonneg hW hG)
  have hw : W ≤ E*Real.exp ((4*(lam/rho))*cofactorScale H) := by
    simpa only [W,cofactorScale,mul_assoc] using hcof H
  calc
    _ ≤ ∑ i ∈ Finset.Icc 0 (R x H),
        ∑ η ∈ (Finset.Icc (collisionLastIndex x i+1) (L x H)).biUnion (omegaExceptionalRemainders x H i), remainderReciprocalWeight η :=
      nonnegative_sum_biUnion_le _ _ _ (fun η => mul_nonneg (by positivity : (0 : ℝ) ≤ (η.cofactor.totient : ℝ)⁻¹) (reciprocalShiftWeight_nonneg η.primes))
    _ ≤ ∑ i ∈ Finset.Icc 0 (R x H), W*G x (m x)*rho^(m x-i) := Finset.sum_le_sum hiBound
    _ = W*G x (m x)*(∑ i ∈ Finset.Icc 0 (R x H), rho^(m x-i)) := by rw [Finset.mul_sum]
    _ ≤ (E*Real.exp ((4*(lam/rho))*cofactorScale H))*G x (m x)*polynomialGeometricTail 0 rho H := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right hw hG
      · exact reverse_geometric_sum hHm
      · exact Finset.sum_nonneg (fun _ _ => (pow_pos rho_pos _).le)
      · positivity
    _ = _ := by dsimp [ε]; ring

end TotientAsymptotic

end

end OAI
