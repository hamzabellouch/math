import OAI.NumberTheory.TotientAsymptotic.SquareCaseSum
import OAI.NumberTheory.TotientAsymptotic.SquareDiscardDecay
import OAI.NumberTheory.TotientAsymptotic.NormalInternalDiscard

namespace OAI

/-! Sum square divisors and both coordinate choices in each positive-index layer. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def squareLayerPrimes (x : ℝ) (i : ℕ) : Finset ℕ :=
  (Nat.primesLE (discardPrimeBound (fordBandScale x i))).filter
    (fun q => collisionSmoothCutoff x i < (q : ℝ))

def squareLayerRemainders (x : ℝ) (H i : ℕ) : Finset (RemainderDatum (L x H)) :=
  (squareLayerPrimes x i).biUnion (fun q =>
    (Finset.Icc i (L x H)).biUnion (fun j =>
      (Finset.Icc i (L x H)).biUnion (fun k => squareRemainderCase x H q j k)))

lemma collision_cutoff_exponent_lower {x : ℝ} {i : ℕ} (hB : 1 < B x)
    (hi : i < m x) (hJ : 2*collisionCutoff (m x-i) < m x-i) :
    fordBandScale x i/(8*((m x-i : ℕ) : ℝ)^20) ≤
      (7/10 : ℝ)*fordBandScale x (collisionLastIndex x i) := by
  have hb := fordBandScale_pos (zero_lt_one.trans hB) hi
  have hh0 : (0 : ℝ) < (m x-i : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hi
  have hd := (le_div_iff₀ hb).mp (ford_collision_layer_ratio hB hi hJ).1
  have hc : (1/8 : ℝ) ≤ (7/20)*rho := by linarith [collision_rho_bounds.1]
  have hm := mul_le_mul_of_nonneg_right hc (div_nonneg hb.le (pow_pos hh0 20).le)
  have hmul := mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 7/10)
  calc
    _ ≤ (7/10 : ℝ)*(rho/(2*((m x-i : ℕ) : ℝ)^20)*fordBandScale x i) := by
      convert hm using 1 <;> ring
    _ ≤ _ := hmul

lemma square_layer_reciprocal_discard (hbox : FordUnitPrimeBoxInput)
    (hren : FordRenewalInput) (hmertens : MertensProductInput) :
    ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop, ∀ i : ℕ, 1 ≤ i → i ≤ R x H →
      (∑ η ∈ squareLayerRemainders x H i, remainderReciprocalWeight η) ≤
      (∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹)*G x (m x)*rho^(m x-i) := by
  obtain ⟨D,hD,hcase⟩ := square_remainder_case_mass hbox hren hmertens
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  obtain ⟨H₀,hH₀⟩ := eventually_atTop.mp (square_discard_geometric
    (C := 8*Real.exp 2) (by positivity) hD0)
  filter_upwards [hcase,ford_band_polynomial_lower 44,eventually_collision_indices,eventually_ge_atTop H₀,
    eventually_ge_atTop 2,P_tendsto.eventually (eventually_ge_atTop 1)]
    with H hc hpoly hind hH0 hH hP
  filter_upwards [hc,hpoly,ford_band_log_upper,m_tendsto.eventually (eventually_ge_atTop H),
    B_tendsto.eventually (eventually_gt_atTop (1 : ℝ))] with x hcases hp hlog hHm hB
  intro i hi hiR
  let h := m x-i
  let b := fordBandScale x i
  let A := 1+Real.log (discardPrimeBound b : ℝ)
  let E := D*(2*b+2)
  let C := (∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹)*G x (m x)
  let I := Finset.Icc i (L x H)
  let Q := squareLayerPrimes x i
  let z := collisionSmoothCutoff x i
  have him : i < m x := by unfold R at hiR; omega
  have hHi : H ≤ h := by dsimp [h]; unfold R at hiR; omega
  have hh0 : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  have hb44 : (h : ℝ)^44 ≤ b := hp i him hHi
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast (show 1 ≤ h by omega)
  have hb1 : (1 : ℝ) ≤ b := (one_le_pow₀ hh1).trans hb44
  have hb2 : (2 : ℝ) ≤ b := by
    have hh2 : (2 : ℝ) ≤ h := by exact_mod_cast hH.trans hHi
    have hp1 : (h : ℝ) ≤ (h : ℝ)^44 := by simpa using pow_le_pow_right₀ hh1 (show 1 ≤ 44 by omega)
    exact hh2.trans (hp1.trans hb44)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hC : 0 ≤ C := mul_nonneg (Finset.sum_nonneg (fun _ _ => by positivity))
    (G_pos (zero_lt_one.trans hB) _).le
  have hA : 0 ≤ A := by
    have hn : (1 : ℝ) ≤ discardPrimeBound b := by exact_mod_cast (show 1 ≤ discardPrimeBound b from (by have := (discardPrimeBound_bounds hb2).1; omega))
    dsimp [A]
    linarith [Real.log_nonneg hn]
  have hI : (I.card : ℝ) ≤ h := by
    have hh : I.card ≤ h := by dsimp [I,h]; simp only [Nat.card_Icc]; unfold L; omega
    exact_mod_cast hh
  have hz1 : 1 ≤ z := by
    dsimp [z,collisionSmoothCutoff]
    exact Real.one_le_exp (Real.exp_pos _).le
  have hqsum : (∑ q ∈ Q, ((q : ℝ)^2)⁻¹) ≤ 2/z :=
    inverse_square_tail Q hz1 (fun q hq => (Finset.mem_filter.mp hq).2)
  have htotal := finite_square_case_sum Q I (squareRemainderCase x H) remainderReciprocalWeight
    (fun η => mul_nonneg (by positivity : (0 : ℝ) ≤ (η.cofactor.totient : ℝ)⁻¹)
      (reciprocalShiftWeight_nonneg η.primes)) hC (sq_nonneg A) (pow_nonneg hE h) hI hz1
    (fun q hq => (Finset.mem_filter.mp hq).2) (by
      intro q hq j hj k hk
      have hqp := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hq).1).2
      simpa only [C,A,E,h,mul_assoc] using hcases i j k q hi hiR
        (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2
        (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2 hqp)
  have hAsmall : 2*A^2 ≤ (8*Real.exp 2)*Real.exp (4*b) := discard_square_log_mass hb2
  have hsmall := hH₀ h (hH0.trans hHi) b ((7/10)*fordBandScale x (collisionLastIndex x i))
    hb44 (hlog i him) (collision_cutoff_exponent_lower hB him (hind x hHm i hiR).2.1)
  calc
    _ ≤ C*((h : ℝ)^2*A^2*E^h)*(2/z) := htotal
    _ = C*((h : ℝ)^2*(2*A^2)*E^h/z) := by ring
    _ ≤ C*((h : ℝ)^2*((8*Real.exp 2)*Real.exp (4*b))*E^h/z) := by gcongr
    _ ≤ C*rho^h := mul_le_mul_of_nonneg_left hsmall hC

end TotientAsymptotic

end

end OAI
