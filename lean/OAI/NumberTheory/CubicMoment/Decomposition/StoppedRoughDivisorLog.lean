import OAI.NumberTheory.CubicMoment.Decomposition.StoppedRoughDivisorMass
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDivisorLogScale
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDivisorGeometry

namespace OAI

/-! Summed nonempty divisor rows have arbitrary logarithmic savings.
No cancellation is assumed for the empty row in this arithmetic estimate. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stopped_rough_divisor_log (hHuxley : HuxleyAdditiveLargeSieve)
    {κ : ℝ} (hκ : 0 < κ) (k : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (w z l b u M B R : ℝ) (W : ι → ℝ → ℂ)
      (selected : Eisenstein → Eisenstein → Prop) (e : Eisenstein)
      (U H : Finset Eisenstein),
      X^κ ≤ b → b ≤ X → 1 ≤ B → B ≤ b^(3/5:ℝ) → 2 < R →
      2*(Real.log X)^(2*(4*(k+2)+k)) ≤ R →
      (∀ p ∈ U, primaryPrime p) →
      (∀ n ∈ stoppedIntervalSupport ι X l b e,
        ‖stoppedRowCoefficient X w z u W selected n‖ ≤ M) →
      (∀ n ∈ stoppedIntervalSupport ι X l b e,
        stoppedRowCoefficient X w z u W selected n ≠ 0 →
        ∀ p, primaryPrime p → p ∣ n → R ≤ norm p) →
      (∀ v ∈ H, v ≠ 0 ∧ norm v ≤ B ∧ ¬∃ n : Eisenstein, n^3 = v) →
      stoppedDivisorMass X w z l b u W selected e H U ≤
        (∑ v ∈ H, ‖stoppedCharacterSum X w z l b u W selected v e‖^2)+
        K*b^2*B^(1/3:ℝ)*M^2/(Real.log X)^k := by
  obtain ⟨K₁,K₂,hK₁,hK₂,hbound⟩ := stopped_rough_divisor_mass (ι := ι) hHuxley
  obtain ⟨CI,hCI,hcount⟩ := core_dyadic_index_log_count
  obtain ⟨C,hC,hnorm⟩ := log_power_normalization_bound (k+2)
    (show 0 < κ/20000 by positivity)
  let S₂ := ∑' n : Eisenstein, norm n^(-2:ℝ)
  let Sε := ∑' n : Eisenstein, norm n^(-(2-1/20000:ℝ))
  let S₃ := ∑' n : Eisenstein, norm n^(-(3/2:ℝ))
  have hS₂ : 0 ≤ S₂ := tsum_nonneg (fun n => Real.rpow_nonneg (norm_nonneg n) _)
  have hSε : 0 ≤ Sε := tsum_nonneg (fun n => Real.rpow_nonneg (norm_nonneg n) _)
  have hS₃ : 0 ≤ S₃ := tsum_nonneg (fun n => Real.rpow_nonneg (norm_nonneg n) _)
  let K := 104976*S₃+K₁*(S₂+Sε)*(4*CI)*((5832:ℝ)^(1/4:ℝ)+C)+K₂*C+1
  refine ⟨K,by dsimp [K]; positivity,?_⟩
  filter_upwards [stopped_divisor_cutoff_geometry hκ,
    eventually_ge_atTop (Real.exp 1)] with X hgeometry hX
  intro w z l b u M B R W selected e U H hb hbX hB hBb hR hRL hU hcoeff hrough hH
  have hX1 : 1 ≤ X := (Real.one_le_exp_iff.mpr (by norm_num)).trans hX
  have hL1 : 1 ≤ Real.log X := by simpa using Real.log_le_log (Real.exp_pos 1) hX
  have hLp : 0 < Real.log X := zero_lt_one.trans_le hL1
  obtain ⟨hb1,hN,hsize⟩ := hgeometry b B hb hBb
  have hbp : 0 < b := zero_lt_one.trans_le hb1
  have hBX : B ≤ X^2 := by
    apply hBb.trans
    simpa only [Real.rpow_two] using
      (Real.rpow_le_rpow (zero_le_one.trans hb1) hbX (by norm_num : (0:ℝ) ≤ 3/5)).trans
        (Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num : (3/5:ℝ) ≤ 2))
  let V := (Real.log X)^(4*(k+2))
  let I := ((largeCoreDyadicIndices V B).card:ℝ)
  have hI : I ≤ (4*CI)*(Real.log X)^2 := by
    apply (hcount V B X hB hX1 hBX).trans
    calc
      _ ≤ CI*(2*Real.log X)^2 := by gcongr; linarith
      _ = _ := by ring
  have hpower : b^(-(1/20000:ℝ))*(Real.log X)^(k+2) ≤ C :=
    (stopped_length_log_power hX1 hb k).trans (hnorm X hX1)
  have hlargePower : b^(-(1/20:ℝ))*(Real.log X)^k ≤ C := by
    apply le_trans _ hpower
    exact mul_le_mul
      (Real.rpow_le_rpow_of_exponent_le hb1 (by norm_num : -(1/20:ℝ) ≤ -(1/20000)))
      (pow_le_pow_right₀ hL1 (Nat.le_add_right k 2))
      (pow_nonneg hLp.le _) (Real.rpow_nonneg hbp.le _)
  have hlargeScalar : b^(2-1/20:ℝ) ≤ C*b^2/(Real.log X)^k := by
    simpa only [pow_zero,mul_one,Real.rpow_two] using
      (rpow_log_saving hbp hLp k 0 (p := 2) (s := 1/20) (by simpa using hlargePower))
  have hhybrid := stopped_hybrid_weighted_scale hbp hLp
    (show 0 ≤ 4*CI by positivity) k (show 0 ≤ I by dsimp [I]; positivity) hI hpower
    (show S₂ ≤ S₂+Sε by linarith) (show Sε ≤ S₂+Sε by linarith)
    (show 0 ≤ S₂+Sε by positivity)
  have hcut := rough_cutoff_log_saving hLp (4*(k+2)) k hRL
  have hm := hbound X w z l b u M V B R W selected e U H hb1
    (by dsimp [V]; positivity) hB hBb hR hN hsize hU hcoeff hrough hH
  apply hm.trans
  have hs : 104976*V*B^(1/3:ℝ)*b^2*M^2*(R/2)^(-(1/2:ℝ))*S₃ ≤
      (104976*S₃)*b^2*B^(1/3:ℝ)*M^2/(Real.log X)^k := by
    calc
      _ = (104976*S₃*b^2*B^(1/3:ℝ)*M^2)*(V*(R/2)^(-(1/2:ℝ))) := by ring
      _ ≤ (104976*S₃*b^2*B^(1/3:ℝ)*M^2)*(1/(Real.log X)^k) :=
        mul_le_mul_of_nonneg_left hcut (by positivity)
      _ = _ := by ring
  have hh : K₁*I*B^(1/3:ℝ)*M^2*(
      b^2*(V/5832)^(-(1/4:ℝ))*S₂+b^(2-1/20000:ℝ)*Sε) ≤
      (K₁*(S₂+Sε)*(4*CI)*((5832:ℝ)^(1/4:ℝ)+C))*
        b^2*B^(1/3:ℝ)*M^2/(Real.log X)^k := by
    calc
      _ = (K₁*B^(1/3:ℝ)*M^2)*(I*(b^2*(V/5832)^(-(1/4:ℝ))*S₂+
          b^(2-1/20000:ℝ)*Sε)) := by ring
      _ ≤ (K₁*B^(1/3:ℝ)*M^2)*((S₂+Sε)*(4*CI)*
          ((5832:ℝ)^(1/4:ℝ)+C)*b^2/(Real.log X)^k) :=
        mul_le_mul_of_nonneg_left hhybrid (by positivity)
      _ = _ := by ring
  have hl : K₂*B^(1/3:ℝ)*b^(2-1/20:ℝ)*M^2 ≤
      (K₂*C)*b^2*B^(1/3:ℝ)*M^2/(Real.log X)^k := by
    calc
      _ = (K₂*B^(1/3:ℝ)*M^2)*b^(2-1/20:ℝ) := by ring
      _ ≤ (K₂*B^(1/3:ℝ)*M^2)*(C*b^2/(Real.log X)^k) :=
        mul_le_mul_of_nonneg_left hlargeScalar (by positivity)
      _ = _ := by ring
  have he := add_le_add (add_le_add hs hh) hl
  have hn : 0 ≤ b^2*B^(1/3:ℝ)*M^2/(Real.log X)^k := by positivity
  have herror := he.trans_eq (show _ =
      (104976*S₃+K₁*(S₂+Sε)*(4*CI)*((5832:ℝ)^(1/4:ℝ)+C)+K₂*C)*
        b^2*B^(1/3:ℝ)*M^2/(Real.log X)^k by ring)
  have htotal :
      (104976*S₃+K₁*(S₂+Sε)*(4*CI)*((5832:ℝ)^(1/4:ℝ)+C)+K₂*C)*
        b^2*B^(1/3:ℝ)*M^2/(Real.log X)^k ≤
      K*b^2*B^(1/3:ℝ)*M^2/(Real.log X)^k := by
    calc
      _ = (104976*S₃+K₁*(S₂+Sε)*(4*CI)*((5832:ℝ)^(1/4:ℝ)+C)+K₂*C)*
          (b^2*B^(1/3:ℝ)*M^2/(Real.log X)^k) := by ring
      _ ≤ (104976*S₃+K₁*(S₂+Sε)*(4*CI)*((5832:ℝ)^(1/4:ℝ)+C)+K₂*C+1)*
          (b^2*B^(1/3:ℝ)*M^2/(Real.log X)^k) :=
        mul_le_mul_of_nonneg_right (by linarith) hn
      _ = _ := by dsimp [K]; ring
  have hf := add_le_add_left (herror.trans htotal)
    (∑ v ∈ H, ‖stoppedCharacterSum X w z l b u W selected v e‖^2)
  convert hf using 1 <;> ring

end CubicFirstMoment

end

end OAI
