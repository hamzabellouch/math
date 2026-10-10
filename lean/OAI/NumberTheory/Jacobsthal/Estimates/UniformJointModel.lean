import OAI.NumberTheory.Jacobsthal.Probability.MomentIndicators

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter
namespace ErdosUniformMobiusRemainder

def cutoffExponent (M : ℝ) : ℝ := 2*M+12

theorem cutoffExponent_margin (M : ℝ) : 2*M+10 < cutoffExponent M := by
  dsimp [cutoffExponent]
  linarith

theorem source_sqrt_lower (M xi W Y : ℝ) (hxi : 0 < xi) (hW : 0 < W)
    (hY : xi*W^(cutoffExponent M) ≤ Y) :
    xi^((1 : ℝ)/2)*W^(M+6) ≤ Y^((1 : ℝ)/2) := by
  have hp := Real.rpow_le_rpow (show 0 ≤ xi*W^(cutoffExponent M) by positivity) hY
    (by norm_num : (0 : ℝ) ≤ 1/2)
  rw [Real.mul_rpow hxi.le (Real.rpow_nonneg hW.le _) ,← Real.rpow_mul hW.le] at hp
  have he : cutoffExponent M*((1 : ℝ)/2)=M+6 := by dsimp [cutoffExponent];ring
  rwa [he] at hp

theorem remainder_scalar_bound (C A M xi W : ℝ) (H : ℕ) (Y : ℝ)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hxi : 0 < xi) (hW : 0 < W)
    (hH : 1 ≤ H) (hHY : (H : ℝ) ≤ Y) (hYscale : xi*W^(cutoffExponent M) ≤ Y)
    (hdiv : (H.divisors.card : ℝ)*(H : ℝ)/(Y*(H.totient : ℝ)) ≤ C/Y^((1 : ℝ)/2)) :
    A*(H.divisors.card : ℝ)*(H : ℝ)/(Y*(H.totient : ℝ))*W^M*(Real.log W)^2 ≤
      (A*C/xi^((1 : ℝ)/2))*((Real.log W)^2/W^(6 : ℝ)) := by
  have hY : 0 < Y := (show (0 : ℝ) < H by exact_mod_cast hH).trans_le hHY
  have hroot := source_sqrt_lower M xi W Y hxi hW hYscale
  have hbase : A*(H.divisors.card : ℝ)*(H : ℝ)/(Y*(H.totient : ℝ)) ≤
      A*C/(xi^((1 : ℝ)/2)*W^(M+6)) := by
    calc
      _ = A*((H.divisors.card : ℝ)*(H : ℝ)/(Y*(H.totient : ℝ))) := by ring
      _ ≤ A*(C/Y^((1 : ℝ)/2)) := mul_le_mul_of_nonneg_left hdiv hA
      _ = A*C/Y^((1 : ℝ)/2) := by ring
      _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hA hC) (by positivity) hroot
  have hf : W^(M+6)=W^M*W^(6 : ℝ) := by rw [Real.rpow_add hW]
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hbase (Real.rpow_nonneg hW.le M)) (sq_nonneg (Real.log W))
  have he : (A*C/(xi^((1 : ℝ)/2)*W^(M+6)))*W^M*(Real.log W)^2 =
      (A*C/xi^((1 : ℝ)/2))*((Real.log W)^2/W^(6 : ℝ)) := by
    rw [hf]
    field_simp
  exact hmul.trans_eq he

theorem uniform_mobius_remainder (M : ℝ) (_hM : 0 ≤ M) :
    ∃ Cs : ℝ,2*M+10 < Cs ∧ ∀ xi : ℝ,0 < xi → ∀ A : ℝ,0 ≤ A →
      ∀ eps : ℝ,0 < eps → ∀ᶠ W : ℝ in atTop,1 < W ∧
        ∀ (H : ℕ) (Y : ℝ),1 ≤ H → (H : ℝ) ≤ Y → xi*W^Cs ≤ Y →
          A*(H.divisors.card : ℝ)*(H : ℝ)/(Y*(H.totient : ℝ))*W^M*(Real.log W)^2 ≤ eps := by
  obtain ⟨C,hC,hbound⟩ := divisor_totient_length_bound
  refine ⟨cutoffExponent M,cutoffExponent_margin M,?_⟩
  intro xi hxi A hA eps heps
  by_cases hA0 : A=0
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with W hW
    refine ⟨hW,?_⟩
    intro H Y _ _ _
    simpa only [hA0,zero_mul,zero_div] using heps.le
  have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
  let K := A*C/xi^((1 : ℝ)/2)
  have hK : 0 < K := by dsimp [K]; positivity
  have hlittle := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 6)).bound (div_pos heps hK)
  filter_upwards [hlittle,eventually_gt_atTop (1 : ℝ)] with W hlog hW
  refine ⟨hW,?_⟩
  intro H Y hH hHY hYscale
  have hW0 : 0 < W := by linarith
  have hlog' : (Real.log W)^2 ≤ (eps/K)*W^(6 : ℝ) := by
    simpa only [Real.rpow_two,Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (Real.log W)),abs_of_nonneg (Real.rpow_nonneg hW0.le (6 : ℝ))] using hlog
  have hsmall : K*((Real.log W)^2/W^(6 : ℝ)) ≤ eps := by
    have hh := (div_le_iff₀ (Real.rpow_pos_of_pos hW0 (6 : ℝ))).mpr hlog'
    have hm := mul_le_mul_of_nonneg_left hh hK.le
    have he : K*(eps/K)=eps := by field_simp
    exact hm.trans_eq he
  exact (remainder_scalar_bound C A M xi W H Y hC.le hA hxi hW0 hH hHY hYscale
    (hbound H Y hH hHY)).trans hsmall

end ErdosUniformMobiusRemainder

end


namespace ErdosVarianceUniformMoments
open NumberTheoryLean ErdosVarianceMoments ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem zero_joint_model_mass (R xi w : ℝ) (H qA : ℕ) (C0 : ℤ)
    (hC0 : Int.gcd C0 (H : ℤ) = 1) (beta delta : ∀ t : ℕ,ZMod t)
    (hqA : ∀ t ∈ coprimePrimes w H,qA.Coprime t) (S : Finset ℕ)
    (hz : jointDensity (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) S = 0) :
    modelMass R xi w H C0 (jointCondition w H C0 qA beta delta S) = 0 := by
  have hmul : jointDensity (divisorPrimes w H) S*jointDensity (coprimePrimes w H) S = 0 :=
    (jointDensity_split w H S).trans hz
  rw [joint_model_mass R xi w H qA C0 beta delta S hC0]
  rcases mul_eq_zero.mp hmul with h0|h1
  · rw [h0,mul_zero,mul_zero,zero_mul]
  · have hf (p : (ZMod (coprimeModulus w H))ˣ) :
        coprimePositionSurvivors w H qA delta S p (modelLeft R xi (C0 : ℝ))
          (modelRight R xi (H : ℝ) (C0 : ℝ)) = ∅ :=
      zero_coprimePositionSurvivors w H qA delta S p hqA h1 _ _
    simp only [hf,Finset.card_empty,Nat.cast_zero,Finset.sum_const_zero,mul_zero]

end ErdosVarianceUniformMoments



open _root_.Filter
namespace ErdosVarianceUniformMoments
open NumberTheoryLean ErdosVarianceMoments ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem uniform_joint_model_relative (zeta : ℝ) (hzeta : 0 < zeta) :
    ∃ Cs : ℝ,0 < Cs ∧ ∀ xi : ℝ,0 < xi → ∀ᶠ w : ℝ in atTop,2 ≤ w ∧
      ∀ (R : ℝ),0 < R → ∀ (H qA : ℕ),0 < H → ∀ (C0 : ℤ),Int.gcd C0 (H : ℤ) = 1 →
        ∀ (beta delta : ∀ t : ℕ,ZMod t),
        (∀ t ∈ coprimePrimes w H,qA.Coprime t) →
        xi*w^Cs ≤ modelLength R xi (H : ℝ) (C0 : ℝ) →
        ∀ S : Finset ℕ,S.card ≤ 2 →
          |modelMass R xi w H C0 (jointCondition w H C0 qA beta delta S)-
            jointDensity (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) S| ≤
              zeta*jointDensity (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) S := by
  let s := max 480024 (-96*Real.log (zeta/2))
  have hs : 480024 ≤ s := le_max_left _ _
  have hs0 : 0 ≤ s := by linarith
  have hexp : Real.exp (-s/96) ≤ zeta/2 := by
    have hsecond : -96*Real.log (zeta/2) ≤ s := le_max_right _ _
    calc
      _ ≤ Real.exp (Real.log (zeta/2)) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := Real.exp_log (by positivity)
  obtain ⟨Cs,hCs,hrem⟩ := ErdosUniformMobiusRemainder.uniform_mobius_remainder (2*s) (by positivity)
  refine ⟨Cs,by linarith,?_⟩
  intro xi hxi
  have hA : 0 ≤ 4*densityInverseConstant := mul_nonneg (by norm_num) densityInverseConstant_pos.le
  filter_upwards [uniform_density_inverse,hrem xi hxi (4*densityInverseConstant) hA (zeta/2) (by positivity)]
    with w hden hremw
  refine ⟨hden.1,?_⟩
  intro R hR H qA hH C0 hC0 beta delta hqA hscale S hS
  let K := jointDensity (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) S
  change |modelMass R xi w H C0 (jointCondition w H C0 qA beta delta S)-K| ≤ zeta*K
  by_cases hzero : K = 0
  · have hm := zero_joint_model_mass R xi w H qA C0 hC0 beta delta hqA S hzero
    simp only [hm,hzero,sub_zero,abs_zero,mul_zero,le_refl]
  have hP (t : ℕ) (ht : t ∈ LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) : t.Prime :=
    (LargePrimeDeletion.mem_cutoffPrimes.mp ht).1
  have hK : 0 < K := lt_of_le_of_ne (jointDensity_nonneg _ S hP) (Ne.symm hzero)
  let Y := modelLength R xi (H : ℝ) (C0 : ℝ)
  let E := 4*(H.divisors.card : ℝ)*(H : ℝ)/(Y*(H.totient : ℝ))*(w^s)^2
  have hW : 0 < w := by linarith [hden.1]
  have hYH : (H : ℝ) ≤ Y := by
    dsimp [Y,modelLength,interceptScale]
    exact le_add_of_nonneg_right (by positivity)
  have hY : 0 < Y := (show (0 : ℝ) < H by exact_mod_cast hH).trans_le hYH
  have hE : 0 ≤ E := by dsimp [E];positivity
  have hbudget := hremw.2 H Y hH hYH hscale
  have hp : (w^s)^2 = w^(2*s) := by
    rw [← Real.rpow_two,← Real.rpow_mul hW.le]
    congr 1
    ring
  have hbudget' : E*(densityInverseConstant*(Real.log w)^2) ≤ zeta/2 := by
    have he : E*(densityInverseConstant*(Real.log w)^2) =
      (4*densityInverseConstant)*(H.divisors.card : ℝ)*(H : ℝ)/(Y*(H.totient : ℝ))*
        w^(2*s)*(Real.log w)^2 := by dsimp [E];rw [hp];ring
    exact he.trans_le hbudget
  have hinv : E/K ≤ zeta/2 := by
    calc
      E/K = E*K⁻¹ := div_eq_mul_inv _ _
      _ ≤ E*(densityInverseConstant*(Real.log w)^2) :=
        mul_le_mul_of_nonneg_left (hden.2 S hS hzero) hE
      _ ≤ _ := hbudget'
  have hEbound : E ≤ (zeta/2)*K := (div_le_iff₀ hK).mp hinv
  have hf := finite_joint_moment_estimate R xi w hR hxi.le hden.1 s hs H qA hH C0 hC0 beta delta hqA S hS
  have heterm := mul_le_mul_of_nonneg_left hexp hK.le
  change K*Real.exp (-s/96) ≤ K*(zeta/2) at heterm
  change |modelMass R xi w H C0 (jointCondition w H C0 qA beta delta S)-K| ≤ K*Real.exp (-s/96)+E at hf
  change |modelMass R xi w H C0 (jointCondition w H C0 qA beta delta S)-K| ≤ zeta*K
  linarith

end ErdosVarianceUniformMoments


end Erdos970

end OAI
