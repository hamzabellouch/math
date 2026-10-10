import OAI.NumberTheory.Jacobsthal.Estimates.JointModelCount
import OAI.NumberTheory.Jacobsthal.Sieve.OddEulerCorrection

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceMoments
open ErdosRandomVariance
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem jointDensity_nonneg (P S : Finset ℕ) (hP : ∀ t ∈ P,t.Prime) :
    0 ≤ jointDensity P S := by
  apply Finset.prod_nonneg
  intro t ht
  let : NeZero t := ⟨(hP t ht).ne_zero⟩
  exact sub_nonneg.mpr (positionDensity_bounds S t).2

theorem odd_position_density_lower (P S : Finset ℕ) (hP : ∀ t ∈ P,3 ≤ t) (hS : S.card ≤ 2) :
    (1 : ℝ)/2*(sieveProduct P)^2 ≤ jointDensity P S := by
  have hh := ErdosOddEulerCorrection.odd_two_class_product_lower P hP
  apply hh.trans
  apply Finset.prod_le_prod₀
  · intro t ht
    have ht3 : (3 : ℝ) ≤ t := by exact_mod_cast hP t ht
    exact sub_nonneg.mpr ((div_le_one (by linarith)).mpr (by linarith))
  · intro t ht
    let : NeZero t := ⟨by have := hP t ht;omega⟩
    exact sub_le_sub_left (positionDensity_le_two S hS t) 1

theorem nonzero_jointDensity_lower (P S : Finset ℕ) (hP : ∀ t ∈ P,t.Prime)
    (hS : S.card ≤ 2) (hne : jointDensity P S ≠ 0) :
    (1 : ℝ)/2*(sieveProduct P)^2 ≤ jointDensity P S := by
  by_cases h2 : 2 ∈ P
  · have hodd (t : ℕ) (ht : t ∈ P.erase 2) : 3 ≤ t := by
      have hh := Finset.mem_erase.mp ht
      have hp := (hP t hh.2).two_le
      omega
    have hO := odd_position_density_lower (P.erase 2) S hodd hS
    have hO0 := jointDensity_nonneg (P.erase 2) S (fun t ht => hP t (Finset.mem_erase.mp ht).2)
    have hT := nonzero_positionDensity_two P S hS hne h2
    have hK : jointDensity P S = (1-positionDensity S 2)*jointDensity (P.erase 2) S :=
      (Finset.mul_prod_erase P (fun t => 1-positionDensity S t) h2).symm
    have hV : sieveProduct P = (1/2 : ℝ)*sieveProduct (P.erase 2) := by
      rw [sieveProduct,← Finset.mul_prod_erase P (fun t => 1-1/(t : ℝ)) h2]
      norm_num [sieveProduct]
    have hmul := mul_le_mul_of_nonneg_right (show (1 : ℝ)/2 ≤ 1-positionDensity S 2 by linarith) hO0
    rw [hV,hK]
    nlinarith [sq_nonneg (sieveProduct (P.erase 2))]
  · exact odd_position_density_lower P S (fun t ht => by
      have hp := (hP t ht).two_le
      have hn : t ≠ 2 := fun he => h2 (he ▸ ht)
      omega) hS

end ErdosVarianceMoments

end

section

open _root_.Filter
namespace ErdosVarianceUniformMoments
open NumberTheoryLean ErdosVarianceMoments ErdosRandomVariance ErdosInverseEuler
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def densityInverseConstant : ℝ := 8*(Real.exp Real.eulerMascheroniConstant)^2

theorem densityInverseConstant_pos : 0 < densityInverseConstant := by
  dsimp [densityInverseConstant]
  positivity

theorem actual_sieveProduct (w : ℝ) :
    sieveProduct (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) = SmallSieveFinite.smallEuler ⌊w⌋₊ := by
  simp only [sieveProduct,SmallSieveFinite.smallEuler,one_div]

theorem uniform_density_inverse : ∀ᶠ w : ℝ in atTop,2 ≤ w ∧
    ∀ S : Finset ℕ,S.card ≤ 2 → jointDensity (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) S ≠ 0 →
      (jointDensity (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) S)⁻¹ ≤
        densityInverseConstant*(Real.log w)^2 := by
  filter_upwards [smallEuler_log_bounds] with w hw
  refine ⟨hw.1,?_⟩
  intro S hS hne
  let P := LargePrimeDeletion.cutoffPrimes ⌊w⌋₊
  let V := SmallSieveFinite.smallEuler ⌊w⌋₊
  let K := jointDensity P S
  let B := 2*Real.exp Real.eulerMascheroniConstant*Real.log w
  have hP (t : ℕ) (ht : t ∈ P) : t.Prime := (LargePrimeDeletion.mem_cutoffPrimes.mp ht).1
  have hlow := nonzero_jointDensity_lower P S hP hS hne
  rw [actual_sieveProduct] at hlow
  have hV : 0 < V := hw.2.1
  have hVB : 1 ≤ V*B := by
    have hh := mul_le_mul_of_nonneg_left hw.2.2.2 hV.le
    change V*V⁻¹ ≤ V*B at hh
    simpa only [mul_inv_cancel₀ hV.ne'] using hh
  have hsq : (1 : ℝ) ≤ V^2*B^2 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hVB 2
    simpa only [one_pow,mul_pow] using hh
  have hm := mul_le_mul_of_nonneg_right hlow (sq_nonneg B)
  have hKpos : 0 < K := (by dsimp [K,V] at *;positivity : 0 < (1 : ℝ)/2*V^2).trans_le hlow
  have hb : 2*B^2 = densityInverseConstant*(Real.log w)^2 := by
    dsimp [B,densityInverseConstant]
    ring
  have hmain : 1 ≤ (densityInverseConstant*(Real.log w)^2)*K := by
    rw [← hb]
    dsimp [K,V] at *
    nlinarith
  rw [← one_div]
  exact (div_le_iff₀ hKpos).mpr hmain

end ErdosVarianceUniformMoments

end

section

namespace ErdosVarianceMoments
open NumberTheoryLean ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem jointDensity_le_one (P S : Finset ℕ) (hP : ∀ t ∈ P,t.Prime) : jointDensity P S ≤ 1 := by
  apply Finset.prod_le_one₀
  · intro t ht
    let : NeZero t := ⟨(hP t ht).ne_zero⟩
    exact sub_nonneg.mpr (positionDensity_bounds S t).2
  · intro t ht
    let : NeZero t := ⟨(hP t ht).ne_zero⟩
    have hh := (positionDensity_bounds S t).1
    linarith

theorem jointDensity_split (w : ℝ) (H : ℕ) (S : Finset ℕ) :
    jointDensity (divisorPrimes w H) S*jointDensity (coprimePrimes w H) S =
      jointDensity (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) S := by
  unfold jointDensity divisorPrimes coprimePrimes
  exact Finset.prod_filter_mul_prod_filter_not _ _ _

theorem model_normalization_identity (R xi w : ℝ) (H : ℕ) (C0 : ℤ)
    (hR : 0 < R) (hxi : 0 ≤ xi) (hH : 0 < H) :
    atomWeight R xi w H C0*(divisorModulus w H : ℝ)*
      ((coprimeModulus w H).totient : ℝ)*
      (modelLength R xi (H : ℝ) (C0 : ℝ)*((H.totient : ℝ)/(H : ℝ))) = 1 := by
  have hHN : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
  have hphi : (H.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hH).ne'
  have hT0 : (divisorModulus w H : ℝ) ≠ 0 := by exact_mod_cast (divisorModulus_pos w H).ne'
  have hT1 : ((coprimeModulus w H).totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (coprimeModulus_pos w H)).ne'
  have hY : 0 < modelLength R xi (H : ℝ) (C0 : ℝ) := by
    have hHR : (0 : ℝ) < H := by exact_mod_cast hH
    dsimp [modelLength,interceptScale]
    positivity
  unfold atomWeight
  field_simp

end ErdosVarianceMoments

end

end Erdos970

end OAI
