import OAI.Combinatorics.PolynomialVacuum.Algebra.NaturalParameters
import OAI.Combinatorics.PolynomialVacuum.Algebra.NaturalUncup

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical

abbrev NatSpectralTensor := (ℕ → ℂ) → SpinTensor ℕ ℂ

def LowerExchange (ψ : NatSpectralTensor) (n : ℕ) : Prop :=
  ∀ j, j+1 < n → ∀ X,
    siteR j (X j) (X (j+1)) (ψ X)=exchangeDenominator (X j) (X (j+1)) • ψ (swapSite j X)

noncomputable def naturalPrescription (ψ : NatSpectralTensor) (n i : ℕ)
    (X : ℕ → ℂ) : SpinTensor ℕ ℂ :=
  ((1+T)*X i*leftFusion i X) •
    (braidTrain (T*X i) X (i+1) (n-i)*cupLinear i) (ψ (skipOne i X))

theorem naturalPrescription_swap_before {ψ : NatSpectralTensor} {n i j : ℕ}
    (hi : i ≤ n) (hji : j+1 < i) (hψ : LowerExchange ψ n) (X : ℕ → ℂ) :
    siteR j (X j) (X (j+1)) (naturalPrescription ψ n i X)=
      exchangeDenominator (X j) (X (j+1)) • naturalPrescription ψ n i (swapSite j X) := by
  have ht : braidTrain (T*X i) (swapSite j X) (i+1) (n-i)=
      braidTrain (T*X i) X (i+1) (n-i) := by
    apply braidTrain_congr
    intro k hk hk'
    exact swapSite_other (by omega) (by omega) X
  have he := hψ j (by omega) (skipOne i X)
  have hj0 : skipOne i X j=X j := by simp [skipOne,show j < i by omega]
  have hj1 : skipOne i X (j+1)=X (j+1) := by simp [skipOne,hji]
  rw [hj0,hj1] at he
  simp only [naturalPrescription,swapSite_other (by omega : i≠j) (by omega : i≠j+1),
    leftFusion_swap_before hji,skipOne_swap_before hji,ht,map_smul]
  have ho : siteR j (X j) (X (j+1)) *
      (braidTrain (T*X i) X (i+1) (n-i)*cupLinear i) =
      (braidTrain (T*X i) X (i+1) (n-i)*cupLinear i)*siteR j (X j) (X (j+1)) := by
    rw [← mul_assoc,braidTrain_far_left _ _ j (i+1) (n-i) (by omega),
      mul_assoc,siteR_cup_before hji,← mul_assoc]
  rw [← Module.End.mul_apply,ho,Module.End.mul_apply,he]
  simp only [map_smul,smul_smul]
  congr 1
  ring

theorem naturalPrescription_swap_after {ψ : NatSpectralTensor} {n i j : ℕ}
    (hij : i < j) (hj : j < n) (hψ : LowerExchange ψ n) (X : ℕ → ℂ) :
    siteR j (X j) (X (j+1)) (naturalPrescription ψ n i X)=
      exchangeDenominator (X j) (X (j+1)) • naturalPrescription ψ n i (swapSite j X) := by
  have he := hψ (j-1) (by omega) (skipOne i X)
  have hj0 : skipOne i X (j-1)=X j := by simp [skipOne,show ¬j-1 < i by omega,show j-1+1=j by omega]
  have hj1 : skipOne i X (j-1+1)=X (j+1) := by simp [skipOne,show ¬j-1+1 < i by omega,show j-1+1+1=j+1 by omega]
  rw [hj0,hj1] at he
  have ht := braidTrain_spectator_swap (T*X i) X (i+1) (j-i-1) (n-j-1)
  have hp : i+1+(j-i-1)=j := by omega
  have hlen : (j-i-1)+(n-j-1+2)=n-i := by omega
  rw [hp,hlen] at ht
  simp only [naturalPrescription,swapSite_other (by omega : i≠j) (by omega : i≠j+1),
    leftFusion_swap_after hij,skipOne_swap_after hij,map_smul]
  have ho : siteR j (X j) (X (j+1)) *
      (braidTrain (T*X i) X (i+1) (n-i)*cupLinear i) =
      (braidTrain (T*X i) (swapSite j X) (i+1) (n-i)*cupLinear i)*siteR (j-1) (X j) (X (j+1)) := by
    rw [← mul_assoc,ht,mul_assoc,siteR_cup_after (by omega : i+2 ≤ j+1),
      show j+1-2=j-1 by omega,← mul_assoc]
  rw [← Module.End.mul_apply,ho,Module.End.mul_apply,he]
  simp only [map_smul,smul_smul]
  congr 1
  ring

theorem naturalPrescription_mark_right {ψ : NatSpectralTensor} {n i : ℕ}
    (hi : i < n) (X : ℕ → ℂ) :
    siteR i (X i) (X (i+1)) (naturalPrescription ψ n i X)=
      exchangeDenominator (X i) (X (i+1)) • naturalPrescription ψ n (i+1) (swapSite i X) := by
  have hlen : n-i=(n-(i+1))+1 := by omega
  have ht : braidTrain (T*X i) (swapSite i X) (i+1+1) (n-(i+1))=
      braidTrain (T*X i) X (i+1+1) (n-(i+1)) := by
    apply braidTrain_congr
    intro k hk hk'
    exact swapSite_other (by omega) (by omega) X
  have ho : siteR i (X i) (X (i+1)) *
      (braidTrain (T*X i) X (i+1) (n-i)*cupLinear i) =
      (exchangeDenominator (X i) (X (i+1))*exchangeDenominator (T*X i) (X (i+1))) •
        (braidTrain (T*X i) X (i+1+1) (n-(i+1))*cupLinear (i+1)) := by
    rw [hlen,braidTrain,← mul_assoc,← mul_assoc,
      braidTrain_far_left _ _ i (i+1+1) (n-(i+1)) (by omega),mul_assoc,mul_assoc]
    rw [← mul_assoc (siteR i _ _) (siteR (i+1) _ _) (cupLinear i),siteR_cup_slide,mul_smul]
    simp only [mul_smul_comm,smul_smul]
  simp only [naturalPrescription,swapSite_right,leftFusion_mark_right,skipOne_mark_right,
    ht,map_smul]
  rw [← Module.End.mul_apply,ho]
  simp only [LinearMap.smul_apply,smul_smul,fusionPair_denominator]
  congr 1
  ring

end PolynomialVacuumAlgebra

end OAI
