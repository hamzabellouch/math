import OAI.Combinatorics.PolynomialVacuum.Algebra.NaturalCovariance

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical

@[simp] theorem swapSite_swap {α : Type*} (i : ℕ) (X : ℕ → α) :
    swapSite i (swapSite i X)=X := by
  funext k
  simp [swapSite]

theorem leftFusion_mark_left (i : ℕ) (X : ℕ → ℂ) :
    leftFusion (i+1) X=leftFusion i (swapSite i X)*fusionPair (X (i+1)) (X i) := by
  simpa only [swapSite_swap,swapSite_left,swapSite_right] using leftFusion_mark_right i (swapSite i X)

theorem skipOne_mark_left {α : Type*} (i : ℕ) (X : ℕ → α) :
    skipOne i (swapSite i X)=skipOne (i+1) X := by
  simpa only [swapSite_swap] using (skipOne_mark_right i (swapSite i X)).symm

theorem naturalPrescription_mark_left {ψ : NatSpectralTensor} {n i : ℕ}
    (hi : i < n) (X : ℕ → ℂ) :
    siteR i (X i) (X (i+1)) (naturalPrescription ψ n (i+1) X)=
      exchangeDenominator (X i) (X (i+1)) • naturalPrescription ψ n i (swapSite i X) := by
  have hlen : n-i=(n-(i+1))+1 := by omega
  have ht : braidTrain (T*X (i+1)) (swapSite i X) (i+1+1) (n-(i+1))=
      braidTrain (T*X (i+1)) X (i+1+1) (n-(i+1)) := by
    apply braidTrain_congr
    intro k hk hk'
    exact swapSite_other (by omega) (by omega) X
  let B := braidTrain (T*X (i+1)) X (i+1+1) (n-(i+1))
  have ho : exchangeDenominator (T*X (i+1)) (X i) •
      (siteR i (X i) (X (i+1)) * (B*cupLinear (i+1))) =
      exchangeDenominator (X i) (X (i+1)) •
        (B*siteR (i+1) (T*X (i+1)) (X i)*cupLinear i) := by
    rw [← mul_assoc,braidTrain_far_left _ _ i (i+1+1) (n-(i+1)) (by omega),mul_assoc,
      ← mul_smul_comm,siteR_cup_unslide,mul_smul_comm,← mul_assoc]
  have hv := congrArg (fun A : Module.End ℂ (SpinTensor ℕ ℂ) => A (ψ (skipOne (i+1) X))) ho
  simp only [LinearMap.smul_apply,Module.End.mul_apply] at hv
  simp only [naturalPrescription,leftFusion_mark_left,swapSite_left,skipOne_mark_left,
    hlen,braidTrain,swapSite_right,ht,map_smul,fusionPair_denominator]
  change ((1+T)*X (i+1)*(leftFusion i (swapSite i X)*exchangeDenominator (T*X (i+1)) (X i))) •
    siteR i (X i) (X (i+1)) ((B*cupLinear (i+1)) (ψ (skipOne (i+1) X))) = _
  rw [← mul_assoc ((1+T)*X (i+1)) _ _,mul_smul]
  simp only [Module.End.mul_apply]
  rw [hv]
  simp only [smul_smul]
  congr 1
  ring

end PolynomialVacuumAlgebra

end OAI
