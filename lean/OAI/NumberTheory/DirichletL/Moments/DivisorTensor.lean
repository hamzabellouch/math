import OAI.NumberTheory.DirichletL.Moments.DivisorExtraction

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorTensor
open IdealMobiusDivisorSum CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
open CenteredMomentHeckeExpansion CenteredMomentHeckeHeight CenteredMomentMask HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

def allocationSign (D : Ideal O) (s : Finset ι) (a : Allocation D s) : ℂ :=
  ∏ P : primeSupport D, (-1:ℂ)^((a P).val.card+1)

theorem allocationSign_norm (D : Ideal O) (s : Finset ι) (a : Allocation D s) :
    ‖allocationSign D s a‖=1 := by
  simp only [allocationSign,norm_prod,norm_pow,norm_neg,norm_one,one_pow,Finset.prod_const_one]

theorem allocationTerm_eq_ite (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) :
    allocationTerm D s v a =
      if ∀ i ∈ s, selectedDivisor D s a i∣v i then allocationSign D s a else 0 := by
  by_cases hh : ∀ i ∈ s, selectedDivisor D s a i∣v i
  · rw [ite_eq_left hh]
    unfold allocationTerm allocationSign
    apply Finset.prod_congr rfl
    intro P hP
    have he : (∏ i ∈ (a P).val,if (P:Ideal O)∣v i then (1:ℂ) else 0)=1 := by
      apply Finset.prod_eq_one
      intro i hi
      have his : i ∈ s := (Finset.mem_powerset.mp (Finset.mem_of_mem_erase (a P).property)) hi
      have hPi : (P:Ideal O)∣selectedDivisor D s a i :=
        Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ P,hi⟩)
      rw [ite_eq_left (hPi.trans (hh i his))]
    rw [he,mul_one]
  · rw [ite_eq_right hh]
    by_contra hn
    exact hh (fun i _ => selectedDivisor_dvd D s v a hn i)

theorem allocationTerm_eq_product (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) :
    allocationTerm D s v a = allocationSign D s a*
      ∏ i ∈ s, if selectedDivisor D s a i∣v i then (1:ℂ) else 0 := by
  rw [allocationTerm_eq_ite]
  by_cases hh : ∀ i ∈ s, selectedDivisor D s a i∣v i
  · rw [ite_eq_left hh,Finset.prod_eq_one (fun i hi => by rw [ite_eq_left (hh i hi)]),mul_one]
  · rw [ite_eq_right hh]
    push Not at hh
    obtain ⟨i,hi,hnd⟩ := hh
    rw [Finset.prod_eq_zero hi (by simp only [ite_eq_right hnd]),mul_zero]

theorem selected_plain_sum (η : Character) (m A z : O) (t : ℝ)
    (D : Ideal O) (hD : D ≠ 0) (W : ℝ → ℂ) (X : ℝ) :
    (∑' I : Ideal O, if D∣I then rowWeight η m A z t I*W ((Ideal.absNorm I:ℝ)/X) else 0) =
      rowWeight η m A z t D*rowTwistedSum η m A z W t (X/Ideal.absNorm D) := by
  rw [tsum_ideal_divisible D hD, rowTwistedSum_eq_weight,← tsum_mul_left]
  apply tsum_congr
  intro I
  rw [map_mul]
  have he : (Ideal.absNorm (D*I):ℝ)/X = (Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm D:ℝ)) := by
    simp only [map_mul,Nat.cast_mul,div_div_eq_mul_div]
    ring
  rw [he]
  ring

theorem selected_plain_scales (D₁ D₂ : Ideal O) (X₁ X₂ Y₁ Y₂ T : ℝ)
    (hX : X₁*X₂=T) (hY : Y₁*Y₂=T) :
    (X₁/Ideal.absNorm D₁)*(X₂/Ideal.absNorm D₂)=T/(Ideal.absNorm D₁*Ideal.absNorm D₂:ℝ) ∧
    (Y₁/Ideal.absNorm D₁)*(Y₂/Ideal.absNorm D₂)=T/(Ideal.absNorm D₁*Ideal.absNorm D₂:ℝ) :=
  CenteredMomentExtraction.extracted_product_scale X₁ X₂ Y₁ Y₂ T D₁ D₂ hX hY

end SevenEighths.CenteredMomentDivisorTensor

end

end OAI
