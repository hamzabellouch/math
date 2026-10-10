import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.AtomicGapScale

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace Coulomb

lemma screenMass_ge_inverse_cube (δ : ℝ) {a : ℝ} (ha : 0<a) :
    a^(-3:ℝ) ≤ screenMass δ a := by
  rw [Real.rpow_neg ha.le,Real.rpow_ofNat]
  unfold screenMass screenBaseMass
  linarith [le_max_left ((a^3)⁻¹) (1:ℝ), Real.sqrt_nonneg (δ*a)]

lemma source_patch_scale_condition {a P δ : ℝ} (ha : 0<a) (ha1 : a≤1) (hP : 1≤P) :
    a≤(a^(6/5:ℝ))^2*Real.sqrt P*screenMass δ a := by
  have hb : 0≤(a^(6/5:ℝ))^2 := sq_nonneg _
  have hm := screenMass_ge_inverse_cube δ ha
  have hs := Real.one_le_sqrt.mpr hP
  have he : (a^(6/5:ℝ))^2*a^(-3:ℝ)=a^(-3/5:ℝ) := by
    rw [←Real.rpow_mul_natCast ha.le,←Real.rpow_add ha]
    norm_num
  calc
    a = a^(1:ℝ) := (Real.rpow_one _).symm
    _ ≤ a^(-3/5:ℝ) := Real.rpow_le_rpow_of_exponent_ge ha ha1 (by norm_num)
    _ = (a^(6/5:ℝ))^2*1*a^(-3:ℝ) := by rw [mul_one,he]
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hs hb) hm
      (Real.rpow_nonneg ha.le _) (mul_nonneg hb (Real.sqrt_nonneg _))

theorem exists_atomic_small_physical_gap : ∃ s : ℝ, 0<s ∧ s≤1 ∧
    ∀ {J n : ℕ} (S : Nuclei J) (hatom : ∀ i, S.position i=0)
    (ψ : H1Vector n), Antisymmetric ψ → mass ψ=1 →
    ∀ {E δ : ℝ}, (E:EReal)≤unrestrictedFormBottom S → form S ψ≤E+δ → 0≤δ →
    ∀ (y : Space) (hy : y≠0), atomicCellScale y<s → δ≤(atomicCellScale y)^(-349/50:ℝ) →
    ∃ t : ℝ, ∃ ht : t∈Set.Icc (5*atomicCellScale y) (6*atomicCellScale y),
    ∃ T : AtomicBudgetHistory S ψ (thinIMS ψ y t ((atomicCellScale y)^(6/5:ℝ))) 1,
      T.ensemble.totalForm S≤form S ψ+thinIMS ψ y t ((atomicCellScale y)^(6/5:ℝ)) ∧
      T.ensemble.OutFermionic ∧ T.ensemble.CoreSupported {z | t≤‖z-y‖} ∧
      T.ensemble.OutSupported (Metric.closedBall y (t+(atomicCellScale y)^(6/5:ℝ))) ∧
      atomicPatchTFGap S hatom T.ensemble y hy ((atomicCellScale y)^(6/5:ℝ))
        (Real.rpow_pos_of_pos (atomicCellScale_pos hy) _) t ht.2 ≤
        2*(atomicCellScale y)^(-349/50:ℝ) := by
  obtain ⟨s,hs,hs1,hbound⟩ := exists_atomic_refined_small_scale
  refine ⟨s,hs,hs1,?_⟩
  intro J n S hatom ψ hψ hm E δ hE hstate hδ y hy hys hd
  let a := atomicCellScale y
  have ha : 0<a := atomicCellScale_pos hy
  have ha1 : a≤1 := hys.le.trans hs1
  obtain ⟨hsmall,herror⟩ := hbound a ha hys
  obtain ⟨t,ht,T,hT,ho,hcs,hos,hgap⟩ := exists_atomic_physical_gap S hatom ψ hψ hm hE hstate hδ
    hy (Real.rpow_pos_of_pos ha (6/5:ℝ)) hsmall
    (source_patch_scale_condition ha ha1 (screenCountParameter_ge_one ψ δ))
  refine ⟨t,ht,T,hT,ho,hcs,hos,?_⟩
  exact hgap.trans ((atomicRefinedError_small_bound hδ
    (le_trans zero_le_one (screenCountParameter_ge_one ψ δ))
    (screenCountParameter_le_atomicCountConstant S hatom ψ hψ hm hE hstate hδ) ha ha1 hd).trans herror)
end Coulomb
end

end
end

end OAI
