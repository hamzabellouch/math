import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.CellBudgetNormalizationBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric
open scoped BigOperators ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombNeumann

 theorem cell_count_feedback {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 1) {y : Space} (hy : y ≠ 0)
    {e Z lam : ℝ} (he : 0 < e) (he1 : e ≤ 1/8) (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hr : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    let D := max (corePriceExcess Z lam ψ) 0
    let m := localOffsetMass D y
    let P := localCountSupremum ψ D
    rawCountMoment ψ y (localCellRadius y) ≤
      (cellCountLeadingConstant*Real.sqrt e*P+
        cellCountErrorConstant e (packetDirichlet g)*(P^(2/3:ℝ)+Real.sqrt P+1))*m^2 := by
  dsimp only
  let a := localCellRadius y
  let D := max (corePriceExcess Z lam ψ) 0
  let m := localOffsetMass D y
  let P := localCountSupremum ψ D
  have ha : 0 < a := localCellRadius_pos hy
  have hb : 0 < e*a := mul_pos he ha
  have hsep : 6*(2*a)+2*(e*a) ≤ ‖y‖ := by
    have : ‖y‖ = 100000*a := by dsimp [a,localCellRadius]; ring
    nlinarith
  obtain ⟨t,ht,ht0,hgap⟩ := selected_fresh_patch_budget hψ hm y (by positivity : 0 < 2*a) hb
    (by nlinarith : 7*(e*a) < 5*(2*a)) hsep hZ hlam hg hcg hgn hr hgs
  have ht' : t ∈ Icc (10*localCellRadius y) (12*localCellRadius y) := by
    constructor <;> linarith [ht.1,ht.2]
  have hta : 8*a < t-4*(e*a) := by nlinarith [ht.1]
  have hty : t ≤ ‖y‖ := by linarith [ht.2]
  have hba : 3*(e*a) ≤ a := by nlinarith
  obtain ⟨ht0',hO,hM⟩ := cell_fresh_field_mass hψ hm hy he he1 ht' hZ hlam
  have hraw := radial_inner_second_moment_gap hψ y ha ht0 hb hba hta hty hZ hlam hg hcg hgn hr hgs
  dsimp only at hgap hraw hO hM
  rw [←rawCountMoment_eq_integral hψ.sobolevVector y a,hm,mul_one] at hraw
  rw [←rawCountMoment_eq_integral hψ.sobolevVector y (7*(2*a))] at hgap
  have hr14 : 7*(2*a) = 14*a := by ring
  have he4 : 8*(e*a)/(2*a) = 4*e := by field_simp; norm_num
  rw [hr14,he4] at hgap
  simp only [←Real.sqrt_eq_rpow] at hgap
  let B := rawCountMoment ψ y (14*a)
  have hB : 0 ≤ B := rawCountMoment_nonneg _ _ _
  have hBC : B ≤ localCountCoverConstant*P*m^2 :=
    (rawCountMoment_le_of_radius hψ.sobolevVector y y (by
      simp only [sub_self,norm_zero,zero_add]; linarith : ‖y-y‖+14*a ≤ 32*a)).trans
      (enlarged_cell_count_le hψ.sobolevVector (le_max_right _ _) hy)
  have hcap := cell_density_mass_bound ha (by linarith : a ≤ t-4*(e*a)) (localOffsetMass_cube_le D y)
  have hcap0 : 0 ≤ localPatchDensityCap (t-4*(e*a))*((4*a)^3*(Real.pi*4/3)) := by
    have := localPatchDensityCap_nonneg (t-4*(e*a))
    positivity
  have hc2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hcap0 hcap 2) (by norm_num : (0:ℝ) ≤ 2)
  have hex : corePriceExcess Z lam ψ ≤ D := le_max_left _ _
  let p := coreFirstRadialCut y ht0 hb
  let hp := coreFirstRadialCut_partition y ht0 hb
  let G := ∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
    weightedPatchGap (orderedCutForm p hp ψ c) s Z lam y (t-4*(e*a)) hb
      (radialPatchRetention N y t (e*a) c s) u
  let O := freshOutMaximumSecondMoment p hp ψ Z lam
  let M := freshPatchMass p hp ψ Z lam y (t-4*(e*a))
  have hgap' : G ≤ D+(3/2:ℝ)*(Real.pi*smoothTransitionBound/(e*a))^2*Real.sqrt (4*e*B)+
      (e*a)⁻¹^2*neumannRemainderConstant*(B^(2/3:ℝ)+Real.sqrt B)+
      (((2*Real.pi+1)/2)/(e*a))*Real.sqrt B+Real.sqrt O*Real.sqrt (4*e*B)+
      ((packetDirichlet g/2)*(e*a)⁻¹^2)*M := by
    change G ≤ corePriceExcess Z lam ψ+_+_+_+_+_ at hgap
    exact hgap.trans (by gcongr)
  have hscale := cell_budget_algebra ha (localOffsetMass_one_le D y) (localOffsetMass_cube_le D y)
    he (by linarith : e ≤ 1) (localOffsetMass_offset (le_max_right _ _) hy) hB
    (packetDirichlet_nonneg g) (localCountSupremum_one_le ψ D) hBC hO hM
  change rawCountMoment ψ y a ≤ _
  calc _ ≤ 2*(localPatchDensityCap (t-4*(e*a))*((4*a)^3*(Real.pi*4/3)))^2+512*a*G := hraw
       _ ≤ 2*cellDensityMassConstant^2*m^2+512*a*(D+
          (3/2:ℝ)*(Real.pi*smoothTransitionBound/(e*a))^2*Real.sqrt (4*e*B)+
          (e*a)⁻¹^2*neumannRemainderConstant*(B^(2/3:ℝ)+Real.sqrt B)+
          (((2*Real.pi+1)/2)/(e*a))*Real.sqrt B+Real.sqrt O*Real.sqrt (4*e*B)+
          ((packetDirichlet g/2)*(e*a)⁻¹^2)*M) := by
            apply add_le_add (by nlinarith only [hc2]) (mul_le_mul_of_nonneg_left hgap' (by positivity))
       _ ≤ cellCountLeadingConstant*Real.sqrt e*P*m^2+
          cellCountErrorConstant e (packetDirichlet g)*(P^(2/3:ℝ)+Real.sqrt P+1)*m^2 := hscale
       _ = _ := by ring

 theorem cell_supremum_feedback {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 1)
    {e Z lam : ℝ} (he : 0 < e) (he1 : e ≤ 1/8) (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hr : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    let P := localCountSupremum ψ (max (corePriceExcess Z lam ψ) 0)
    P ≤ 1+cellCountLeadingConstant*Real.sqrt e*P+
      cellCountErrorConstant e (packetDirichlet g)*(P^(2/3:ℝ)+Real.sqrt P+1) := by
  dsimp only
  let D := max (corePriceExcess Z lam ψ) 0
  let P := localCountSupremum ψ D
  have hP : 0 ≤ P := le_trans zero_le_one (localCountSupremum_one_le ψ D)
  have hL := cellCountLeadingConstant_pos.le
  have hC := cellCountErrorConstant_nonneg he (packetDirichlet_nonneg g)
  apply localCountSupremum_le
  · have h1 : 0 ≤ cellCountLeadingConstant*Real.sqrt e*P := by positivity
    have h2 : 0 ≤ cellCountErrorConstant e (packetDirichlet g)*(P^(2/3:ℝ)+Real.sqrt P+1) := by positivity
    linarith
  intro y hy
  have hh := cell_count_feedback hψ hm hy he he1 hZ hlam hg hcg hgn hr hgs
  dsimp only at hh
  exact hh.trans (by gcongr; linarith)

end CoulombAtom

end

end OAI
