import Mathlib
import OAI.Analysis.CoulombIonization.Variational.SelectedMasterComparison
import OAI.Analysis.CoulombIonization.RadialBounds.LocalBallTraceBarrier

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SharpLocalPotential_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology

lemma sharpOrdinaryDensityConstant_nonneg : 0 ≤ sharpOrdinaryDensityConstant := by
  have hc := le_trans zero_le_one actualCellMomentConstant_one_le
  have hk := le_trans zero_le_one sharpFreshKineticConstant_one_le
  unfold sharpOrdinaryDensityConstant
  positivity

lemma ordinaryDensity_power_integrable {N : ℕ} {ψ : FormVector N} (hψ : FormAdmissible ψ) :
    Integrable (fun z => (ordinaryDensity ψ z)^(5/3:ℝ)) := by
  have hh := (ordinaryDensity_memLp hψ).integrable_norm_rpow (by norm_num : (5/3:ENNReal) ≠ 0)
    (ENNReal.div_ne_top (by norm_num) (by norm_num) : (5/3:ENNReal) ≠ ⊤)
  simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat,Real.norm_of_nonneg (ordinaryDensity_nonneg ψ _)] using hh

lemma ordinaryDensity_power_ball_mono {N : ℕ} {ψ : FormVector N} (hψ : FormAdmissible ψ)
    (y : Space) {q R : ℝ} (hqR : q ≤ R) :
    (∫ z in ball y q, (ordinaryDensity ψ z)^(5/3:ℝ)) ≤
      ∫ z in ball y R, (ordinaryDensity ψ z)^(5/3:ℝ) := by
  exact setIntegral_mono_set (ordinaryDensity_power_integrable hψ).integrableOn
    (ae_of_all _ (fun z => Real.rpow_nonneg (ordinaryDensity_nonneg ψ z) _))
    (ae_of_all _ (fun _ hz => ball_subset_ball hqR hz))

 theorem sharp_cell_local_potential {N : ℕ} {ψ : FormVector N}
    (hψ : FormAdmissible ψ) {y : Space} (hy : y ≠ 0)
    (ha1 : localCellRadius y ≤ 1) {Z lam q : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    (hq : 0 < q) (hqR : q ≤ 4*localCellRadius y) :
    (∫ x, rawLocalPotential y q x ∂formRawLaw ψ) ≤
      (sharpOrdinaryDensityConstant*(localOffsetMass (max (corePriceExcess Z lam ψ) 0) y)^2/localCellRadius y)^(3/5:ℝ)*
        (8*Real.pi)^(2/5:ℝ)*q^(1/5:ℝ) := by
  apply (ordinaryDensity_raw_local_holder hψ.sobolevFermion.sobolevVector y hq
    ((ordinaryDensity_memLp hψ).restrict _)).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact Real.rpow_le_rpow (setIntegral_nonneg measurableSet_ball
      (fun z _ => Real.rpow_nonneg (ordinaryDensity_nonneg ψ z) _))
    ((ordinaryDensity_power_ball_mono hψ y hqR).trans (sharp_cell_ordinary_density hψ hy ha1 hZ hlam))
    (by norm_num)

 theorem unshifted_cell_ordinary_density (Z : ℕ) {N : ℕ} {ψ : FormVector N}
    (hψ : FormAdmissible ψ) {D : ℝ} (hD : 0 ≤ D)
    (he : formEnergy Z ψ ≤ sInf (Set.range (energy (Z:ℝ)))+D)
    {y : Space} (hy : y ≠ 0) (ha1 : localCellRadius y ≤ 1) :
    (∫ z in ball y (4*localCellRadius y), (ordinaryDensity ψ z)^(5/3:ℝ)) ≤
      sharpOrdinaryDensityConstant*(localOffsetMass D y)^2/localCellRadius y := by
  have ha := localCellRadius_pos hy
  have hC := sharpOrdinaryDensityConstant_nonneg
  have hm : formMass ψ = 1 := hψ.2.2.2.2.1
  have hh (lam : ℝ) (hlam : 0 < lam) :
      (∫ z in ball y (4*localCellRadius y), (ordinaryDensity ψ z)^(5/3:ℝ)) ≤
        sharpOrdinaryDensityConstant*(localOffsetMass (D+lam*N) y)^2/localCellRadius y := by
    have hex := unshifted_priced_excess_bound Z hm hlam he
    have hm' := localOffsetMass_mono (max_le hex (by positivity : 0 ≤ D+lam*N)) y
    have hsq := pow_le_pow_left₀ (le_trans zero_le_one (localOffsetMass_one_le _ _)) hm' 2
    exact (sharp_cell_ordinary_density hψ hy ha1 (Nat.cast_nonneg Z) hlam).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hC) ha.le)
  let eps (n : ℕ) : ℝ := 1/((n:ℝ)+1)
  have hp (n : ℕ) : 0 < eps n := by dsimp [eps]; positivity
  have ht : Tendsto eps atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hc : Continuous (fun t : ℝ => sharpOrdinaryDensityConstant*(localOffsetMass (D+t*N) y)^2/localCellRadius y) := by
    unfold localOffsetMass
    fun_prop
  have ht' : Tendsto (fun n => sharpOrdinaryDensityConstant*(localOffsetMass (D+eps n*N) y)^2/localCellRadius y)
      atTop (𝓝 (sharpOrdinaryDensityConstant*(localOffsetMass D y)^2/localCellRadius y)) := by
    simpa only [Function.comp_def,zero_mul,add_zero] using hc.continuousAt.tendsto.comp ht
  exact ge_of_tendsto ht' (Eventually.of_forall (fun n => hh (eps n) (hp n)))

end Work_SharpLocalPotential_barrier_scope

open MeasureTheory Set Metric
open scoped BigOperators

open CoulombAnalysis CoulombNeumann

 theorem sharp_selected_patch_energy {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 1) {y : Space} (hy : y ≠ 0)
    {b Z lam r : ℝ} (hb : 0 < b) (hba : 7*b < 5*localCellRadius y)
    (hr : r ∈ Icc (5*localCellRadius y) (6*localCellRadius y)) (hr0 : 0 ≤ r)
    (hZ : 0 ≤ Z) (hlam : 0 < lam)
    (hcollar : localCellRadius y ≤ b^2*localOffsetMass (max (corePriceExcess Z lam ψ) 0) y) :
    selectedPatchEnergyError ψ y (localCellRadius y) hr0 hb Z lam canonicalRealPacket ≤
      corePriceExcess Z lam ψ+sharpPatchRemainder (localCellRadius y) b
        (localOffsetMass (max (corePriceExcess Z lam ψ) 0) y) := by
  let a := localCellRadius y
  let D := max (corePriceExcess Z lam ψ) 0
  let m := localOffsetMass D y
  let B := rawCountMoment ψ y (7*a)
  have ha : 0 < a := localCellRadius_pos hy
  have hba' : b ≤ a := by linarith
  obtain ⟨hr0',hfield,hmass⟩ := sharp_cell_fresh_field_mass hψ hm hy hb hba' hr hZ hlam hcollar
  have hBC : B ≤ actualCellMomentConstant*m^2 :=
    (rawCountMoment_le_of_radius hψ.sobolevVector y y (by simp only [sub_self,norm_zero,zero_add]; linarith : ‖y-y‖+7*a ≤ 32*a)).trans
      (priced_enlarged_cell_count hψ hm hZ hlam hy)
  have hB : 0 ≤ B := rawCountMoment_nonneg ψ y (7*a)
  have hC := actualCellMomentConstant_one_le
  have hC0 := le_trans zero_le_one hC
  have hm0 : 0 ≤ m := le_trans zero_le_one (localOffsetMass_one_le D y)
  have hroot : Real.sqrt B ≤ actualCellMomentConstant*m := by
    simpa using sqrt_count_scale hB hC (by norm_num : (0:ℝ) ≤ 1) hm0 (by simpa using hBC)
  have htwo := count_two_thirds_scale hB hC0 hm0 hBC
  have hsqrt : Real.sqrt ((8*b/a)*B) ≤ Real.sqrt (8*b/a)*actualCellMomentConstant*m := by
    rw [Real.sqrt_mul (show 0 ≤ 8*b/a by positivity)]
    exact (mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg _)).trans_eq (by ring)
  have hF0 : 0 ≤ sharpFreshFieldConstant*(m/a) := by
    have := sharpFreshFieldConstant_one_le
    positivity
  have hfieldroot : Real.sqrt (freshOutMaximumSecondMoment (coreFirstRadialCut y hr0 hb)
      (coreFirstRadialCut_partition y hr0 hb) ψ Z lam) ≤ sharpFreshFieldConstant*(m/a) :=
    Real.sqrt_le_iff.mpr ⟨hF0,hfield⟩
  have hims : (3/2:ℝ)*(Real.pi*smoothTransitionBound/b)^2 = localizationIMSConstant/b^2 := by
    unfold localizationIMSConstant
    ring
  unfold selectedPatchEnergyError
  dsimp only
  rw [←rawCountMoment_eq_integral hψ.sobolevVector y (7*a)]
  simp only [←Real.sqrt_eq_rpow,hims]
  have hI := localizationIMSConstant_nonneg
  have hN := neumannRemainderConstant_pos.le
  have hP := packetDirichlet_nonneg canonicalRealPacket
  change _ ≤ corePriceExcess Z lam ψ+sharpPatchRemainder a b m
  unfold sharpPatchRemainder
  simp only [←add_assoc]
  gcongr

 def sharpLocalPotentialBudget (a m u : ℝ) : ℝ :=
    (sharpOrdinaryDensityConstant*m^2/a)^(3/5:ℝ)*(8*Real.pi)^(2/5:ℝ)*u^(1/5:ℝ)

 def sharpPotentialRemainder (a b m D q : ℝ) : ℝ :=
    Real.sqrt ((2/q)*(D+sharpPatchRemainder a b m))+
    sharpLocalPotentialBudget a m (q+Real.sqrt 3*b)+
    2*Real.pi*tfPatchDensityCapConstant*q^2/a^6+
    sharpLocalPotentialBudget a m (Real.sqrt 3*b)+
    (Real.sqrt (8*b/a)*actualCellMomentConstant*m)/a

 theorem sharp_selected_potential_error {N : ℕ} {ψ : FormVector N}
    (hψ : FormAdmissible ψ) {y : Space} (hy : y ≠ 0) (ha1 : localCellRadius y ≤ 1)
    {b Z lam r q : ℝ} (hb : 0 < b) (hba : 2*b ≤ localCellRadius y)
    (hr : r ∈ Icc (5*localCellRadius y) (6*localCellRadius y)) (hr0 : 0 ≤ r)
    (hZ : 0 ≤ Z) (hlam : 0 < lam) (hq : 0 < q)
    (hqr : q+Real.sqrt 3*b ≤ 4*localCellRadius y)
    (hcollar : localCellRadius y ≤ b^2*localOffsetMass (max (corePriceExcess Z lam ψ) 0) y) :
    selectedPotentialError ψ y (localCellRadius y) hr0 hb Z lam q canonicalRealPacket ≤
      sharpPotentialRemainder (localCellRadius y) b
        (localOffsetMass (max (corePriceExcess Z lam ψ) 0) y) (max (corePriceExcess Z lam ψ) 0) q := by
  let a := localCellRadius y
  let D := max (corePriceExcess Z lam ψ) 0
  let m := localOffsetMass D y
  let B := rawCountMoment ψ y (7*a)
  have ha : 0 < a := localCellRadius_pos hy
  have hm : formMass ψ = 1 := hψ.2.2.2.2.1
  have hsf := hψ.sobolevFermion
  have h7 : 7*b < 5*a := by linarith
  have hE := sharp_selected_patch_energy hsf hm hy hb h7 hr hr0 hZ hlam hcollar
  have hE' : selectedPatchEnergyError ψ y a hr0 hb Z lam canonicalRealPacket ≤
      D+sharpPatchRemainder a b m := hE.trans (add_le_add (le_max_left _ _) le_rfl)
  have hq3 : 0 < q+Real.sqrt 3*b := by positivity
  have hb3 : 0 < Real.sqrt 3*b := by positivity
  have hqB := sharp_cell_local_potential hψ hy ha1 hZ hlam hq3 hqr
  have hbB := sharp_cell_local_potential hψ hy ha1 hZ hlam hb3 (by linarith : Real.sqrt 3*b ≤ 4*a)
  have hBC : B ≤ actualCellMomentConstant*m^2 :=
    (rawCountMoment_le_of_radius hsf.sobolevVector y y
      (by simp only [sub_self,norm_zero,zero_add]; linarith : ‖y-y‖+7*a ≤ 32*a)).trans
      (priced_enlarged_cell_count hsf hm hZ hlam hy)
  have hB : 0 ≤ B := rawCountMoment_nonneg ψ y (7*a)
  have hm0 : 0 ≤ m := le_trans zero_le_one (localOffsetMass_one_le D y)
  have hC := actualCellMomentConstant_one_le
  have hroot : Real.sqrt B ≤ actualCellMomentConstant*m := by
    simpa using sqrt_count_scale hB hC (by norm_num : (0:ℝ) ≤ 1) hm0 (by simpa using hBC)
  have hsqrt : Real.sqrt ((8*b/a)*B) ≤ Real.sqrt (8*b/a)*actualCellMomentConstant*m := by
    rw [Real.sqrt_mul (show 0 ≤ 8*b/a by positivity)]
    exact (mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg _)).trans_eq (by ring)
  have ht7 : a ≤ r-7*b := by linarith [hr.1]
  have ht4 : a ≤ r-4*b := by linarith [hr.1]
  have hcap : 0 ≤ 2*Real.pi*tfPatchDensityCapConstant*q^2 := by
    have := tfPatchDensityCapConstant_pos
    positivity
  have hcap' : 2*Real.pi*tfPatchDensityCapConstant*q^2/(r-4*b)^6 ≤
      2*Real.pi*tfPatchDensityCapConstant*q^2/a^6 := by gcongr
  have hdel : Real.sqrt ((8*b/a)*B)/(r-7*b) ≤
      (Real.sqrt (8*b/a)*actualCellMomentConstant*m)/a := by gcongr
  change _ ≤ sharpPotentialRemainder a b m D q
  unfold selectedPotentialError sharpPotentialRemainder
  rw [←rawCountMoment_eq_integral hsf.sobolevVector y (7*a)]
  exact add_le_add (add_le_add (add_le_add (add_le_add
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hE' (by positivity))) hqB) hcap') hbB) hdel

end CoulombAtom

end

end OAI
