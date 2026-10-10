import Mathlib
import OAI.Analysis.CoulombIonization.Ionization.SharpJointComparisonBarrier

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_ExpectedRadialCap_barrier_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

open CoulombAnalysis

theorem expectedRadialPatchCenter_le {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (hbt : 4*b < t) (hy : t ≤ ‖y‖) (Z lam : ℝ) :
    expectedRadialPatchCenter ψ y ht hb Z lam ≤
      (tfPatchCapConstant/(t-4*b)^4)*formMass ψ := by
  let p := coreFirstRadialCut y ht hb
  let hp := coreFirstRadialCut_partition y ht hb
  let χ := fun c : Fin N → Fin 2 => orderedCutForm p hp ψ c
  have hR : 0 < t-4*b := by linarith
  have hχ (c : Fin N → Fin 2) : SobolevVector (χ c) := orderedCutForm_sobolev p hp hψ c
  have hcore (c : Fin N → Fin 2) (s : Spins (cutOutNumber c))
      (u : Configuration (cutOutNumber c)) (v : Configuration (cutCoreNumber c))
      (i : Fin (cutCoreNumber c)) (hi : v i ∉ radialPatchCore y t) :
      FormZeroAt (coreSlice (χ c) s u) v := by
    apply FormZeroAt.coreSlice
    exact orderedCutForm_core_hole _ _ ψ c (radialPatchCore y t)ᶜ
      (coreFirstRadialCut_core_zero y ht hb) (coreFirstRadialCut_core_deriv_zero y ht hb)
      (joinLists v u) i (by simpa only [joinLists_left,mem_compl_iff] using hi)
  have hi (c : Fin N → Fin 2) (s : Spins (cutOutNumber c)) :=
    weightedPatchCenter_integrable (hχ c) s y hR Z lam hb (radialPatchCore y t)
      (hcore c s) (radialPatch_nuclear_distance hb hy) (radialPatch_core_distance y hb)
  have hbnd (c : Fin N → Fin 2) (s : Spins (cutOutNumber c)) :
      (∫ u, weightedPatchCenter (χ c) s Z lam y (t-4*b) u) ≤
        (tfPatchCapConstant/(t-4*b)^4)*(∫ u, formMass (coreSlice (χ c) s u)) := by
    rw [←integral_const_mul]
    apply integral_mono_ae (hi c s) ((hχ c).coreSlice_mass_integrable s |>.const_mul _)
    filter_upwards [radialPatchMinimizer_nonradial_cap hψ y ht hb hbt hy Z lam c s] with u hu
    have h := hu 0 (by simpa only [norm_zero] using (by positivity : 0 ≤ 3*(t-4*b)/4))
    simp only [add_zero] at h
    have hh := mul_le_mul_of_nonneg_left h (formMass_nonneg (coreSlice (χ c) s u))
    simpa only [weightedPatchCenter,conditionalPatchCenter,mul_comm,χ,p,hp] using hh
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun c _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun s _ => hbnd c s))
  simp_rw [←Finset.mul_sum,(hχ _).integral_coreSlice_mass] at hh
  rw [orderedCutForm_mass_sum p hp hψ] at hh
  exact hh

theorem sharp_eventLaw_field_cap {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {N K : ℕ} (F G : fermionGraph N) (hG : ‖fermionGraphValue N G‖^2 = 1)
    (ell : Fin K → ℝ) (j : ℕ) {A : Set (Fin K × (Fin N × Fin 3) → ℝ)}
    (hinfo : MeasurableSet[observationInformation ell j] (physicalObservationEvent ell A))
    (hp : 0 < physicalObservationProbability F ell A)
    (hlaw : graphRawLaw G = (ENNReal.ofReal (physicalObservationProbability F ell A))⁻¹ •
      Measure.map Prod.fst ((physicalObservationLaw (graphRawLaw F) K).restrict
        (physicalObservationEvent ell A)))
    {y : Space} (hy : y ≠ 0) (ha1 : localCellRadius y ≤ 1)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) (hry : r₀ ≤ ‖y‖)
    {b q : ℝ} (hb : 0 < b) (hba : 2*b ≤ localCellRadius y) (hq : 0 < q)
    (hqr : q+Real.sqrt 3*b ≤ 4*localCellRadius y)
    (hqR : q ≤ 3*(5*localCellRadius y-4*b)/4)
    (hcollar : localCellRadius y ≤ b^2*
      localOffsetMass (max (corePriceExcess Z lam (graphFormVector G)) 0) y) :
    Z/‖y‖-lam-(physicalObservationProbability F ell A)⁻¹*
      (∫ z in physicalObservationEvent ell A,
        tfPotential (jointMasterPosterior (graphRawLaw F) ell j c₁ r₀ s canonicalRealPacket
          (originalDatum ell j z)) y ∂physicalObservationLaw (graphRawLaw F) K) ≤
      tfPatchCapConstant/(localCellRadius y)^4+
      (sharpPotentialRemainder (localCellRadius y) b
        (localOffsetMass (max (corePriceExcess Z lam (graphFormVector G)) 0) y)
        (max (corePriceExcess Z lam (graphFormVector G)) 0) q+
      sharpLocalPotentialBudget (localCellRadius y)
        (localOffsetMass (max (corePriceExcess Z lam (graphFormVector G)) 0) y)
        (2*masterWidth c₁ r₀ s y)) := by
  obtain ⟨t,ht,ht0,hgap,hcmp⟩ := sharp_eventLaw_joint_comparison hZ hlam F G hG ell j
    hinfo hp hlaw hy ha1 hc hcL hr hs hs1 hry hb hba hq hqr hqR hcollar
  have ha := localCellRadius_pos hy
  have hnorm : t ≤ ‖y‖ := by
    have := ht.2
    unfold localCellRadius at this
    nlinarith [norm_nonneg y]
  have hcap := expectedRadialPatchCenter_le (graphFormVector_sobolev G).sobolevVector
    y ht0 hb (by linarith [ht.1]) hnorm Z lam
  have hm : formMass (graphFormVector G) = 1 := (graphFormVector_admissible G hG).2.2.2.2.1
  rw [hm,mul_one] at hcap
  have hpw : (localCellRadius y)^4 ≤ (t-4*b)^4 := pow_le_pow_left₀ ha.le (by linarith [ht.1]) 4
  have hd := div_le_div_of_nonneg_left tfPatchCapConstant_pos.le (by positivity : 0 < (localCellRadius y)^4) hpw
  have hh := (le_abs_self _).trans hcmp
  linarith [hcap.trans hd]

end Work_ExpectedRadialCap_barrier_scope

open MeasureTheory Filter Set
open scoped Topology

open CoulombAnalysis CoulombNeumann

 def dimensionlessPatchRemainder (a β M : ℝ) : ℝ :=
    (a^2/β^2)*localizationIMSConstant*(Real.sqrt (8*β)*actualCellMomentConstant*M)+
    (a/β^2)*neumannRemainderConstant*actualCellMomentConstant^(2/3:ℝ)*M^(4/3:ℝ)+
    (a^2/β^2)*neumannRemainderConstant*actualCellMomentConstant*M+
    (a^3/β)*((2*Real.pi+1)/2)*actualCellMomentConstant*M+
    sharpFreshFieldConstant*Real.sqrt (8*β)*actualCellMomentConstant*M^2+
    (a^2/β^2)*(packetDirichlet canonicalRealPacket/2)*768*sharpFreshFieldConstant*M

lemma scaled_mass_four_thirds {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) :
    (M/a^3)^(4/3:ℝ) = M^(4/3:ℝ)/a^4 := by
  rw [Real.div_rpow hM (by positivity),←Real.rpow_natCast,←Real.rpow_mul ha.le]
  norm_num

lemma sharpPatchRemainder_rescale {a β M : ℝ} (ha : 0 < a) (hβ : 0 < β) (hM : 0 ≤ M) :
    a^7*sharpPatchRemainder a (a*β) (M/a^3) = dimensionlessPatchRemainder a β M := by
  have hs : 8*(a*β)/a = 8*β := by field_simp
  unfold sharpPatchRemainder dimensionlessPatchRemainder
  rw [hs,scaled_mass_four_thirds ha hM]
  field_simp
  ring

 def dimensionlessLocalPotential (M u : ℝ) : ℝ :=
    (sharpOrdinaryDensityConstant*M^2)^(3/5:ℝ)*(8*Real.pi)^(2/5:ℝ)*u^(1/5:ℝ)

lemma sharpLocalPotentialBudget_rescale {a M u : ℝ} (ha : 0 < a) (hu : 0 ≤ u) :
    a^4*sharpLocalPotentialBudget a (M/a^3) (a*u) = dimensionlessLocalPotential M u := by
  have hC := sharpOrdinaryDensityConstant_nonneg
  have he : sharpOrdinaryDensityConstant*(M/a^3)^2/a =
      sharpOrdinaryDensityConstant*M^2/a^7 := by field_simp
  have hp : (a^7)^(3/5:ℝ) = a^(21/5:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul ha.le]; norm_num
  have hprod : a^4*a^(1/5:ℝ) = a^(21/5:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_add ha]
    norm_num
  unfold sharpLocalPotentialBudget dimensionlessLocalPotential
  rw [he,Real.div_rpow (mul_nonneg hC (sq_nonneg M)) (by positivity),hp,
    Real.mul_rpow ha.le hu]
  have hne : a^(21/5:ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ha _)
  calc _ = (a^4*a^(1/5:ℝ)/a^(21/5:ℝ))*
        ((sharpOrdinaryDensityConstant*M^2)^(3/5:ℝ)*(8*Real.pi)^(2/5:ℝ)*u^(1/5:ℝ)) := by ring
       _ = _ := by rw [hprod,div_self hne,one_mul]

 def dimensionlessPotentialRemainder (a β M E τ : ℝ) : ℝ :=
    Real.sqrt ((2/τ)*(E+dimensionlessPatchRemainder a β M))+
    dimensionlessLocalPotential M (τ+Real.sqrt 3*β)+
    2*Real.pi*tfPatchDensityCapConstant*τ^2+
    dimensionlessLocalPotential M (Real.sqrt 3*β)+
    Real.sqrt (8*β)*actualCellMomentConstant*M

lemma sharpPotentialRemainder_rescale {a β M E τ : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (hM : 0 ≤ M) (hτ : 0 < τ) :
    a^4*sharpPotentialRemainder a (a*β) (M/a^3) (E/a^7) (a*τ) =
      dimensionlessPotentialRemainder a β M E τ := by
  have hR := sharpPatchRemainder_rescale ha hβ hM
  have hroot : a^4*Real.sqrt ((2/(a*τ))*(E/a^7+sharpPatchRemainder a (a*β) (M/a^3))) =
      Real.sqrt ((2/τ)*(E+dimensionlessPatchRemainder a β M)) := by
    rw [←Real.sqrt_sq (by positivity : 0 ≤ a^4),←Real.sqrt_mul (sq_nonneg (a^4))]
    congr 1
    rw [←hR]
    field_simp
  have hpot1 := sharpLocalPotentialBudget_rescale (M := M) ha
    (by positivity : 0 ≤ τ+Real.sqrt 3*β)
  have hpot2 := sharpLocalPotentialBudget_rescale (M := M) ha
    (by positivity : 0 ≤ Real.sqrt 3*β)
  have he1 : a*τ+Real.sqrt 3*(a*β) = a*(τ+Real.sqrt 3*β) := by ring
  have he2 : Real.sqrt 3*(a*β) = a*(Real.sqrt 3*β) := by ring
  have he3 : 8*(a*β)/a = 8*β := by field_simp
  unfold sharpPotentialRemainder dimensionlessPotentialRemainder
  rw [mul_add,mul_add,mul_add,mul_add]
  rw [hroot,he1,he2,hpot1,hpot2,he3]
  field_simp

lemma localOffsetMass_rescale {D : ℝ} {y : Space} (hy : y ≠ 0) (ha1 : localCellRadius y ≤ 1) :
    (localCellRadius y)^3*localOffsetMass D y = 1+Real.sqrt (D*(localCellRadius y)^7) := by
  have ha := localCellRadius_pos hy
  have hh : (localCellRadius y)^3 ≤ 1 := pow_le_one₀ ha.le ha1
  have hmax : max (1/(localCellRadius y)^3) 1 = 1/(localCellRadius y)^3 :=
    max_eq_left ((le_div_iff₀ (by positivity : 0 < (localCellRadius y)^3)).mpr (by simpa using hh))
  unfold localOffsetMass
  rw [hmax,mul_add,mul_one_div_cancel (pow_ne_zero _ ha.ne'),←Real.sqrt_sq (by positivity : 0 ≤ (localCellRadius y)^3),
    ←Real.sqrt_mul (sq_nonneg ((localCellRadius y)^3))]
  congr 2
  ring

end CoulombAtom

end

end OAI
