import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.InverseBudgetScaleBarrier
import OAI.Analysis.CoulombIonization.Localization.InverseObservationScaleBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.InverseThresholdMarginsBarrier

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_InverseNumericalStatements_barrier_scope

open MeasureTheory Filter Set
open scoped Topology

open CoulombAnalysis

 def inverseDensityError (c₁ r₀ s ell C : ℝ) (y : Space) : ℝ :=
  (C/(localCellRadius y)^3)*
    ((masterTestConstant canonicalRealPacket_smooth canonicalRealPacket_support:ℝ)*
      (masterWidth c₁ r₀ s y)⁻¹^4*Real.sqrt 3*((localCellRadius y)^(6/5:ℝ)+2*ell))

 def inversePotentialError (c₁ r₀ s D : ℝ) (y : Space) : ℝ :=
  sharpPotentialRemainder (localCellRadius y) ((localCellRadius y)^(6/5:ℝ))
    (localOffsetMass D y) D ((localCellRadius y)*(localCellRadius y)^masterExponent)+
  sharpLocalPotentialBudget (localCellRadius y) (localOffsetMass D y)
    (2*masterWidth c₁ r₀ s y)

 def inverseGapBudget (D : ℝ) (y : Space) : ℝ :=
  D+sharpPatchRemainder (localCellRadius y) ((localCellRadius y)^(6/5:ℝ)) (localOffsetMass D y)

 def LowInverseNumerics (c₁ r₀ s ell D h xi C : ℝ) (y : Space) : Prop :=
  let a := localCellRadius y
  let b := a^(6/5:ℝ)
  let H := (h+xi/2)/a^4
  let eta := a^(-7+(1/100:ℝ))
  ∀ t ∈ Icc (5*a) (6*a),
    localTFResponse h/a^6+inverseDensityError c₁ r₀ s ell C y <
      freshLowThreshold y (t-4*b) H eta c₁ r₀ s ∧
    H+((tfPatchCapConstant/(t-4*b)^4)/eta)*inverseGapBudget D y+
      inversePotentialError c₁ r₀ s D y < (h+xi)/a^4

 def HighInverseNumerics (c₁ r₀ s ell D h xi C : ℝ) (y : Space) : Prop :=
  let a := localCellRadius y
  let b := a^(6/5:ℝ)
  let H := (h-xi/2)/a^4
  let eta := a^(-7+(1/100:ℝ))
  let m := a^(-3+(1/100:ℝ))
  ∀ t ∈ Icc (5*a) (6*a),
    tfPatchOscillationConstant/(t-4*b)*(3*masterWidth c₁ r₀ s y) ≤ 1/2 ∧
    max (freshHighThreshold y (t-4*b) H eta c₁ r₀ s)
      (canonicalMasterAmplitude*(masterWidth c₁ r₀ s y)⁻¹^3*m)+
      inverseDensityError c₁ r₀ s ell C y < localTFResponse h/a^6 ∧
    (h-xi)/a^4+inversePotentialError c₁ r₀ s D y <
      H-(H/eta+2/m)*inverseGapBudget D y-
        2*(tfPatchOscillationConstant/(t-4*b)*(3*masterWidth c₁ r₀ s y))*(t-4*b)⁻¹^4

lemma scaled_div_pow_constant {ι : Type*} {l : Filter ι} {a : ι → ℝ}
    (ha : ∀ᶠ i in l, 0 < a i) (n : ℕ) (c : ℝ) :
    Tendsto (fun i => (a i)^n*(c/(a i)^n)) l (𝓝 c) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [ha] with i hai
  field_simp

lemma inverse_density_error_tendsto {ι : Type*} {l : Filter ι}
    {r₀ s ell : ι → ℝ} {y : ι → Space} {c₁ E C : ℝ}
    (hc : 0 < c₁) (hE : 0 ≤ E)
    (hy : ∀ᶠ i in l, y i ≠ 0)
    (ha0 : Tendsto (fun i => localCellRadius (y i)) l (𝓝 0))
    (hw : ∀ᶠ i in l, c₁*(localCellRadius (y i))^(1+masterExponent) ≤ masterWidth c₁ (r₀ i) (s i) (y i))
    (hell : ∀ᶠ i in l, 0 ≤ ell i ∧ ell i ≤ E*(localCellRadius (y i))^(101/100:ℝ)) :
    Tendsto (fun i => (localCellRadius (y i))^6*inverseDensityError c₁ (r₀ i) (s i) (ell i) C (y i)) l (𝓝 0) := by
  have ha := hy.mono fun i hi => localCellRadius_pos hi
  exact inverse_observation_error_tendsto hc hE ha ha0 hw hell (scaled_div_pow_constant ha 3 C)

end Work_InverseNumericalStatements_barrier_scope

open Filter Set
open scoped Topology

open CoulombAnalysis

 theorem low_inverse_numerics_eventually {ι : Type*} {l : Filter ι}
    {y : ι → Space} {r₀ s ell D : ι → ℝ} {c₁ E C h xi : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) (hE : 0 ≤ E)
    (hh : 0 ≤ h) (hxi : 0 < xi)
    (hy : ∀ᶠ i in l, y i ≠ 0)
    (ha0 : Tendsto (fun i => localCellRadius (y i)) l (𝓝 0))
    (hr : ∀ᶠ i in l, 0 < r₀ i) (hs : ∀ᶠ i in l, 0 < s i) (hs0 : Tendsto s l (𝓝 0))
    (hw : ∀ᶠ i in l, c₁*(localCellRadius (y i))^(1+masterExponent) ≤ masterWidth c₁ (r₀ i) (s i) (y i))
    (hw0 : Tendsto (fun i => masterWidth c₁ (r₀ i) (s i) (y i)/localCellRadius (y i)) l (𝓝 0))
    (hell : ∀ᶠ i in l, 0 ≤ ell i ∧ ell i ≤ E*(localCellRadius (y i))^(101/100:ℝ))
    (hD : Tendsto (fun i => D i*(localCellRadius (y i))^(7-masterExponent)) l (𝓝 0))
    (hDgap : Tendsto (fun i => D i*(localCellRadius (y i))^(7-(1/100:ℝ))) l (𝓝 0)) :
    ∀ᶠ i in l, LowInverseNumerics c₁ (r₀ i) (s i) (ell i) (D i) h xi C (y i) := by
  let a := fun i => localCellRadius (y i)
  let H := fun i => (h+xi/2)/(a i)^4
  have ha : ∀ᶠ i in l, 0 < a i := hy.mono fun i hi => localCellRadius_pos hi
  have hsmallb : ∀ᶠ i in l, (a i)^(6/5:ℝ) < a i := by
    filter_upwards [ha,(microscopic_relative_tendsto ha ha0).eventually
      (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with i hai hi
    simpa only [one_mul] using (div_lt_iff₀ hai).mp hi
  have hH : Tendsto (fun i => (a i)^4*H i) l (𝓝 (h+xi/2)) := scaled_div_pow_constant ha 4 _
  have hT := scaled_div_pow_constant ha 6 (localTFResponse h)
  have hdenerr := inverse_density_error_tendsto (C := C) hc hE hy ha0 hw hell
  have ht : ∀ᶠ i in l, 0 ≤ masterWidth c₁ (r₀ i) (s i) (y i) := by
    filter_upwards [hr,hs] with i hri hsi
    exact (masterWidth_pos hc hri hsi _).le
  have hpot := inverse_potential_error_tendsto hy ha0 hD ht hw0
  have hG : Tendsto (fun i => inverseGapBudget (D i) (y i)*(a i)^(7-(1/100:ℝ))) l (𝓝 0) :=
    physical_patch_error_tendsto hy ha0 (by norm_num : (0:ℝ) < 1/100) (by norm_num) hDgap
  apply eventually_forall_mem_of_selections (fun i => 5*a i) (by
    filter_upwards [ha] with i hai
    exact ⟨le_rfl,by linarith⟩)
  intro t htcut
  let R := fun i => t i-4*(a i)^(6/5:ℝ)
  have hR : ∀ᶠ i in l, a i ≤ R i := by
    filter_upwards [hsmallb,htcut] with i hbi hti
    dsimp only [R]
    linarith [hti.1]
  have hF := freshLowThreshold_tendsto hc hcL ha ha0 hr hs hs0 hR hw hw0 hH
  have hdensity := inverse_low_density_margin ha hT hdenerr hF
    (localTFResponse_strict_mono hh (by linarith : h < h+xi/2))
  have hgap := inverse_low_gap_tendsto tfPatchCapConstant_pos.le ha hR hG
  have hleft := (hH.add hgap).add hpot
  simp only [add_zero] at hleft
  have hright := scaled_div_pow_constant ha 4 (h+xi)
  have hsmall := hleft.eventually_lt hright (by linarith : h+xi/2 < h+xi)
  filter_upwards [ha,hdensity,hsmall] with i hai hdi hsi
  refine ⟨hdi,?_⟩
  apply (mul_lt_mul_iff_right₀ (pow_pos hai 4)).mp
  dsimp only [H,R,a,inverseGapBudget,inversePotentialError] at hsi ⊢
  linarith only [hsi]

open Filter Set
open scoped Topology

open CoulombAnalysis

lemma inverse_unscaled_oscillation_tendsto {ι : Type*} {l : Filter ι}
    {a R t : ι → ℝ} (ha : ∀ᶠ i in l, 0 < a i) (hR : ∀ᶠ i in l, a i ≤ R i)
    (ht0 : Tendsto (fun i => t i/a i) l (𝓝 0)) (C n : ℝ) :
    Tendsto (fun i => C/R i*(n*t i)) l (𝓝 0) := by
  have hh : Tendsto (fun i => C*n*(t i/a i)) l (𝓝 0) := by
    simpa only [mul_zero] using ht0.const_mul (C*n)
  have hm := bdd_le_mul_tendsto_zero (f := fun i => a i/R i) (b := 0) (B := 1)
    (by filter_upwards [ha,hR] with i hai hRi; exact div_nonneg hai.le (hai.le.trans hRi))
    (by filter_upwards [ha,hR] with i hai hRi; exact (div_le_one (hai.trans_le hRi)).mpr hRi) hh
  apply hm.congr'
  filter_upwards [ha,hR] with i hai hRi
  have hRi' := hai.trans_le hRi
  field_simp

 theorem high_inverse_numerics_eventually {ι : Type*} {l : Filter ι}
    {y : ι → Space} {r₀ s ell D : ι → ℝ} {c₁ E C h xi : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) (hE : 0 ≤ E)
    (hxi : 0 < xi) (hxih : xi < 2*h)
    (hy : ∀ᶠ i in l, y i ≠ 0)
    (ha0 : Tendsto (fun i => localCellRadius (y i)) l (𝓝 0))
    (hr : ∀ᶠ i in l, 0 < r₀ i) (hs : ∀ᶠ i in l, 0 < s i) (hs0 : Tendsto s l (𝓝 0))
    (hw : ∀ᶠ i in l, c₁*(localCellRadius (y i))^(1+masterExponent) ≤ masterWidth c₁ (r₀ i) (s i) (y i))
    (hw0 : Tendsto (fun i => masterWidth c₁ (r₀ i) (s i) (y i)/localCellRadius (y i)) l (𝓝 0))
    (hell : ∀ᶠ i in l, 0 ≤ ell i ∧ ell i ≤ E*(localCellRadius (y i))^(101/100:ℝ))
    (hD : Tendsto (fun i => D i*(localCellRadius (y i))^(7-masterExponent)) l (𝓝 0))
    (hDgap : Tendsto (fun i => D i*(localCellRadius (y i))^(7-(1/100:ℝ))) l (𝓝 0)) :
    ∀ᶠ i in l, HighInverseNumerics c₁ (r₀ i) (s i) (ell i) (D i) h xi C (y i) := by
  let a := fun i => localCellRadius (y i)
  let H := fun i => (h-xi/2)/(a i)^4
  have ha : ∀ᶠ i in l, 0 < a i := hy.mono fun i hi => localCellRadius_pos hi
  have hsmallb : ∀ᶠ i in l, (a i)^(6/5:ℝ) < a i := by
    filter_upwards [ha,(microscopic_relative_tendsto ha ha0).eventually
      (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with i hai hi
    simpa only [one_mul] using (div_lt_iff₀ hai).mp hi
  have hH : Tendsto (fun i => (a i)^4*H i) l (𝓝 (h-xi/2)) := scaled_div_pow_constant ha 4 _
  have hT := scaled_div_pow_constant ha 6 (localTFResponse h)
  have hdenerr := inverse_density_error_tendsto (C := C) hc hE hy ha0 hw hell
  have ht : ∀ᶠ i in l, 0 ≤ masterWidth c₁ (r₀ i) (s i) (y i) := by
    filter_upwards [hr,hs] with i hri hsi
    exact (masterWidth_pos hc hri hsi _).le
  have hpot := inverse_potential_error_tendsto hy ha0 hD ht hw0
  have hG : Tendsto (fun i => inverseGapBudget (D i) (y i)*(a i)^(7-(1/100:ℝ))) l (𝓝 0) :=
    physical_patch_error_tendsto hy ha0 (by norm_num : (0:ℝ) < 1/100) (by norm_num) hDgap
  have hgap := inverse_high_gap_tendsto ha hH hG
  have hmass := inverse_retained_tendsto hc canonicalMasterAmplitude_pos.le ha ha0 hw
  apply eventually_forall_mem_of_selections (fun i => 5*a i) (by
    filter_upwards [ha] with i hai
    exact ⟨le_rfl,by linarith⟩)
  intro t htcut
  let R := fun i => t i-4*(a i)^(6/5:ℝ)
  have hR : ∀ᶠ i in l, a i ≤ R i := by
    filter_upwards [hsmallb,htcut] with i hbi hti
    dsimp only [R]
    linarith [hti.1]
  have hF := freshHighThreshold_tendsto hc hcL ha ha0 hr hs hs0 hR hw hw0 hH
  have hdensity := inverse_high_density_margin ha hT hdenerr hF hmass
    (localTFResponse_nonneg (h-xi/2))
    (localTFResponse_strict_mono (by linarith : 0 ≤ h-xi/2) (by linarith : h-xi/2 < h))
  have hosc := inverse_unscaled_oscillation_tendsto ha hR hw0 tfPatchOscillationConstant 3
  have hoscsmall := hosc.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2))
  have hoscscaled := inverse_oscillation_tendsto tfPatchOscillationConstant_pos.le
    (by norm_num : (0:ℝ) ≤ 3) ha hR ht hw0
  have hleft := (scaled_div_pow_constant ha 4 (h-xi)).add hpot
  simp only [add_zero] at hleft
  have hright := (hH.sub hgap).sub (hoscscaled.const_mul 2)
  simp only [sub_zero,mul_zero] at hright
  have hsmall := hleft.eventually_lt hright (by linarith : h-xi < h-xi/2)
  filter_upwards [ha,hoscsmall,hdensity,hsmall] with i hai hosi hdi hsi
  refine ⟨hosi.le,hdi,?_⟩
  apply (mul_lt_mul_iff_right₀ (pow_pos hai 4)).mp
  dsimp only [H,R,a,inverseGapBudget,inversePotentialError] at hsi ⊢
  linarith only [hsi]

end CoulombAtom

end

end OAI
