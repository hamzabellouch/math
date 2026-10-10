import Mathlib
import OAI.Analysis.CoulombIonization.Ionization.PricedSelectedMaster
import OAI.Analysis.CoulombIonization.RadialBounds.SharpErrorLimitBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.SharpBudgetMonotoneBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.SharpOrdinaryCapBarrier

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_ActualUpperDeficit_barrier_scope

open MeasureTheory Set Metric
open scoped BigOperators ENNReal ContDiff

open CoulombAnalysis
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

lemma localCellRadius_rotate (g : SpatialRotation) (y : Space) :
    localCellRadius (rotate g y) = localCellRadius y := by
  simp only [localCellRadius,(rotate _).norm_map]

lemma localOffsetMass_rotate (g : SpatialRotation) (D : ℝ) (y : Space) :
    localOffsetMass D (rotate g y) = localOffsetMass D y := by
  simp only [localOffsetMass,localCellRadius_rotate]

theorem actual_upper_deficit {Z lam D : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {N : ℕ} (hN : PriceMinimizes (energy Z) lam N) (hD : 0 < D)
    {p : Space} (hp : p ≠ 0) (ha1 : localCellRadius p ≤ 1)
    {b q : ℝ} (hb : 0 < b) (hba : 2*b ≤ localCellRadius p)
    (hq : 0 < q) (hqr : q+Real.sqrt 3*b ≤ 4*localCellRadius p)
    (hqR : q ≤ 3*(5*localCellRadius p-4*b)/4)
    (hcollar : localCellRadius p ≤ b^2*(1/(localCellRadius p)^3)) :
    Z-(N:ℝ) ≤ ‖p‖*(lam+tfPatchCapConstant/(localCellRadius p)^4+
      sharpPotentialRemainder (localCellRadius p) b (localOffsetMass D p) D q) := by
  obtain ⟨F,hFn,hFE⟩ := quantum_sector_near_minimizer Z N hD
  have hψ := graphFormVector_admissible F hFn
  have hsf := hψ.sobolevFermion.sobolevVector
  have hDE : max (corePriceExcess Z lam (graphFormVector F)) 0 ≤ D :=
    max_le (priced_graph_tilt_excess hN F hFn hFE.le) hD.le
  have hcap (g : SpatialRotation) : Z/‖rotate g p‖-
      tfPotential (ordinaryDensity (graphFormVector F)) (rotate g p) ≤
      lam+tfPatchCapConstant/(localCellRadius p)^4+
        sharpPotentialRemainder (localCellRadius p) b (localOffsetMass D p) D q := by
    have hgp : rotate g p ≠ 0 := by
      intro he
      have hnorm := (rotate g).norm_map p
      rw [he,norm_zero] at hnorm
      exact hp (norm_eq_zero.mp hnorm.symm)
    have hcollar' : localCellRadius (rotate g p) ≤ b^2*
        localOffsetMass (max (corePriceExcess Z lam (graphFormVector F)) 0) (rotate g p) := by
      rw [localOffsetMass,localCellRadius_rotate]
      apply hcollar.trans
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg b)
      linarith [le_max_left (1/(localCellRadius p)^3) 1,
        Real.sqrt_nonneg (max (corePriceExcess Z lam (graphFormVector F)) 0*localCellRadius p)]
    have hbound := sharp_unconditional_field_cap hψ hZ hlam hgp
      (by simpa only [localCellRadius_rotate] using ha1) hb
      (by simpa only [localCellRadius_rotate] using hba) hq
      (by simpa only [localCellRadius_rotate] using hqr)
      (by simpa only [localCellRadius_rotate] using hqR) hcollar'
    simp only [localCellRadius_rotate,localOffsetMass_rotate] at hbound
    have he := sharpPotentialRemainder_mono (localCellRadius_pos hp) hb
      (le_trans zero_le_one (localOffsetMass_one_le _ p))
      (localOffsetMass_mono hDE p) hDE hq
    linarith [hbound.trans (add_le_add le_rfl he)]
  have hbound := L1_residualCharge_of_field_cap
    (ordinaryDensity_measurable (graphFormVector F)) (ordinaryDensity_integrable hsf)
    (ordinaryDensity_nonneg (graphFormVector F)) Z hp hcap
  have hm : formMass (graphFormVector F) = 1 := hψ.2.2.2.2.1
  rwa [ordinaryDensity_mass hsf,hm,mul_one] at hbound

end Work_ActualUpperDeficit_barrier_scope

open Filter Set
open scoped Topology

open CoulombAnalysis

 def quantumUpperDeficitConstant : ℝ :=
  1+(100000:ℝ)^4*(tfPatchCapConstant+1)

lemma quantumUpperDeficitConstant_pos : 0 < quantumUpperDeficitConstant := by
  have := tfPatchCapConstant_pos
  unfold quantumUpperDeficitConstant
  positivity

lemma pointOnFirstAxis_norm {s : ℝ} (hs : 0 ≤ s) :
    ‖s • spaceDirections 0‖ = s := by
  simp [norm_smul,spaceDirections,Real.norm_of_nonneg hs]

lemma upperDeficit_rescale {s C R : ℝ} (hs : 0 < s) :
    s^3*(s*((s^4)⁻¹+C/(s/100000)^4+R)) =
      1+(100000:ℝ)^4*(C+(s/100000)^4*R) := by
  field_simp [hs.ne']
  ring

theorem actual_uniform_upper_deficit {ι : Type*} {l : Filter ι} {s : ι → ℝ}
    (hs : ∀ᶠ i in l, 0 < s i) (hs0 : Tendsto s l (𝓝 0)) :
    ∀ᶠ i in l, ∀ Z : ℝ, 0 ≤ Z → ∀ N : ℕ,
      PriceMinimizes (energy Z) ((s i)^4)⁻¹ N →
      (s i)^3*(Z-(N:ℝ)) ≤ quantumUpperDeficitConstant := by
  let p : ι → Space := fun i => s i • spaceDirections 0
  let a : ι → ℝ := fun i => localCellRadius (p i)
  have hpn : ∀ᶠ i in l, ‖p i‖ = s i := hs.mono (fun i hi => pointOnFirstAxis_norm hi.le)
  have hp : ∀ᶠ i in l, p i ≠ 0 := by
    filter_upwards [hs,hpn] with i hi hn
    apply norm_ne_zero_iff.mp
    rw [hn]
    exact hi.ne'
  have haeq : ∀ᶠ i in l, a i = s i/100000 := by
    filter_upwards [hpn] with i hi
    simp only [a,localCellRadius,hi]
  have ha : ∀ᶠ i in l, 0 < a i := hp.mono (fun i hi => localCellRadius_pos hi)
  have ha0 : Tendsto a l (𝓝 0) := by
    have hh := hs0.div_const 100000
    simp only [zero_div] at hh
    exact hh.congr' (haeq.mono (fun _ h => h.symm))
  have hbeta := ha0.rpow_const_nhds_zero (by norm_num : (0:ℝ) < 1/5)
  have htau := ha0.rpow_const_nhds_zero (by norm_num : (0:ℝ) < 1/100000)
  have hD : Tendsto (fun i => (1:ℝ)*(a i)^(7-(1/100000:ℝ))) l (𝓝 0) := by
    simpa only [one_mul] using ha0.rpow_const_nhds_zero (by norm_num : (0:ℝ) < 7-(1/100000:ℝ))
  have herr := physical_potential_error_tendsto (D := fun _ => 1) hp ha0
    (by norm_num : (0:ℝ) < 1/100000) (by norm_num : (1/100000:ℝ) < 1/10) hD
  filter_upwards [hs,hpn,hp,ha,haeq,
    ha0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)),
    hbeta.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/8)),
    htau.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/8)),
    herr.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))]
    with i hsi hpni hpi hai haei ha1 hb1 hq1 he Z hZ N hN
  let b : ℝ := a i*(a i)^(1/5:ℝ)
  let q : ℝ := a i*(a i)^(1/100000:ℝ)
  have hb : 0 < b := mul_pos hai (Real.rpow_pos_of_pos hai _)
  have hq : 0 < q := mul_pos hai (Real.rpow_pos_of_pos hai _)
  have hba : 2*b ≤ a i := by dsimp [b]; nlinarith
  have hbb : b ≤ a i/8 := by dsimp [b]; nlinarith
  have hqq : q ≤ a i/8 := by dsimp [q]; nlinarith
  have hroot : Real.sqrt 3 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3),Real.sqrt_nonneg 3]
  have hqr : q+Real.sqrt 3*b ≤ 4*a i := by nlinarith
  have hqR : q ≤ 3*(5*a i-4*b)/4 := by nlinarith
  have hc : a i ≤ b^2*(1/(a i)^3) := microscopic_collar hai ha1.le le_rfl
  have hu := actual_upper_deficit hZ (by positivity : 0 < ((s i)^4)⁻¹)
    hN (by norm_num : (0:ℝ) < 1) hpi ha1.le hb hba hq hqr hqR hc
  rw [hpni] at hu
  have hscale := mul_le_mul_of_nonneg_left hu (pow_nonneg hsi.le 3)
  have heb : (a i)^4*sharpPotentialRemainder (a i) b
      (localOffsetMass 1 (p i)) 1 q ≤ 1 := by
    simpa only [b,q,microscopicWidth_eq hai] using he.le
  rw [show localCellRadius (p i) = a i from rfl,haei,
    upperDeficit_rescale hsi] at hscale
  apply hscale.trans
  unfold quantumUpperDeficitConstant
  rw [haei] at heb
  nlinarith

end CoulombAtom

end

end OAI
