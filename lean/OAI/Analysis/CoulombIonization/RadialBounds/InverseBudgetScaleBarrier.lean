import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.SharpErrorLimitBarrier
import OAI.Analysis.CoulombIonization.Localization.ActualPosteriorCapBarrier

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_InverseBudgetScale_barrier_scope

open Filter Set
open scoped Topology

open CoulombAnalysis CoulombObservation

lemma polynomial_event_cost_tendsto {v : ℝ} (hv : 2.02 < v) :
    Tendsto (fun r : ℝ => r^(v-2.02)*(Real.log (Real.exp 1/r^40))^5)
      (𝓝[>] 0) (𝓝 0) := by
  let q : ℝ := (v-2.02)/5
  have hq : 0 < q := by dsimp [q]; linarith
  have hpow : Tendsto (fun r : ℝ => r^q) (𝓝[>] 0) (𝓝 0) :=
    (tendsto_id.rpow_const_nhds_zero hq).mono_left inf_le_left
  have hlog := tendsto_log_mul_rpow_nhdsGT_zero hq
  have hh := (hpow.sub (hlog.const_mul 40)).pow 5
  simp only [mul_zero,sub_zero,zero_pow (by norm_num : (5:ℕ) ≠ 0)] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  rw [Real.log_div (Real.exp_pos 1).ne' (pow_pos hr 40).ne',Real.log_exp,Real.log_pow]
  rw [show r^q-40*(Real.log r*r^q) = r^q*(1-40*Real.log r) by ring,
    mul_pow,←Real.rpow_natCast,←Real.rpow_mul hr.le]
  congr 2
  dsimp [q]
  ring

lemma polynomial_budget_tendsto {v : ℝ} (hv : 2.02 < v) (δ : ℝ) :
    Tendsto (fun r : ℝ => dyadicUniformEventBudget r (r^40) δ*r^v)
      (𝓝[>] 0) (𝓝 0) := by
  have hvp : 0 < v := by linarith
  have hp : Tendsto (fun r : ℝ => r^v) (𝓝[>] 0) (𝓝 0) :=
    (tendsto_id.rpow_const_nhds_zero hvp).mono_left inf_le_left
  have hh := ((polynomial_event_cost_tendsto hv).const_mul observationFisherConstant).add
    (hp.const_mul δ)
  simp only [mul_zero,add_zero] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  have he : r^(-2.02:ℝ)*r^v = r^(v-2.02) := by
    rw [←Real.rpow_add hr]
    congr 1
    ring
  dsimp only [dyadicUniformEventBudget]
  rw [add_mul]
  rw [show observationFisherConstant*r^(-2.02:ℝ)*(Real.log (Real.exp 1/r^40))^5*r^v =
    observationFisherConstant*(r^(-2.02:ℝ)*r^v)*(Real.log (Real.exp 1/r^40))^5 by ring,he]
  ring

theorem band_event_excess_tendsto {ι : Type*} {l : Filter ι}
    {r : ι → ℝ} {y : ι → Space} {w δ : ℝ}
    (hr : ∀ᶠ i in l, 0 < r i) (hr0 : Tendsto r l (𝓝 0))
    (hy : ∀ᶠ i in l, ‖y i‖ ≤ 2*r i) (hw : w < 1/10) (hδ : 0 ≤ δ) :
    Tendsto (fun i => dyadicUniformEventBudget (r i) ((r i)^40) δ*
      (localCellRadius (y i))^(7-w)) l (𝓝 0) := by
  have he := (polynomial_budget_tendsto (by linarith : (2.02:ℝ) < 7-w) δ).comp
    (tendsto_nhdsWithin_iff.mpr ⟨hr0,hr⟩)
  have hn : ∀ᶠ i in l, 0 ≤ dyadicUniformEventBudget (r i) ((r i)^40) δ := by
    filter_upwards [hr,hr0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with i hi hi1
    exact dyadicUniformEventBudget_nonneg hi (pow_pos hi _) (pow_le_one₀ hi.le hi1.le) hδ
  apply squeeze_zero' _ _ he
  · filter_upwards [hn] with i hi
    exact mul_nonneg hi (Real.rpow_nonneg (by unfold localCellRadius; positivity) _)
  · filter_upwards [hr,hy,hn] with i hi hyi hni
    apply mul_le_mul_of_nonneg_left _ hni
    apply Real.rpow_le_rpow (by unfold localCellRadius; positivity) _ (by linarith)
    unfold localCellRadius
    linarith

end Work_InverseBudgetScale_barrier_scope

open Filter Set
open scoped Topology

open CoulombAnalysis

lemma inverse_gap_rescale {a R : ℝ} (ha : 0 < a) (hR : 0 < R) (C G : ℝ) :
    a^4*((C/R^4)/a^(-7+(1/100:ℝ)))*G =
      (C*(a/R)^4)*(G*a^(7-(1/100:ℝ))) := by
  have he : a^(-7+(1/100:ℝ)) = (a^(7-(1/100:ℝ)))⁻¹ := by
    rw [←Real.rpow_neg ha.le]
    congr 1
    ring
  rw [he,div_inv_eq_mul]
  field_simp

lemma inverse_high_gap_rescale {a : ℝ} (ha : 0 < a) (H G : ℝ) :
    a^4*(H/a^(-7+(1/100:ℝ))+2/a^(-3+(1/100:ℝ)))*G =
      (a^4*H+2)*(G*a^(7-(1/100:ℝ))) := by
  have he1 : a^(-7+(1/100:ℝ)) = (a^(7-(1/100:ℝ)))⁻¹ := by
    rw [←Real.rpow_neg ha.le]; congr 1; ring
  have he2 : a^(-3+(1/100:ℝ)) = (a^(3-(1/100:ℝ)))⁻¹ := by
    rw [←Real.rpow_neg ha.le]; congr 1; ring
  have he3 : a^4*a^(3-(1/100:ℝ)) = a^(7-(1/100:ℝ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_add ha]
    norm_num
  rw [he1,he2,div_inv_eq_mul,div_inv_eq_mul]
  calc _ = (a^4*H)*(G*a^(7-(1/100:ℝ)))+2*G*(a^4*a^(3-(1/100:ℝ))) := by ring
       _ = _ := by rw [he3]; ring

lemma inverse_low_gap_tendsto {ι : Type*} {l : Filter ι}
    {a R G : ι → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ᶠ i in l, 0 < a i) (hR : ∀ᶠ i in l, a i ≤ R i)
    (hG : Tendsto (fun i => G i*(a i)^(7-(1/100:ℝ))) l (𝓝 0)) :
    Tendsto (fun i => (a i)^4*((C/(R i)^4)/(a i)^(-7+(1/100:ℝ)))*G i)
      l (𝓝 0) := by
  have hh := bdd_le_mul_tendsto_zero (f := fun i => C*(a i/R i)^4)
    (b := 0) (B := C) (by
      filter_upwards [ha,hR] with i hai hRi
      positivity) (by
      filter_upwards [ha,hR] with i hai hRi
      have hRi' := hai.trans_le hRi
      have hb := pow_le_one₀ (div_nonneg hai.le hRi'.le) ((div_le_one hRi').mpr hRi) (n := 4)
      exact (mul_le_mul_of_nonneg_left hb hC).trans_eq (mul_one C)) hG
  apply hh.congr'
  filter_upwards [ha,hR] with i hai hRi
  exact (inverse_gap_rescale hai (hai.trans_le hRi) C (G i)).symm

lemma inverse_high_gap_tendsto {ι : Type*} {l : Filter ι}
    {a H G : ι → ℝ} {h : ℝ} (ha : ∀ᶠ i in l, 0 < a i)
    (hH : Tendsto (fun i => (a i)^4*H i) l (𝓝 h))
    (hG : Tendsto (fun i => G i*(a i)^(7-(1/100:ℝ))) l (𝓝 0)) :
    Tendsto (fun i => (a i)^4*(H i/(a i)^(-7+(1/100:ℝ))+
      2/(a i)^(-3+(1/100:ℝ)))*G i) l (𝓝 0) := by
  have hh := (hH.add_const 2).mul hG
  simp only [mul_zero] at hh
  apply hh.congr'
  exact ha.mono fun i hi => (inverse_high_gap_rescale hi (H i) (G i)).symm

theorem inverse_potential_error_tendsto {ι : Type*} {l : Filter ι}
    {y : ι → Space} {D t : ι → ℝ}
    (hy : ∀ᶠ i in l, y i ≠ 0)
    (ha0 : Tendsto (fun i => localCellRadius (y i)) l (𝓝 0))
    (hD : Tendsto (fun i => D i*(localCellRadius (y i))^(7-masterExponent)) l (𝓝 0))
    (ht : ∀ᶠ i in l, 0 ≤ t i)
    (ht0 : Tendsto (fun i => t i/localCellRadius (y i)) l (𝓝 0)) :
    Tendsto (fun i => (localCellRadius (y i))^4*(
      sharpPotentialRemainder (localCellRadius (y i)) ((localCellRadius (y i))^(6/5:ℝ))
        (localOffsetMass (D i) (y i)) (D i)
        ((localCellRadius (y i))*(localCellRadius (y i))^masterExponent)+
      sharpLocalPotentialBudget (localCellRadius (y i)) (localOffsetMass (D i) (y i))
        (2*t i))) l (𝓝 0) := by
  have hpot := physical_potential_error_tendsto hy ha0 masterExponent_pos
    (by norm_num [masterExponent] : masterExponent < 1/10) hD
  have hu : ∀ᶠ i in l, 0 ≤ 2*(t i/localCellRadius (y i)) := by
    filter_upwards [hy,ht] with i hyi hti
    have hai := localCellRadius_pos hyi
    positivity
  have hu0 : Tendsto (fun i => 2*(t i/localCellRadius (y i))) l (𝓝 0) := by
    simpa only [mul_zero] using ht0.const_mul 2
  have hmaster := physical_master_error_tendsto hy ha0 masterExponent_pos hD hu hu0
  have hh := hpot.add hmaster
  simp only [add_zero] at hh
  apply hh.congr'
  filter_upwards [hy] with i hyi
  have hai := localCellRadius_pos hyi
  rw [show localCellRadius (y i)*(2*(t i/localCellRadius (y i))) = 2*t i by field_simp]
  ring

end CoulombAtom

end

end OAI
