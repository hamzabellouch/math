import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.SharpErrorLimitBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.FreshRetainedMassBarrier
import OAI.Analysis.CoulombIonization.ThomasFermi.InverseThresholdLimitBarrier

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_InverseThresholdMargins_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology

open CoulombAnalysis

lemma eventually_forall_mem_of_selections {ι α : Type*} {l : Filter ι}
    {S : ι → Set α} {P : ι → α → Prop} (d : ι → α)
    (hd : ∀ᶠ i in l, d i ∈ S i)
    (h : ∀ f : ι → α, (∀ᶠ i in l, f i ∈ S i) → ∀ᶠ i in l, P i (f i)) :
    ∀ᶠ i in l, ∀ x ∈ S i, P i x := by
  classical
  let f : ι → α := fun i => if hi : ∃ x ∈ S i, ¬P i x then Classical.choose hi else d i
  have hf : ∀ᶠ i in l, f i ∈ S i := by
    filter_upwards [hd] with i hi
    dsimp only [f]
    split_ifs with hn
    · exact (Classical.choose_spec hn).1
    · exact hi
  filter_upwards [h f hf] with i hi
  intro x hx
  by_contra hn
  have hex : ∃ x ∈ S i, ¬P i x := ⟨x,hx,hn⟩
  exact (Classical.choose_spec hex).2 (by simpa only [f,dite_eq_left hex] using hi)

lemma localTFResponse_nonneg (h : ℝ) : 0 ≤ localTFResponse h := by
  have hT := tfKinetic_pos
  unfold localTFResponse
  exact Real.rpow_nonneg (div_nonneg (le_max_right _ _) (by positivity)) _

lemma localTFResponse_strict_mono {h H : ℝ} (hh : 0 ≤ h) (hH : h < H) :
    localTFResponse h < localTFResponse H := by
  have hT : 0 < (5/3:ℝ)*tfKinetic := mul_pos (by norm_num) tfKinetic_pos
  unfold localTFResponse
  rw [max_eq_left hh,max_eq_left (hh.trans hH.le)]
  exact Real.rpow_lt_rpow (div_nonneg hh hT.le) ((div_lt_div_iff_of_pos_right hT).mpr hH) (by norm_num)

lemma freshLowThreshold_tendsto {ι : Type*} {l : Filter ι}
    {a r₀ s R H : ι → ℝ} {y : ι → Space} {c₁ h : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (ha : ∀ᶠ i in l, 0 < a i) (ha0 : Tendsto a l (𝓝 0))
    (hr : ∀ᶠ i in l, 0 < r₀ i) (hs : ∀ᶠ i in l, 0 < s i) (hs0 : Tendsto s l (𝓝 0))
    (hR : ∀ᶠ i in l, a i ≤ R i)
    (hw : ∀ᶠ i in l, c₁*(a i)^(1+masterExponent) ≤ masterWidth c₁ (r₀ i) (s i) (y i))
    (hw0 : Tendsto (fun i => masterWidth c₁ (r₀ i) (s i) (y i)/a i) l (𝓝 0))
    (hH : Tendsto (fun i => (a i)^4*H i) l (𝓝 h)) :
    Tendsto (fun i => (a i)^6*freshLowThreshold (y i) (R i) (H i)
      ((a i)^(-7+(1/100:ℝ))) c₁ (r₀ i) (s i)) l (𝓝 (localTFResponse h)) := by
  simpa only [freshLowThreshold,localTFResponse,neg_one_mul,neg_mul,one_mul,sub_eq_add_neg] using
    (fresh_threshold_response_tendsto (sign := -1) hc hcL (by norm_num : (2:ℝ) ≤ 2)
      ha ha0 hr hs hs0 hR hw hw0 hH)

lemma freshHighThreshold_tendsto {ι : Type*} {l : Filter ι}
    {a r₀ s R H : ι → ℝ} {y : ι → Space} {c₁ h : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (ha : ∀ᶠ i in l, 0 < a i) (ha0 : Tendsto a l (𝓝 0))
    (hr : ∀ᶠ i in l, 0 < r₀ i) (hs : ∀ᶠ i in l, 0 < s i) (hs0 : Tendsto s l (𝓝 0))
    (hR : ∀ᶠ i in l, a i ≤ R i)
    (hw : ∀ᶠ i in l, c₁*(a i)^(1+masterExponent) ≤ masterWidth c₁ (r₀ i) (s i) (y i))
    (hw0 : Tendsto (fun i => masterWidth c₁ (r₀ i) (s i) (y i)/a i) l (𝓝 0))
    (hH : Tendsto (fun i => (a i)^4*H i) l (𝓝 h)) :
    Tendsto (fun i => (a i)^6*freshHighThreshold (y i) (R i) (H i)
      ((a i)^(-7+(1/100:ℝ))) c₁ (r₀ i) (s i)) l (𝓝 (localTFResponse h)) := by
  simpa only [freshHighThreshold,localTFResponse,one_mul] using
    (fresh_threshold_response_tendsto (sign := 1) hc hcL (by norm_num : (2:ℝ) ≤ 3)
      ha ha0 hr hs hs0 hR hw hw0 hH)

lemma inverse_low_density_margin {ι : Type*} {l : Filter ι}
    {a T E F : ι → ℝ} {t f : ℝ} (ha : ∀ᶠ i in l, 0 < a i)
    (hT : Tendsto (fun i => (a i)^6*T i) l (𝓝 t))
    (hE : Tendsto (fun i => (a i)^6*E i) l (𝓝 0))
    (hF : Tendsto (fun i => (a i)^6*F i) l (𝓝 f)) (htf : t < f) :
    ∀ᶠ i in l, T i+E i < F i := by
  have hh := (hT.add hE).eventually_lt hF (by simpa using htf)
  filter_upwards [ha,hh] with i hai hi
  apply (mul_lt_mul_iff_right₀ (pow_pos hai 6)).mp
  linarith

lemma inverse_high_density_margin {ι : Type*} {l : Filter ι}
    {a T E F M : ι → ℝ} {t f : ℝ} (ha : ∀ᶠ i in l, 0 < a i)
    (hT : Tendsto (fun i => (a i)^6*T i) l (𝓝 t))
    (hE : Tendsto (fun i => (a i)^6*E i) l (𝓝 0))
    (hF : Tendsto (fun i => (a i)^6*F i) l (𝓝 f))
    (hM : Tendsto (fun i => (a i)^6*M i) l (𝓝 0)) (hf : 0 ≤ f) (htf : f < t) :
    ∀ᶠ i in l, max (F i) (M i)+E i < T i := by
  have hh := ((hF.max hM).add hE).eventually_lt hT (by simpa [max_eq_left hf] using htf)
  filter_upwards [ha,hh] with i hai hi
  apply (mul_lt_mul_iff_right₀ (pow_pos hai 6)).mp
  rw [mul_add,mul_max_of_nonneg _ _ (pow_nonneg hai.le _)]
  exact hi

end Work_InverseThresholdMargins_barrier_scope

open Filter Set
open scoped Topology

open CoulombAnalysis CoulombBarrier

lemma band_local_radius_pos {u : ℝ} {y : Space} (hu : 0 < u) (hy : u ≤ ‖y‖) :
    0 < localCellRadius y := by
  unfold localCellRadius
  exact div_pos (hu.trans_le hy) (by norm_num)

lemma band_local_radius_le {u : ℝ} {y : Space} (hu : 0 ≤ u) (hy : ‖y‖ ≤ 2*u) :
    localCellRadius y ≤ u := by
  unfold localCellRadius
  linarith

lemma band_observation_width_bound {u : ℝ} {y : Space} (hu : 0 < u) (hy : u ≤ ‖y‖) :
    0 ≤ u^(101/100:ℝ) ∧
      u^(101/100:ℝ) ≤ (100000:ℝ)^(101/100:ℝ)*(localCellRadius y)^(101/100:ℝ) := by
  constructor
  · positivity
  · have hn : 0 ≤ ‖y‖ := norm_nonneg y
    have hh := Real.rpow_le_rpow hu.le hy (by norm_num : (0:ℝ) ≤ 101/100)
    convert hh using 1
    rw [←Real.mul_rpow (by norm_num) (by unfold localCellRadius; positivity)]
    congr 1
    unfold localCellRadius
    ring

lemma band_local_radius_tendsto {ι : Type*} {l : Filter ι} {s u : ι → ℝ}
    {y : ι → Space} (hs0 : Tendsto s l (𝓝 0))
    (hu : ∀ᶠ i in l, 0 < u i) (hus : ∀ᶠ i in l, u i ≤ s i)
    (hy : ∀ᶠ i in l, ‖y i‖ ≤ 2*u i) :
    Tendsto (fun i => localCellRadius (y i)) l (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => by unfold localCellRadius; positivity)) _ hs0
  filter_upwards [hu,hus,hy] with i hui husi hyi
  exact (band_local_radius_le hui.le hyi).trans husi

lemma observation_relative_tendsto {ι : Type*} {l : Filter ι} {a ell : ι → ℝ}
    {E : ℝ} (_hE : 0 ≤ E) (ha : ∀ᶠ i in l, 0 < a i)
    (ha0 : Tendsto a l (𝓝 0))
    (hell : ∀ᶠ i in l, 0 ≤ ell i ∧ ell i ≤ E*(a i)^(101/100:ℝ)) :
    Tendsto (fun i => ell i/a i) l (𝓝 0) := by
  have hh : Tendsto (fun i => E*(a i)^(1/100:ℝ)) l (𝓝 0) := by
    simpa only [mul_zero] using (ha0.rpow_const_nhds_zero (by norm_num : (0:ℝ) < 1/100)).const_mul E
  apply squeeze_zero' _ _ hh
  · filter_upwards [ha,hell] with i hai hei
    exact div_nonneg hei.1 hai.le
  · filter_upwards [ha,hell] with i hai hei
    calc _ ≤ E*(a i)^(101/100:ℝ)/a i := div_le_div_of_nonneg_right hei.2 hai.le
         _ = _ := by
           have heq : (a i)^(101/100:ℝ)/a i = (a i)^(1/100:ℝ) := by
             calc _ = (a i)^((101/100:ℝ)-1) := by rw [Real.rpow_sub hai,Real.rpow_one]
                  _ = _ := by norm_num
           rw [mul_div_assoc,heq]

lemma microscopic_relative_tendsto {ι : Type*} {l : Filter ι} {a : ι → ℝ}
    (ha : ∀ᶠ i in l, 0 < a i) (ha0 : Tendsto a l (𝓝 0)) :
    Tendsto (fun i => (a i)^(6/5:ℝ)/a i) l (𝓝 0) := by
  have hh := ha0.rpow_const_nhds_zero (by norm_num : (0:ℝ) < 1/5)
  apply hh.congr'
  filter_upwards [ha] with i hai
  calc _ = (a i)^((6/5:ℝ)-1) := by norm_num
       _ = _ := by rw [Real.rpow_sub hai,Real.rpow_one]

theorem inverse_geometry_eventually {ι : Type*} {l : Filter ι}
    {a t ell : ι → ℝ} (ha : ∀ᶠ i in l, 0 < a i) (ha0 : Tendsto a l (𝓝 0))
    (ht0 : Tendsto (fun i => t i/a i) l (𝓝 0))
    (hell0 : Tendsto (fun i => ell i/a i) l (𝓝 0)) :
    ∀ᶠ i in l,
      a i ≤ 1 ∧
      0 < (a i)^(6/5:ℝ) ∧ 2*(a i)^(6/5:ℝ) ≤ a i ∧
      0 < a i*(a i)^masterExponent ∧
      a i*(a i)^masterExponent+Real.sqrt 3*(a i)^(6/5:ℝ) ≤ 4*a i ∧
      a i*(a i)^masterExponent ≤ 3*(5*a i-4*(a i)^(6/5:ℝ))/4 ∧
      a i ≤ ((a i)^(6/5:ℝ))^2*(1/(a i)^3) ∧
      3*t i ≤ (5*a i-4*(a i)^(6/5:ℝ))/12 ∧
      2*t i+Real.sqrt 3*((a i)^(6/5:ℝ)+2*ell i) < a i := by
  have hb0 := microscopic_relative_tendsto ha ha0
  have hq0 := ha0.rpow_const_nhds_zero masterExponent_pos
  filter_upwards [ha,
    ha0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)),
    hb0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/100)),
    hq0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/100)),
    ht0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/100)),
    hell0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/100))]
    with i hai ha1 hbi hqi hti heli
  have hb : (a i)^(6/5:ℝ) < a i/100 := by linarith [(div_lt_iff₀ hai).mp hbi]
  have ht : t i < a i/100 := by linarith [(div_lt_iff₀ hai).mp hti]
  have he : ell i < a i/100 := by linarith [(div_lt_iff₀ hai).mp heli]
  have hq : a i*(a i)^masterExponent < a i/100 := by nlinarith
  have hbpos : 0 < (a i)^(6/5:ℝ) := Real.rpow_pos_of_pos hai _
  have hqpos : 0 < a i*(a i)^masterExponent := mul_pos hai (Real.rpow_pos_of_pos hai _)
  have hroot : Real.sqrt 3 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3),Real.sqrt_nonneg 3]
  have hprod : Real.sqrt 3*(a i)^(6/5:ℝ) ≤ 2*(a i)^(6/5:ℝ) :=
    mul_le_mul_of_nonneg_right hroot hbpos.le
  have hcol := microscopic_collar hai ha1.le (m := 1/(a i)^3) le_rfl
  rw [microscopicWidth_eq hai] at hcol
  refine ⟨ha1.le,hbpos,by linarith,hqpos,by linarith,by linarith,hcol,by linarith,?_⟩
  have he' : Real.sqrt 3*ell i < 2*a i/100 := by
    calc _ < Real.sqrt 3*(a i/100) := mul_lt_mul_of_pos_left he (Real.sqrt_pos.mpr (by norm_num))
         _ ≤ _ := by nlinarith
  nlinarith

end CoulombAtom

end

end OAI
