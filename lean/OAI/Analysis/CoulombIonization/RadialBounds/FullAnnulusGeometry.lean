import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.PolynomialProbabilityBudgetBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.FullAnnulusWidthNumerics

namespace OAI

noncomputable section

namespace CoulombAtom

section
open Filter Set
open scoped Topology
open CoulombAnalysis CoulombBarrier CoulombObservation

lemma fullAnnulus_local_radius_le {B u : ℝ} {y : Space}
    (hBu : 0 ≤ B*u) (hy : ‖y‖ ≤ B*u) : localCellRadius y ≤ B*u := by
  unfold localCellRadius
  linarith

lemma masterWidth_fullAnnulus_lower {c₁ B r₀ s : ℝ} {y : Space}
    (hc : 0 ≤ c₁) (hB : 1 ≤ B) (hy : y ≠ 0)
    (has : localCellRadius y ≤ B*s) :
    (c₁/B^(1+masterExponent))*(localCellRadius y)^(1+masterExponent) ≤
      masterWidth c₁ r₀ s y := by
  have hBp : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have ha := localCellRadius_pos hy
  have hr : 0 < localCellRadius y/B := div_pos ha hBp
  have hrs : localCellRadius y/B ≤ s := (div_le_iff₀ hBp).mpr (by nlinarith only [has])
  have hry : localCellRadius y/B ≤ ‖y‖ := by
    have hdiv : localCellRadius y/B ≤ localCellRadius y :=
      div_le_self ha.le hB
    apply hdiv.trans
    unfold localCellRadius
    linarith [norm_nonneg y]
  have hh := masterWidth_radius_lower (r₀ := r₀) hc hr hrs hry
  rw [Real.div_rpow ha.le hBp.le] at hh
  convert hh using 1; ring

lemma fullAnnulus_local_radius_tendsto {ι : Type*} {l : Filter ι}
    {s u : ι → ℝ} {y : ι → Space} {B : ℝ} (hB : 0 ≤ B)
    (hs0 : Tendsto s l (𝓝 0)) (hu : ∀ᶠ i in l, 0 < u i)
    (hus : ∀ᶠ i in l, u i ≤ s i) (hy : ∀ᶠ i in l, ‖y i‖ ≤ B*u i) :
    Tendsto (fun i => localCellRadius (y i)) l (𝓝 0) := by
  have hb : Tendsto (fun i => B*s i) l (𝓝 0) := by
    simpa only [mul_zero] using hs0.const_mul B
  apply squeeze_zero' (Eventually.of_forall (fun _ => by unfold localCellRadius; positivity)) _ hb
  filter_upwards [hu,hus,hy] with i hui husi hyi
  exact (fullAnnulus_local_radius_le (mul_nonneg hB hui.le) hyi).trans
    (mul_le_mul_of_nonneg_left husi hB)

theorem fullAnnulus_event_excess_tendsto (n : ℕ) {ι : Type*} {l : Filter ι}
    {u : ι → ℝ} {y : ι → Space} {B w δ : ℝ} (hB : 0 ≤ B)
    (hu : ∀ᶠ i in l, 0 < u i) (hu0 : Tendsto u l (𝓝 0))
    (hy : ∀ᶠ i in l, ‖y i‖ ≤ B*u i) (hw : w < 1/10) (hδ : 0 ≤ δ) :
    Tendsto (fun i => dyadicUniformEventBudget (u i) ((u i)^n) δ*
      (localCellRadius (y i))^(7-w)) l (𝓝 0) := by
  have he := (polynomial_probability_budget_tendsto n (by linarith : (2.02:ℝ) < 7-w) δ).comp
    (tendsto_nhdsWithin_iff.mpr ⟨hu0,hu⟩)
  have hb : Tendsto (fun i => B^(7-w)*
      (dyadicUniformEventBudget (u i) ((u i)^n) δ*(u i)^(7-w))) l (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using he.const_mul (B^(7-w))
  have hn : ∀ᶠ i in l, 0 ≤ dyadicUniformEventBudget (u i) ((u i)^n) δ := by
    filter_upwards [hu,hu0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with i hi hi1
    exact dyadicUniformEventBudget_nonneg hi (pow_pos hi _) (pow_le_one₀ hi.le hi1.le) hδ
  apply squeeze_zero' _ _ hb
  · filter_upwards [hn] with i hi
    exact mul_nonneg hi (Real.rpow_nonneg (by unfold localCellRadius; positivity) _)
  · filter_upwards [hu,hy,hn] with i hi hyi hni
    calc
      _ ≤ dyadicUniformEventBudget (u i) ((u i)^n) δ*(B*u i)^(7-w) := by
        apply mul_le_mul_of_nonneg_left _ hni
        exact Real.rpow_le_rpow (by unfold localCellRadius; positivity)
          (fullAnnulus_local_radius_le (mul_nonneg hB hi.le) hyi) (by linarith)
      _ = _ := by rw [Real.mul_rpow hB hi.le]; ring

theorem fullAnnulus_inverse_numerics_eventually {ι : Type*} {l : Filter ι}
    {r₀ u s : ι → ℝ} {y : ι → Space} {B c₁ h xi δ : ℝ}
    (hB : 1 ≤ B) (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hxi : 0 < xi) (hxih : xi < 2*h) (hδ : 0 ≤ δ)
    (hs0 : Tendsto s l (𝓝 0))
    (hband : ∀ᶠ i in l, 0 < r₀ i ∧ r₀ i ≤ u i ∧ u i ≤ s i ∧
      u i ≤ ‖y i‖ ∧ ‖y i‖ ≤ B*u i) :
    ∀ᶠ i in l,
      InverseFiniteGeometry c₁ (r₀ i) (s i) ((u i)^(101/100:ℝ)) (y i) ∧
      LowInverseNumerics c₁ (r₀ i) (s i) ((u i)^(101/100:ℝ))
        (dyadicUniformEventBudget (u i) ((u i)^40) δ) h xi quantumInverseCountConstant (y i) ∧
      HighInverseNumerics c₁ (r₀ i) (s i) ((u i)^(101/100:ℝ))
        (dyadicUniformEventBudget (u i) ((u i)^40) δ) h xi quantumInverseCountConstant (y i) ∧
      universalCellCountConstant*(localOffsetMass (dyadicUniformEventBudget (u i) ((u i)^40) δ) (y i))^2 <
        (quantumInverseCountConstant/(localCellRadius (y i))^3)^2 := by
  have hBp : 0 < B := lt_of_lt_of_le zero_lt_one hB
  let c₂ : ℝ := c₁/B^(1+masterExponent)
  have hc₂ : 0 < c₂ := div_pos hc (Real.rpow_pos_of_pos hBp _)
  have hr := hband.mono fun _ hi => hi.1
  have hu := hband.mono fun _ hi => hi.1.trans_le hi.2.1
  have hs := hband.mono fun _ hi => (hi.1.trans_le hi.2.1).trans_le hi.2.2.1
  have hus := hband.mono fun _ hi => hi.2.2.1
  have hyl := hband.mono fun _ hi => hi.2.2.2.1
  have hyu := hband.mono fun _ hi => hi.2.2.2.2
  have hry := hband.mono fun _ hi => hi.2.1.trans hi.2.2.2.1
  have hu0 : Tendsto u l (𝓝 0) := squeeze_zero' (hu.mono fun _ hi => hi.le) hus hs0
  have hy : ∀ᶠ i in l, y i ≠ 0 := by
    filter_upwards [hu,hyl] with i hui hyi
    exact norm_pos_iff.mp (hui.trans_le hyi)
  have ha := hy.mono fun _ hi => localCellRadius_pos hi
  have ha0 := fullAnnulus_local_radius_tendsto hBp.le hs0 hu hus hyu
  have hwidth := masterWidth_local_relative_tendsto hc hr hs hs0 hry
  have hw : ∀ᶠ i in l, c₂*(localCellRadius (y i))^(1+masterExponent) ≤
      masterWidth c₁ (r₀ i) (s i) (y i) := by
    filter_upwards [hy,hu,hus,hyu] with i hyi hui husi hyui
    apply masterWidth_fullAnnulus_lower hc.le hB hyi
    exact (fullAnnulus_local_radius_le (mul_nonneg hBp.le hui.le) hyui).trans
      (mul_le_mul_of_nonneg_left husi hBp.le)
  have hell : ∀ᶠ i in l, 0 ≤ (u i)^(101/100:ℝ) ∧
      (u i)^(101/100:ℝ) ≤ (100000:ℝ)^(101/100:ℝ)*(localCellRadius (y i))^(101/100:ℝ) := by
    filter_upwards [hu,hyl] with i hui hyi
    exact band_observation_width_bound hui hyi
  have hD := fullAnnulus_event_excess_tendsto 40 (δ := δ) hBp.le hu hu0 hyu
    (by norm_num [masterExponent] : masterExponent < 1/10) hδ
  have hDgap := fullAnnulus_event_excess_tendsto 40 (δ := δ) hBp.le hu hu0 hyu
    (by norm_num : (1/100:ℝ) < 1/10) hδ
  have hgeom := inverse_geometry_eventually ha ha0 hwidth
    (observation_relative_tendsto (by positivity : 0 ≤ (100000:ℝ)^(101/100:ℝ)) ha ha0 hell)
  have hlow := low_inverse_numerics_eventually_of_width (C := quantumInverseCountConstant) hc hcL hc₂
    (by positivity : 0 ≤ (100000:ℝ)^(101/100:ℝ)) (by linarith : 0 ≤ h) hxi
    hy ha0 hr hs hs0 hw hwidth hell hD hDgap
  have hhigh := high_inverse_numerics_eventually_of_width (C := quantumInverseCountConstant) hc hcL hc₂
    (by positivity : 0 ≤ (100000:ℝ)^(101/100:ℝ)) hxi hxih
    hy ha0 hr hs hs0 hw hwidth hell hD hDgap
  have hcount := inverse_count_margin_eventually hy ha0 hD
  filter_upwards [hgeom,hlow,hhigh,hcount] with i hi hlo hhi hci
  refine ⟨?_,hlo,hhi,hci⟩
  rcases hi with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  exact ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩

end
open Filter Set
open scoped Topology
open CoulombAnalysis CoulombObservation

theorem own_probability_fullAnnulus_excess_tendsto {ι : Type*} {l : Filter ι}
    {r p : ι → ℝ} {y : ι → Space} {B w δ : ℝ} (hB : 0 ≤ B)
    (hr : ∀ᶠ i in l, 0 < r i) (hr0 : Tendsto r l (𝓝 0))
    (hp : ∀ᶠ i in l, 0 < p i) (hp0 : Tendsto p l (𝓝 0))
    (hy : ∀ᶠ i in l, ‖y i‖ ≤ B*r i) (hw : w < 1/10) (hδ : 0 ≤ δ) :
    Tendsto (fun i => (p i)^(1/4:ℝ)*dyadicUniformEventBudget (r i) (p i) δ*
      (localCellRadius (y i))^(7-w)) l (𝓝 0) := by
  have he := own_probability_weighted_budget_tendsto hr hr0 hp hp0 (δ := δ)
    (by linarith : (2.02:ℝ) < 7-w)
  have hn : ∀ᶠ i in l, 0 ≤ (p i)^(1/4:ℝ)*dyadicUniformEventBudget (r i) (p i) δ := by
    filter_upwards [hr,hp,hp0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with i hi hpi hpi1
    exact mul_nonneg (Real.rpow_nonneg hpi.le _)
      (dyadicUniformEventBudget_nonneg hi hpi hpi1.le hδ)
  have hb : Tendsto (fun i => B^(7-w)*
      ((p i)^(1/4:ℝ)*dyadicUniformEventBudget (r i) (p i) δ*(r i)^(7-w))) l (𝓝 0) := by
    simpa only [mul_zero] using he.const_mul (B^(7-w))
  apply squeeze_zero' _ _ hb
  · filter_upwards [hn] with i hi
    exact mul_nonneg hi (Real.rpow_nonneg (by unfold localCellRadius; positivity) _)
  · filter_upwards [hr,hy,hn] with i hi hyi hni
    calc
      _ ≤ (p i)^(1/4:ℝ)*dyadicUniformEventBudget (r i) (p i) δ*(B*r i)^(7-w) := by
        apply mul_le_mul_of_nonneg_left _ hni
        exact Real.rpow_le_rpow (by unfold localCellRadius; positivity)
          (fullAnnulus_local_radius_le (mul_nonneg hB hi.le) hyi) (by linarith)
      _ = _ := by rw [Real.mul_rpow hB hi.le]; ring

end CoulombAtom

end

end OAI
