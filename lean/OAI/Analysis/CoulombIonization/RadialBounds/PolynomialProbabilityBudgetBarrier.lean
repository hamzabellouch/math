import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.WeightedCapLimitBarrier

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_PolynomialProbabilityBudget_barrier_scope

open Filter Set
open scoped Topology

open CoulombAnalysis CoulombObservation

lemma polynomial_log_cost_tendsto (n : ℕ) {v : ℝ} (hv : 0 < v) :
    Tendsto (fun r : ℝ => r^v*(Real.log (Real.exp 1/r^n))^5)
      (𝓝[>] 0) (𝓝 0) := by
  let q : ℝ := v/5
  have hq : 0 < q := by dsimp [q]; positivity
  have hpow : Tendsto (fun r : ℝ => r^q) (𝓝[>] 0) (𝓝 0) :=
    (tendsto_id.rpow_const_nhds_zero hq).mono_left inf_le_left
  have hlog := tendsto_log_mul_rpow_nhdsGT_zero hq
  have hh := (hpow.sub (hlog.const_mul (n:ℝ))).pow 5
  simp only [mul_zero,sub_zero,zero_pow (by norm_num : (5:ℕ) ≠ 0)] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  rw [Real.log_div (Real.exp_pos 1).ne' (pow_pos hr n).ne',Real.log_exp,Real.log_pow]
  rw [show r^q-n*(Real.log r*r^q) = r^q*(1-n*Real.log r) by ring,
    mul_pow,←Real.rpow_natCast,←Real.rpow_mul hr.le]
  congr 2
  dsimp [q]
  ring

lemma polynomial_probability_budget_tendsto (n : ℕ) {v : ℝ} (hv : 2.02 < v) (δ : ℝ) :
    Tendsto (fun r : ℝ => dyadicUniformEventBudget r (r^n) δ*r^v)
      (𝓝[>] 0) (𝓝 0) := by
  have hp : Tendsto (fun r : ℝ => r^v) (𝓝[>] 0) (𝓝 0) :=
    (tendsto_id.rpow_const_nhds_zero (by linarith : 0 < v)).mono_left inf_le_left
  have hh := ((polynomial_log_cost_tendsto n (by linarith : 0 < v-2.02)).const_mul
    observationFisherConstant).add (hp.const_mul δ)
  simp only [mul_zero,add_zero] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  have he : r^(-2.02:ℝ)*r^v = r^(v-2.02) := by
    rw [←Real.rpow_add hr]
    congr 1
    ring
  dsimp only [dyadicUniformEventBudget]
  rw [add_mul]
  rw [show observationFisherConstant*r^(-2.02:ℝ)*(Real.log (Real.exp 1/r^n))^5*r^v =
    observationFisherConstant*(r^(-2.02:ℝ)*r^v)*(Real.log (Real.exp 1/r^n))^5 by ring,he]
  ring

lemma polynomial_band_excess_tendsto (n : ℕ) {ι : Type*} {l : Filter ι}
    {r : ι → ℝ} {y : ι → Space} {w δ : ℝ}
    (hr : ∀ᶠ i in l, 0 < r i) (hr0 : Tendsto r l (𝓝 0))
    (hy : ∀ᶠ i in l, ‖y i‖ ≤ 2*r i) (hw : w < 1/10) (hδ : 0 ≤ δ) :
    Tendsto (fun i => dyadicUniformEventBudget (r i) ((r i)^n) δ*
      (localCellRadius (y i))^(7-w)) l (𝓝 0) := by
  have he := (polynomial_probability_budget_tendsto n (by linarith : (2.02:ℝ) < 7-w) δ).comp
    (tendsto_nhdsWithin_iff.mpr ⟨hr0,hr⟩)
  have hn : ∀ᶠ i in l, 0 ≤ dyadicUniformEventBudget (r i) ((r i)^n) δ := by
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

end Work_PolynomialProbabilityBudget_barrier_scope

open Filter Set
open scoped Topology

open CoulombAnalysis CoulombBarrier

lemma cap_band_numerics_eventually {ι : Type*} {l : Filter ι}
    {r₀ u s : ι → ℝ} {y : ι → Space} {c₁ δ : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) (hδ : 0 ≤ δ)
    (hs0 : Tendsto s l (𝓝 0))
    (hband : ∀ᶠ i in l, 0 < r₀ i ∧ r₀ i ≤ u i ∧ u i ≤ s i ∧
      u i ≤ ‖y i‖ ∧ ‖y i‖ ≤ 2*u i) :
    ∀ᶠ i in l,
      InverseFiniteGeometry c₁ (r₀ i) (s i) ((u i)^(101/100:ℝ)) (y i) ∧
      originalFieldCapBudget (u i) ((u i)^80) δ c₁ (r₀ i) (s i) (y i)
        ((localCellRadius (y i))^(6/5:ℝ))
        (localCellRadius (y i)*(localCellRadius (y i))^masterExponent) <
          (tfPatchCapConstant+2)/(localCellRadius (y i))^4 := by
  have hr := hband.mono fun _ hi => hi.1
  have hu := hband.mono fun _ hi => hi.1.trans_le hi.2.1
  have hs := hband.mono fun _ hi => (hi.1.trans_le hi.2.1).trans_le hi.2.2.1
  have hus := hband.mono fun _ hi => hi.2.2.1
  have hyu := hband.mono fun _ hi => hi.2.2.2.2
  have hry := hband.mono fun _ hi => hi.2.1.trans hi.2.2.2.1
  have hu0 : Tendsto u l (𝓝 0) := squeeze_zero' (hu.mono fun _ hi => hi.le) hus hs0
  have hy : ∀ᶠ i in l, y i ≠ 0 := by
    filter_upwards [hband] with i hi
    exact norm_pos_iff.mp ((hi.1.trans_le hi.2.1).trans_le hi.2.2.2.1)
  have ha0 := band_local_radius_tendsto hs0 hu hus hyu
  have hD := polynomial_band_excess_tendsto 80 (δ := δ) hu hu0 hyu
    (by norm_num [masterExponent] : masterExponent < 1/10) hδ
  have hwidth := masterWidth_local_relative_tendsto hc hr hs hs0 hry
  have ht : ∀ᶠ i in l, 0 ≤ masterWidth c₁ (r₀ i) (s i) (y i) := by
    filter_upwards [hr,hs] with i hri hsi
    exact (masterWidth_pos hc hri hsi _).le
  have hlim := physical_field_cap_tendsto hy ha0 hD ht hwidth
  have hbound := hlim.eventually (gt_mem_nhds (by linarith :
    tfPatchCapConstant < tfPatchCapConstant+2))
  have hgeom := band_inverse_numerics_eventually (h := 1) (xi := 1) (δ := 0) hc hcL
    (by norm_num) (by norm_num) (by norm_num) hs0 hband
  filter_upwards [hy,hbound,hgeom] with i hyi hi hgi
  refine ⟨hgi.1,?_⟩
  apply (lt_div_iff₀ (pow_pos (localCellRadius_pos hyi) 4)).mpr
  change _*physicalFieldCapBudget _ _ _ _ _ < _ at hi
  simpa only [originalFieldCapBudget,physicalFieldCapBudget,mul_comm] using hi

theorem own_probability_cap_uniform_eventually {ι : Type*} {l : Filter ι}
    {r₀ s : ι → ℝ} {c₁ δ : ℝ}
    (hc : 0 < c₁) (hδ : 0 ≤ δ) (hs0 : Tendsto s l (𝓝 0))
    (hr₀ : ∀ᶠ i in l, 0 < r₀ i) :
    ∀ᶠ i in l, ∀ (u : ℝ) (y : Space) (p : ℝ),
      r₀ i ≤ u → u ≤ s i → u ≤ ‖y‖ → ‖y‖ ≤ 2*u → 0 < p → p ≤ u^80 →
      (localCellRadius y)^4*(p*originalFieldCapBudget u p δ c₁ (r₀ i) (s i) y
        ((localCellRadius y)^(6/5:ℝ)) (localCellRadius y*(localCellRadius y)^masterExponent)) ≤
      p^(3/4:ℝ)*(tfPatchCapConstant+1) := by
  let A : ι → Type := fun i => {q : ℝ × Space × ℝ //
    r₀ i ≤ q.1 ∧ q.1 ≤ s i ∧ q.1 ≤ ‖q.2.1‖ ∧ ‖q.2.1‖ ≤ 2*q.1 ∧
      0 < q.2.2 ∧ q.2.2 ≤ q.1^80}
  let π : (Σ i, A i) → ι := Sigma.fst
  let L : Filter (Σ i, A i) := Filter.comap π l
  have hπ : Tendsto π L l := tendsto_comap
  have hb : ∀ᶠ q in L, 0 < r₀ (π q) ∧ r₀ (π q) ≤ q.2.1.1 ∧
      q.2.1.1 ≤ s (π q) ∧ q.2.1.1 ≤ ‖q.2.1.2.1‖ ∧ ‖q.2.1.2.1‖ ≤ 2*q.2.1.1 := by
    filter_upwards [hπ.eventually hr₀] with q hq
    exact ⟨hq,q.2.2.1,q.2.2.2.1,q.2.2.2.2.1,q.2.2.2.2.2.1⟩
  have hu0 : Tendsto (fun q : Σ i, A i => q.2.1.1) L (𝓝 0) :=
    squeeze_zero' (hb.mono fun _ h => (h.1.trans_le h.2.1).le)
      (hb.mono fun _ h => h.2.2.1) (hs0.comp hπ)
  have hp : ∀ᶠ q : Σ i, A i in L, 0 < q.2.1.2.2 :=
    Eventually.of_forall fun q => q.2.2.2.2.2.2.1
  have hp0 : Tendsto (fun q : Σ i, A i => q.2.1.2.2) L (𝓝 0) := by
    apply squeeze_zero' (hp.mono fun _ h => h.le)
      (Eventually.of_forall fun q => q.2.2.2.2.2.2.2)
    simpa using hu0.pow 80
  have hh := own_probability_weighted_cap_eventually hc hδ (hs0.comp hπ) hp hp0 hb
  have he := Filter.eventually_comap.mp hh
  filter_upwards [he] with i hi
  intro u y p hru hus hyl hyu hpv hpu
  exact hi ⟨i,⟨(u,y,p),hru,hus,hyl,hyu,hpv,hpu⟩⟩ rfl

end CoulombAtom

end

end OAI
