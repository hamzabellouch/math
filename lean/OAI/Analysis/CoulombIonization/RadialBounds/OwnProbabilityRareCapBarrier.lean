import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.PolynomialProbabilityBudgetBarrier
import OAI.Analysis.CoulombIonization.ThomasFermi.SmallEventFieldIntegralBarrier

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_OwnProbabilityRareCap_barrier_scope

open MeasureTheory Filter Set
open scoped Topology

open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

lemma tinyProbabilityFloor_le_eighty {Z u : ℝ} (hZ : 0 ≤ Z) (hu : 0 ≤ u) :
    tinyProbabilityFloor Z u ≤ min 1 (u^80) := by
  exact div_le_self (le_min (by norm_num) (pow_nonneg hu _)) (by linarith)

lemma originalQueryField_info_measurable {N K : ℕ} (F : fermionGraph N)
    (Z lam r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr₀ : 0 < r₀)
    (hs : 0 < s) (y : Space) :
    Measurable[observationInformation (fun k : Fin K => dyadicObservationWidth r k) j]
      (fun z => originalQueryField F Z lam r j c₁ r₀ s z y) :=
  measurable_const.sub (jointMasterPosterior_potential_measurable (graphRawLaw F)
    (fun k : Fin K => dyadicObservationWidth r k) j y hc hr₀ hs canonicalRealPacket_smooth.continuous)

theorem OwnProbabilityTailTiltState.rare_cap_event {Z lam r : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) (hr : 0 < r) {N K : ℕ} {F : fermionGraph N}
    {δ c₁ r₀ s : ℝ}
    (hF : OwnProbabilityTailTiltState Z lam r K
      (fun j => tinyProbabilityFloor Z ((2:ℝ)^j.val*r)) δ F)
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr₀ : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    (j : Fin (K+1)) {y : Space} (hy : y ≠ 0)
    (hu1 : (2:ℝ)^j.val*r ≤ 1) (hry : r₀ ≤ ‖y‖)
    (hgeom : InverseFiniteGeometry c₁ r₀ s (((2:ℝ)^j.val*r)^(101/100:ℝ)) y)
    (hcap : originalFieldCapBudget ((2:ℝ)^j.val*r) (((2:ℝ)^j.val*r)^80) δ c₁ r₀ s y
        ((localCellRadius y)^(6/5:ℝ)) (localCellRadius y*(localCellRadius y)^masterExponent) <
        (tfPatchCapConstant+2)/(localCellRadius y)^4) :
    (physicalObservationLaw (graphRawLaw F) K).real
      {z | (tfPatchCapConstant+2)/(localCellRadius y)^4 <
        originalQueryField F Z lam r j c₁ r₀ s z y} < ((2:ℝ)^j.val*r)^80 := by
  let p₁ : Fin (K+1) → ℝ := fun k => min 1 (((2:ℝ)^k.val*r)^80)
  have h₁ : ∀ k, 0 < p₁ k := by intro k; dsimp [p₁]; positivity
  have hT := hF.to_tailTiltState hr h₁
    (fun _ => tinyProbabilityFloor_le_eighty hZ (by positivity))
  have hu : 0 < (2:ℝ)^j.val*r := by positivity
  have hj : p₁ j = ((2:ℝ)^j.val*r)^80 := min_eq_right (pow_le_one₀ hu.le hu1)
  have hh := hT.posterior_cap hZ hlam h₁ hc hcL hr₀ hs hs1 j y hy hgeom.radius_le hry
    ((localCellRadius y)^(6/5:ℝ)) (localCellRadius y*(localCellRadius y)^masterExponent)
    ((tfPatchCapConstant+2)/(localCellRadius y)^4)
    hgeom.cut_pos hgeom.cut_le hgeom.probe_pos hgeom.probe_fit hgeom.probe_margin hgeom.collar
    (by rw [hj]; exact hcap)
  unfold originalQueryField originalQueryDensity
  simpa only [hj,Measure.real] using hh

lemma integral_positive_excess_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {f : Ω → ℝ} (hi : Integrable f μ)
    {C a : ℝ} (hC : 0 ≤ C) (ha : 0 < a)
    (hA : MeasurableSet {z | C/a < f z}) :
    (∫ z, max (a*f z-C) 0 ∂μ) ≤ a*(∫ z in {z | C/a < f z}, f z ∂μ) := by
  let A := {z | C/a < f z}
  have he : (fun z => max (a*f z-C) 0) = A.indicator (fun z => a*f z-C) := by
    funext z
    by_cases hz : z ∈ A
    · rw [indicator_of_mem hz]
      exact max_eq_left (by have hz' := (div_lt_iff₀ ha).mp hz; nlinarith)
    · rw [indicator_of_notMem hz]
      apply max_eq_right
      have hz' : f z ≤ C/a := not_lt.mp hz
      have hh := (le_div_iff₀ ha).mp hz'
      nlinarith
  rw [he,integral_indicator hA,integral_sub (hi.const_mul a).integrableOn (integrable_const C),
    integral_const_mul,integral_const]
  simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul]
  exact sub_le_self _ (mul_nonneg ENNReal.toReal_nonneg hC)

end Work_OwnProbabilityRareCap_barrier_scope

open MeasureTheory Filter Set
open scoped Topology

open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

 theorem actual_cap_excess_eventually {ι : Type*} {l : Filter ι}
    {r₀ s Z lam : ι → ℝ} {y : ι → Space} {N K : ι → ℕ}
    {F : ∀ i, fermionGraph (N i)} {j : ∀ i, Fin (K i+1)} {c₁ δ : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) (hδ : 0 ≤ δ)
    (hs0 : Tendsto s l (𝓝 0))
    (hband : ∀ᶠ i in l, 0 < r₀ i ∧ (2:ℝ)^(j i).val*r₀ i ≤ s i ∧
      (2:ℝ)^(j i).val*r₀ i ≤ ‖y i‖ ∧ ‖y i‖ ≤ 2*((2:ℝ)^(j i).val*r₀ i))
    (hstate : ∀ᶠ i in l, 0 ≤ Z i ∧ 0 < lam i ∧
      OwnProbabilityTailTiltState (Z i) (lam i) (r₀ i) (K i)
        (fun k => tinyProbabilityFloor (Z i) ((2:ℝ)^k.val*r₀ i)) δ (F i)) :
    ∀ᶠ i in l,
      (∫ z, max ((localCellRadius (y i))^4*
        originalQueryField (F i) (Z i) (lam i) (r₀ i) (j i) c₁ (r₀ i) (s i) z (y i)-
        (tfPatchCapConstant+2)) 0 ∂physicalObservationLaw (graphRawLaw (F i)) (K i)) ≤
      (tfPatchCapConstant+2)*((2:ℝ)^(j i).val*r₀ i)^60 := by
  let u := fun i => (2:ℝ)^(j i).val*r₀ i
  have hb : ∀ᶠ i in l, 0 < r₀ i ∧ r₀ i ≤ u i ∧ u i ≤ s i ∧
      u i ≤ ‖y i‖ ∧ ‖y i‖ ≤ 2*u i := by
    filter_upwards [hband] with i hi
    refine ⟨hi.1,?_,hi.2⟩
    dsimp only [u]
    exact le_mul_of_one_le_left hi.1.le (one_le_pow₀ (by norm_num))
  have hnum := cap_band_numerics_eventually hc hcL hδ hs0 hb
  have hw := own_probability_cap_uniform_eventually hc hδ hs0 (hb.mono fun _ hi => hi.1)
  filter_upwards [hb,hnum,hw,hstate,hs0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))]
    with i hbi hni hwi hFi hsi
  have hui : 0 < u i := hbi.1.trans_le hbi.2.1
  have hsy : 0 < s i := hui.trans_le hbi.2.2.1
  have hy : y i ≠ 0 := norm_pos_iff.mp (hui.trans_le hbi.2.2.2.1)
  have ha := localCellRadius_pos hy
  have hry := hbi.2.1.trans hbi.2.2.2.1
  have hu1 := hbi.2.2.1.trans hsi.le
  let A : Set (Configuration (N i) × (Fin (K i) × (Fin (N i) × Fin 3) → ℝ)) := {z | (tfPatchCapConstant+2)/(localCellRadius (y i))^4 <
    originalQueryField (F i) (Z i) (lam i) (r₀ i) (j i) c₁ (r₀ i) (s i) z (y i)}
  have hA : MeasurableSet[observationInformation
      (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k) (j i)] A :=
    measurableSet_lt measurable_const
      (originalQueryField_info_measurable (F i) (Z i) (lam i) (r₀ i) (j i) hc hbi.1 hsy (y i))
  have hp := hFi.2.2.rare_cap_event hFi.1 hFi.2.1 hbi.1 hc hcL hbi.1 hsy hsi.le
    (j i) hy hu1 hry hni.1 hni.2
  have hsml := hFi.2.2.small_event_integral hFi.1 hFi.2.1 hbi.1 hc hcL hbi.1 hsy hsi.le
    (j i) hbi.2.2.2.1 hbi.2.2.2.2 hu1 hry hni.1
    (fun p hpp hpu => hwi (u i) (y i) p hbi.2.1 hbi.2.2.1 hbi.2.2.2.1 hbi.2.2.2.2 hpp hpu)
    A hA hp.le
  have hC : 0 ≤ tfPatchCapConstant+2 := by linarith [tfPatchCapConstant_pos]
  have hh := integral_positive_excess_le (physicalObservationLaw (graphRawLaw (F i)) (K i))
    (originalQueryField_integrable (F i) (Z i) (lam i) (r₀ i) (j i) hc hbi.1 hsy (y i))
    hC (pow_pos ha 4)
    ((observationInformation_le (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k) (j i)) A hA)
  exact hh.trans hsml

theorem actual_cap_excess_uniform_eventually {ι : Type*} {l : Filter ι}
    {r₀ s Z lam : ι → ℝ} {N K : ι → ℕ}
    {F : ∀ i, fermionGraph (N i)} {c₁ δ : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) (hδ : 0 ≤ δ)
    (hs0 : Tendsto s l (𝓝 0)) (hr₀ : ∀ᶠ i in l, 0 < r₀ i)
    (hstate : ∀ᶠ i in l, 0 ≤ Z i ∧ 0 < lam i ∧
      OwnProbabilityTailTiltState (Z i) (lam i) (r₀ i) (K i)
        (fun k => tinyProbabilityFloor (Z i) ((2:ℝ)^k.val*r₀ i)) δ (F i)) :
    ∀ᶠ i in l, ∀ (j : Fin (K i+1)) (y : Space),
      (2:ℝ)^j.val*r₀ i ≤ s i →
      (2:ℝ)^j.val*r₀ i ≤ ‖y‖ → ‖y‖ ≤ 2*((2:ℝ)^j.val*r₀ i) →
      (∫ z, max ((localCellRadius y)^4*
        originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) z y-
        (tfPatchCapConstant+2)) 0 ∂physicalObservationLaw (graphRawLaw (F i)) (K i)) ≤
      (tfPatchCapConstant+2)*((2:ℝ)^j.val*r₀ i)^60 := by
  let A : ι → Type := fun i => {p : Fin (K i+1) × Space //
    (2:ℝ)^p.1.val*r₀ i ≤ s i ∧
    (2:ℝ)^p.1.val*r₀ i ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ 2*((2:ℝ)^p.1.val*r₀ i)}
  let π : (Σ i, A i) → ι := Sigma.fst
  let L : Filter (Σ i, A i) := Filter.comap π l
  have ht : Tendsto π L l := tendsto_comap
  have hb : ∀ᶠ q in L, 0 < r₀ (π q) ∧
      (2:ℝ)^q.2.1.1.val*r₀ (π q) ≤ s (π q) ∧
      (2:ℝ)^q.2.1.1.val*r₀ (π q) ≤ ‖q.2.1.2‖ ∧
      ‖q.2.1.2‖ ≤ 2*((2:ℝ)^q.2.1.1.val*r₀ (π q)) := by
    filter_upwards [ht.eventually hr₀] with q hq
    exact ⟨hq,q.2.2⟩
  have hh := actual_cap_excess_eventually
    (F := fun q : Σ i, A i => F (π q)) (j := fun q => q.2.1.1)
    hc hcL hδ (hs0.comp ht) hb (ht.eventually hstate)
  have he := Filter.eventually_comap.mp hh
  filter_upwards [he] with i hi
  intro j y hjs hyl hyu
  exact hi ⟨i,⟨(j,y),hjs,hyl,hyu⟩⟩ rfl

end CoulombAtom

end

end OAI
