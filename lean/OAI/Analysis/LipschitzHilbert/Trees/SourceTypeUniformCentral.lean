import OAI.Analysis.LipschitzHilbert.Phase.SourceTypeUniformInterpolation
import OAI.Analysis.LipschitzHilbert.Trees.SourceCentralPathGain

namespace OAI

/-! The numerical thresholds are chosen before all spatial and coefficient
index types. These are the existing source estimates with their universal
type binders moved inside the eventual statement; no bound changes. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert
namespace AngularGrid
attribute [local instance] Classical.propDecidable
theorem eventually_source_central_sum_gain_types (d q Q : ℝ)
    (hd : 0 ≤ d) (hq : 0 ≤ q) (hQ : 0 ≤ Q) :
    ∀ᶠ L : ℝ in atTop, ∀ (τ σ X : Type*) (κ : Type) [MeasurableSpace X] [Fintype κ],
    ∀ D : ℝ, 1 ≤ D → D ≤ L^d →
    ∀ (μ : Measure X) [IsFiniteMeasure μ] (g : AngularGrid) (tops : Finset τ)
      (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ),
      (∀ t ∈ tops, 0 ≤ precision t) → (∀ t x, 0 < weight t x) →
      (∀ t, Measurable (weight t)) →
    ∀ (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
      (value : X → σ → EuclideanSpace ℂ κ),
      (∀ s, Measurable (fun x => value x s)) →
      (∀ s ∈ packets, assigned s ∈ tops) →
      (∀ s ∈ packets, g.eligible cutoff (precision (assigned s)) (stop s)) →
    ∀ (start Nmass Fmass S : ℝ), 0 < Nmass → 0 < Fmass → 0 ≤ S →
      L/2 ≤ Real.log Nmass → μ.real Set.univ ≤ Fmass → S ≤ L^q*Nmass^2*Fmass →
      (∀ t ∈ tops, start ≤ slope t ∧ slope t ≤ start+g.rootWidth) →
      (∀ᵐ x ∂μ, (∑ t ∈ tops, weight t x) ≤ L^q*Nmass) →
    let K := SourceParameters.blockCount L
    let p := Real.sqrt L
    let alpha := 2+PhaseCombinatorics.phaseParameter D
    let beta := ((1+PhaseCombinatorics.phaseParameter D)/p)/(K:ℝ)
    let n := fun c => g.mass tops slope precision cutoff weight 0 c
    let amp := fun c x => g.sourcePacketAmplitude tops slope precision cutoff weight K gap
      packets assigned stop (value x) (fun _ => (beta:ℂ)) beta x 0 c
    (∀ c ∈ g.sourceRootCells tops slope precision cutoff,
      Integrable (fun x => ‖(n c x^(alpha/p-1)) • amp c x‖^p) μ) →
    (∀ c ∈ g.sourceRootCells tops slope precision cutoff,
      (∫ x, ‖(n c x^(alpha/p-1)) • amp c x‖^p ∂μ)^(1/p) ≤ L^q*S^(1/p)) →
    let W := fun x => ∑ s ∈ packets,
      ((g.sourceBoundaryCoefficient tops slope precision cutoff weight K gap
        (stop s) (assigned s) beta x:ℝ):ℂ) • value x s
    Integrable (fun x => ‖W x‖) μ ∧ (∫ x, ‖W x‖ ∂μ) ≤ L^(-Q)*Nmass*Fmass := by
  filter_upwards [eventually_source_central_integral_gain_ae d q (Q+1) hd hq (by positivity),
    eventually_ge_atTop (2:ℝ)] with L hgain hL
  intro τ σ X κ _ _ D hD hDL μ _ g tops slope precision cutoff weight hp hw hwmeas gap packets
    assigned stop value hv hassigned heligible start Nmass Fmass S hN hF hS hlogN
    hmeasure hSbound hslope htotal K p alpha beta n amp henergy hmoment W
  have hL0 : 0 < L := by linarith
  have hK : 0 < K := SourceParameters.blockCount_pos (by linarith)
  let B := L^(-(Q+1))*Nmass*Fmass
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hroot (c : ℤ) (hc : c ∈ g.sourceRootCells tops slope precision cutoff) :
      Integrable (fun x => n c x^beta*‖amp c x‖) μ ∧
        (∫ x, n c x^beta*‖amp c x‖ ∂μ) ≤ B := by
    have hnpos : ∀ x, 0 < n c x := by
      obtain ⟨t,ht⟩ := (g.mem_sourceRootCells tops slope precision cutoff c).mp hc
      intro x
      exact g.mass_pos_of_member tops slope precision cutoff weight hw 0 c x ht
    have hnupper : ∀ᵐ x ∂μ, n c x ≤ L^q*Nmass := by
      filter_upwards [htotal] with x hx
      exact (g.mass_le_total tops slope precision cutoff weight
        (fun t x => (hw t x).le) 0 c x).trans hx
    exact hgain D hD hDL X κ μ (n c) (amp c) Nmass Fmass S hN hF hS hlogN
      hnpos hnupper (g.measurable_mass tops slope precision cutoff weight hwmeas 0 c)
      (g.measurable_sourcePacketAmplitude tops slope precision cutoff weight hwmeas K gap
        packets assigned stop value hv _ beta 0 c) hmeasure hSbound (henergy c hc) (hmoment c hc)
  have heq (c : ℤ) (x : X) :
      ‖((n c x^beta:ℝ):ℂ) • amp c x‖ = n c x^beta*‖amp c x‖ := by
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg
        (g.mass_nonnegative tops slope precision cutoff weight (fun t x => (hw t x).le) 0 c x) _)]
  have hs := g.sourceBoundarySum_integral_le μ tops slope precision cutoff weight hp hw hwmeas
    hK gap packets assigned stop value hv hassigned heligible beta start B hB hslope
    (fun c hc => by
      change Integrable (fun x => ‖((n c x^beta:ℝ):ℂ) • amp c x‖) μ
      simpa only [heq] using (hroot c hc).1)
    (fun c hc => by
      change (∫ x, ‖((n c x^beta:ℝ):ℂ) • amp c x‖ ∂μ) ≤ B
      simpa only [heq] using (hroot c hc).2)
  refine ⟨hs.1,hs.2.trans ?_⟩
  have hpower : 2*L^(-(Q+1)) ≤ L^(-Q) := by
    calc
      2*L^(-(Q+1)) ≤ L*L^(-(Q+1)) :=
        mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg hL0.le _)
      _ = L^(-Q) := by
        conv_lhs => lhs; rw [← Real.rpow_one L]
        rw [← Real.rpow_add hL0]
        congr 1
        ring
  dsimp only [B]
  calc
    2*(L^(-(Q+1))*Nmass*Fmass) = (2*L^(-(Q+1)))*Nmass*Fmass := by ring
    _ ≤ L^(-Q)*Nmass*Fmass := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hpower hN.le) hF.le

theorem eventually_source_central_from_paths_types (q A B Pconst d m Q : ℝ)
    (hq : 0 ≤ q) (hA : 0 ≤ A) (hB : 0 ≤ B) (hP : 0 ≤ Pconst)
    (hd : 0 ≤ d) (hm : 0 ≤ m) (hqm : 2*q+2 ≤ m) (hQ : 0 ≤ Q) :
    ∀ᶠ L : ℝ in atTop, ∀ (τ σ X : Type*) (κ : Type) [MeasurableSpace X] [Fintype κ],
    ∀ D : ℝ, 1 ≤ D → D ≤ L^d →
    ∀ (μ : Measure X) (g : AngularGrid) (tops : Finset τ)
      (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ),
      (∀ t ∈ tops, 0 ≤ precision t) → (∀ t x, 0 < weight t x) →
      (∀ t ∈ tops, Integrable (weight t) μ) → (∀ t, Measurable (weight t)) →
    ∀ (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
      (value : X → σ → EuclideanSpace ℂ κ),
      (∀ s, Measurable (fun x => value x s)) →
      (∀ s ∈ packets, assigned s ∈ tops) →
      (∀ s ∈ packets, g.eligible cutoff (precision (assigned s)) (stop s)) →
    ∀ (start Nmass Fmass : ℝ), 0 < Nmass → 0 < Fmass →
      L/2 ≤ Real.log Nmass → Real.log Nmass ≤ 2*L →
      (∀ t ∈ tops, start ≤ slope t ∧ slope t ≤ start+g.rootWidth) →
    ∀ (good : Set X), MeasurableSet good →
    ∀ [IsFiniteMeasure (μ.restrict good)], (μ.restrict good).real univ ≤ Fmass →
      (∀ x ∈ good, (∑ t ∈ tops, weight t x) ≤ L^m*Nmass) →
    let S := ∑ t ∈ tops, ∫ x, weight t x ∂μ
    S ≤ L^m*Nmass^2*Fmass →
    ∀ (hK : 0 < SourceParameters.blockCount L),
    let K := SourceParameters.blockCount L
    let p := Real.sqrt L
    let alpha := 2+PhaseCombinatorics.phaseParameter D
    let mu := PhaseCombinatorics.phaseMu D p
    let a := mu/(K:ℝ)
    let phase := fun (i : Fin K) (eta : Fin K → ℝ) (j : ℕ) =>
      phaseTubePoint (Pi.single i mu) eta (ShiftedBlocks.tag hK j)
    let cost := 1+(L^q)^p*(L^A+1)^(alpha-1)
    (∀ (i : Fin K) eta x, x ∈ good → ∀ c,
      ‖g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
        (value x) (phase i eta) a x 0 c‖ ≤
        L^(2*q)*(1+Real.sqrt (∑ j, (eta j)^2))*g.mass tops slope precision cutoff weight 0 c x) →
    ∀ (count : Fin K → ℕ) (bad : Fin K → (Fin K → ℝ) → τ → Set X),
      (∀ i, ∀ t ∈ tops, ¬g.eligible cutoff (precision t) (ShiftedBlocks.endpoint i (count i))) →
    (∀ i eta, Real.sqrt (∑ j, (eta j)^2) ≤ L^2 →
      (∀ x ∈ good, ∀ j ≤ count i, ∀ c,
        ‖g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
          (value x) (phase i eta) a x (ShiftedBlocks.endpoint i j) c‖ ≤
          L^q*g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint i j) c x) ∧
      (∀ x ∈ good, cost*(∑ t ∈ tops.filter (fun t => x ∈ bad i eta t), weight t x) ≤ 1/2) ∧
      (∀ t ∈ tops, Integrable ((good\bad i eta t).indicator (fun x => weight t x*
        g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop value
          (phase i eta) a alpha p (L^A) i t (count i) x)) μ) ∧
      (∀ t ∈ tops, (∫ x, (good\bad i eta t).indicator (fun x => weight t x*
        g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop value
          (phase i eta) a alpha p (L^A) i t (count i) x) x ∂μ) ≤
        Pconst*L^B*cost*(∫ x, weight t x ∂μ))) →
    let W := fun x => ∑ s ∈ packets,
      ((g.sourceBoundaryCoefficient tops slope precision cutoff weight K gap
        (stop s) (assigned s) a x:ℝ):ℂ) • value x s
    IntegrableOn (fun x => ‖W x‖) good μ ∧
      (∫ x in good, ‖W x‖ ∂μ) ≤ L^(-Q)*Nmass*Fmass := by
  filter_upwards [eventually_source_root_diagonal_from_paths_types
      q A B Pconst hq hA hB hP,
    eventually_source_central_sum_gain_types
      d m Q hd hm hQ,
    eventually_source_polynomial_mass_log m,eventually_ge_atTop (256:ℝ)]
    with L hroot hcentral hlogmass hL
  intro τ σ X κ _ _ D hD hDL μ g tops slope precision cutoff weight hp hw hwint hwmeas gap packets assigned
    stop value hv hassigned heligible start Nmass Fmass hN hF hloglo hloghi hslope good hgood _
    hmeasure htotal S hSbound hK K p alpha mu a phase cost hcrude count bad hterminal hpaths W
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hp0 : 0 < p := Real.sqrt_pos.mpr hL0
  have halpha : 1 ≤ alpha ∧ alpha ≤ 3 := by
    have htheta := PhaseCombinatorics.phaseParameter_range hD
    change 0 < PhaseCombinatorics.phaseParameter D ∧ PhaseCombinatorics.phaseParameter D ≤ 1/3 at htheta
    dsimp only [alpha]
    constructor <;> linarith [htheta.1,htheta.2]
  have hmu := source_phaseMu_small hD hL
  have hSn : 0 ≤ S := Finset.sum_nonneg fun t _ => integral_nonneg fun x => (hw t x).le
  have hcost : 0 ≤ cost := by dsimp only [cost]; positivity
  have hr (c : ℤ) (hc : c ∈ g.sourceRootCells tops slope precision cutoff) := by
    have hrmem {t : τ} (ht : t ∈ g.cellTops tops slope precision cutoff 0 c) : t ∈ tops :=
      ((g.mem_cellTops _ _ _ _ _ _ _).mp ht).1
    exact hroot τ σ X κ μ g tops slope precision cutoff weight hp hw hwint hwmeas K hK gap packets
      assigned stop value hv hassigned heligible c good hgood (L^m*Nmass) a alpha mu
      (by positivity) halpha.1 halpha.2 hmu.1.le (hmu.2.trans (by norm_num))
      (hlogmass Nmass hN hloghi) ((g.mem_sourceRootCells tops slope precision cutoff c).mp hc)
      (fun x hx => (g.mass_le_total tops slope precision cutoff weight
        (fun t x => (hw t x).le) 0 c x).trans (htotal x hx))
      (fun i eta x hx => hcrude i eta x hx c) count bad
      (fun i t ht => hterminal i t (hrmem ht))
      (fun i eta heta => by
        obtain ⟨henv,hbad,hpi,hpb⟩ := hpaths i eta heta
        refine ⟨henv,?_,fun t ht => hpi t (hrmem ht),fun t ht => hpb t (hrmem ht)⟩
        intro x hx
        apply (mul_le_mul_of_nonneg_left ?_ hcost).trans (hbad x hx)
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset_filter _ (fun t ht => hrmem ht))
          (fun t _ _ => (hw t x).le))
  have hmoment (c : ℤ) (hc : c ∈ g.sourceRootCells tops slope precision cutoff) :
      (∫ x in good, ‖(g.mass tops slope precision cutoff weight 0 c x^(alpha/p-1)) •
        g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
          (value x) (fun _ => (a:ℂ)) a x 0 c‖^p ∂μ)^(1/p) ≤ L^m*S^(1/p) := by
    have hb := (hr c hc).2
    simp only [sourceShiftFamily,phaseTubePoint,Complex.ofReal_zero,zero_mul,add_zero] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hL1 hqm) (Real.rpow_nonneg hSn _))
  have hi := hcentral τ σ X κ D hD hDL (μ.restrict good) g tops slope precision cutoff weight hp hw hwmeas
    gap packets assigned stop value hv hassigned heligible start Nmass Fmass S hN hF hSn
    hloglo hmeasure hSbound hslope (by
      filter_upwards [ae_restrict_mem hgood] with x hx
      exact htotal x hx)
    (fun c hc => by
      have hh := (hr c hc).1
      simpa only [p,K,alpha,mu,a,IntegrableOn,PhaseCombinatorics.phaseMu,sourceShiftFamily,phaseTubePoint,Complex.ofReal_zero,zero_mul,add_zero] using hh)
    hmoment
  exact hi

end AngularGrid
end LipschitzHilbert

end

end OAI
