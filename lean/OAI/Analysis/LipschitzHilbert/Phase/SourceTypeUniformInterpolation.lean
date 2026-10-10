import OAI.Analysis.LipschitzHilbert.Trees.SourceTypeUniformMoments
import OAI.Analysis.LipschitzHilbert.Phase.SourceRootPathInterpolation

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
theorem eventually_source_diagonal_finite_phases_types
    (q b : ℝ) (hb : 0 ≤ b) :
    ∀ᶠ L : ℝ in atTop, ∀ (τ σ X : Type*) (κ : Type) [MeasurableSpace X] [Fintype κ],
    ∀ (nphases : ℕ), 0 < nphases →
    ∀ (μ : Measure X) [IsFiniteMeasure μ]
      (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
      (weight : τ → X → ℝ),
      (∀ t ∈ tops, 0 ≤ precision t) → (∀ t x, 0 < weight t x) →
      (∀ t, Measurable (weight t)) →
    ∀ (K : ℕ), 0 < K → ∀ (gap : ℕ → ℝ)
      (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
      (value : X → σ → EuclideanSpace ℂ κ),
      (∀ s, Measurable (fun x => value x s)) →
      (∀ s ∈ packets, assigned s ∈ tops) →
      (∀ s ∈ packets, g.eligible cutoff (precision (assigned s)) (stop s)) →
    ∀ (phaseIndex : ℕ → (Fin nphases)) (a : ℝ) (level : ℕ) (cell : ℤ)
      (n : X → ℝ) (U S alpha mu : ℝ),
      Measurable n → Integrable n μ → (∀ x, 0 < n x) → (∀ᵐ x ∂μ, n x ≤ U) →
      0 < U → 0 ≤ S → 1 ≤ alpha → alpha ≤ 3 → 0 ≤ mu → mu ≤ 1 →
      Real.log U ≤ 3*L → (∫ x, n x ∂μ) ≤ L^b*S →
    let p := Real.sqrt L
    let F := g.sourceShiftFamily tops slope precision cutoff weight K gap
      packets assigned stop value phaseIndex a level cell
    (∀ i : (Fin nphases), ∀ eta, ∀ᵐ x ∂μ, ‖F (phaseTubePoint (Pi.single i mu) eta) x‖ ≤
      L^q*(1+Real.sqrt (∑ j, (eta j)^2))*n x) →
    (∀ i : (Fin nphases), ∀ eta, Real.sqrt (∑ j, (eta j)^2) ≤ L^2 →
      (∫ x, ‖(n x^(alpha/p-1)) • F (phaseTubePoint (Pi.single i mu) eta) x‖^p ∂μ)^(1/p) ≤
        L^(q+1)*S^(1/p)) →
    let central := F (phaseTubePoint (fun _ => mu/(Fintype.card (Fin nphases):ℝ)) (fun _ => 0))
    Integrable (fun x => ‖(n x^(alpha/p-1)) • central x‖^p) μ ∧
      (∫ x, ‖(n x^(alpha/p-1)) • central x‖^p ∂μ)^(1/p) ≤ L^(q+2)*S^(1/p) := by
  filter_upwards [eventually_source_crude_mass_budget_types q b hb,
    eventually_source_damped_vertex_root_types 6 (by norm_num),
    eventually_ge_atTop (max 1 (Real.exp 1))] with L hcrude hdamp hLbig
  intro τ σ X κ _ _ nphases hnphases μ _ g tops slope precision cutoff weight hp hw hwmeas K hK gap packets assigned stop
    value hv hassigned heligible phaseIndex a level cell n U S alpha mu hn hnint hnpos hnU
    hU hS ha ha3 hmu hmu1 hlog hmass p F hnode hsmall central
  let : Nonempty (Fin nphases) := ⟨⟨0,hnphases⟩⟩
  have hL : 1 ≤ L := (le_max_left _ _).trans hLbig
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hp0 : 0 < p := Real.sqrt_pos.mpr hL0
  have hP : 0 ≤ L^(q+1)*S^(1/p) := by positivity
  have hraw (i : (Fin nphases)) (eta : (Fin nphases) → ℝ) :
      Integrable (fun x => ‖(n x^(alpha/p-1)) • F (phaseTubePoint (Pi.single i mu) eta) x‖^p) μ ∧
      (∫ x, ‖(n x^(alpha/p-1)) • F (phaseTubePoint (Pi.single i mu) eta) x‖^p ∂μ)^(1/p) ≤
        (L^(q+1)*S^(1/p))*(1+Real.sqrt (∑ j, (eta j)^2))*Real.exp (6*Real.sqrt L) := by
    apply hcrude X κ μ n (F (phaseTubePoint (Pi.single i mu) eta)) U S alpha
      (Real.sqrt (∑ j, (eta j)^2)) hnpos hnU hn hnint
    · exact g.measurable_sourcePacketAmplitude tops slope precision cutoff weight hwmeas
        K gap packets assigned stop value hv _ a level cell
    · exact hU
    · exact hS
    · exact ha
    · exact ha3
    · exact Real.sqrt_nonneg _
    · exact hlog
    · exact hmass
    · exact hnode i eta
  have hvertices (i : (Fin nphases)) (eta : (Fin nphases) → ℝ) :
      (∫ x, ‖gaussianPhaseDamping (phaseTubePoint (Pi.single i mu) eta) •
        ((n x^(alpha/p-1)) • F (phaseTubePoint (Pi.single i mu) eta) x)‖^p ∂μ)^(1/p) ≤
          L^(q+2)*S^(1/p) := by
    have hsimplex := sourceShiftSimplex_vertex (ι := Fin nphases) hmu i
    have hd := hdamp X κ nphases μ (fun x => (n x^(alpha/p-1)) • F (phaseTubePoint (Pi.single i mu) eta) x)
      (Pi.single i mu) eta mu (L^(q+1)*S^(1/p)) p
      hsimplex.1 hsimplex.2 hmu hmu1 hP hp0 (hraw i eta).2 (hsmall i eta)
    apply hd.trans
    calc
      Real.exp 1*(L^(q+1)*S^(1/p)) ≤ L*(L^(q+1)*S^(1/p)) :=
        mul_le_mul_of_nonneg_right ((le_max_right _ _).trans hLbig) hP
      _ = L^(q+2)*S^(1/p) := by
        have he : L*L^(q+1) = L^(q+2) := by
          calc
            L*L^(q+1) = L^(1:ℝ)*L^(q+1) := by rw [Real.rpow_one]
            _ = L^(q+2) := by rw [← Real.rpow_add hL0]; congr 1; ring
        rw [← mul_assoc,he]
  exact g.sourceShiftFamily_normalized_diagonal_lp μ tops slope precision cutoff weight hp hw hwmeas
    hK gap packets assigned stop value hv hassigned heligible phaseIndex a level cell
    n hn (alpha/p-1) p (L^(q+2)*S^(1/p)) mu
    (by
      have hexp : 1 < Real.exp (1:ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
      have hLgt : 1 < L := hexp.trans_le ((le_max_right _ _).trans hLbig)
      exact (Real.lt_sqrt (by norm_num : (0:ℝ) ≤ 1)).mpr (by simpa using hLgt))
    (by positivity) hmu
    (fun i eta => source_lp_power_smul_integrable μ _ _ p (hraw i eta).1) hvertices

theorem eventually_source_root_diagonal_from_paths_types (q A B Pconst : ℝ)
    (hq : 0 ≤ q) (hA : 0 ≤ A) (hB : 0 ≤ B) (hP : 0 ≤ Pconst) :
    ∀ᶠ L : ℝ in atTop, ∀ (τ σ X : Type*) (κ : Type) [MeasurableSpace X] [Fintype κ],
    ∀ (μ : Measure X)
      (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
      (weight : τ → X → ℝ),
      (∀ t ∈ tops, 0 ≤ precision t) → (∀ t x, 0 < weight t x) →
      (∀ t ∈ tops, Integrable (weight t) μ) → (∀ t, Measurable (weight t)) →
    ∀ (K : ℕ) (hK : 0 < K), ∀ (gap : ℕ → ℝ) (packets : Finset σ)
      (assigned : σ → τ) (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ),
      (∀ s, Measurable (fun x => value x s)) →
      (∀ s ∈ packets, assigned s ∈ tops) →
      (∀ s ∈ packets, g.eligible cutoff (precision (assigned s)) (stop s)) →
    ∀ (root : ℤ) (good : Set X), MeasurableSet good →
    ∀ [IsFiniteMeasure (μ.restrict good)] (U a alpha mu : ℝ),
      0 < U → 1 ≤ alpha → alpha ≤ 3 → 0 ≤ mu → mu ≤ 1 → Real.log U ≤ 3*L →
      (g.cellTops tops slope precision cutoff 0 root).Nonempty →
    let p := Real.sqrt L
    let n := g.mass tops slope precision cutoff weight 0 root
    let F := g.sourceShiftFamily tops slope precision cutoff weight K gap packets assigned stop
      value (ShiftedBlocks.tag hK) a 0 root
    let phase := fun (i : Fin K) (eta : Fin K → ℝ) (j : ℕ) =>
      phaseTubePoint (Pi.single i mu) eta (ShiftedBlocks.tag hK j)
    let cost := 1+(L^q)^p*(L^A+1)^(alpha-1)
    (∀ x ∈ good, n x ≤ U) →
    (∀ (i : Fin K) eta x, x ∈ good →
      ‖F (phaseTubePoint (Pi.single i mu) eta) x‖ ≤
        L^(2*q)*(1+Real.sqrt (∑ j, (eta j)^2))*n x) →
    ∀ (count : Fin K → ℕ) (bad : Fin K → (Fin K → ℝ) → τ → Set X),
      (∀ i, ∀ t ∈ g.cellTops tops slope precision cutoff 0 root,
        ¬g.eligible cutoff (precision t) (ShiftedBlocks.endpoint i (count i))) →
    (∀ i eta, Real.sqrt (∑ j, (eta j)^2) ≤ L^2 →
      (∀ x ∈ good, ∀ j ≤ count i, ∀ c,
        ‖g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
          (value x) (phase i eta) a x (ShiftedBlocks.endpoint i j) c‖ ≤
          L^q*g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint i j) c x) ∧
      (∀ x ∈ good, cost*
        (∑ t ∈ (g.cellTops tops slope precision cutoff 0 root).filter
          (fun t => x ∈ bad i eta t), weight t x) ≤ 1/2) ∧
      (∀ t ∈ g.cellTops tops slope precision cutoff 0 root,
        Integrable ((good\bad i eta t).indicator (fun x => weight t x*
          g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop value
            (phase i eta) a alpha p (L^A) i t (count i) x)) μ) ∧
      (∀ t ∈ g.cellTops tops slope precision cutoff 0 root,
        (∫ x, (good\bad i eta t).indicator (fun x => weight t x*
          g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop value
            (phase i eta) a alpha p (L^A) i t (count i) x) x ∂μ) ≤
          Pconst*L^B*cost*(∫ x, weight t x ∂μ))) →
    let central := F (phaseTubePoint (fun _ => mu/(K:ℝ)) (fun _ => 0))
    let S := ∑ t ∈ tops, ∫ x, weight t x ∂μ
    IntegrableOn (fun x => ‖(n x^(alpha/p-1)) • central x‖^p) good μ ∧
      (∫ x in good, ‖(n x^(alpha/p-1)) • central x‖^p ∂μ)^(1/p) ≤
        L^(2*q+2)*S^(1/p) := by
  filter_upwards [eventually_source_tree_vertex_moment_types
      q A B Pconst hq hA hB hP,
    eventually_source_diagonal_finite_phases_types (2*q) 0 (by norm_num),
    eventually_ge_atTop (1:ℝ)] with L htree hinterp hL
  intro τ σ X κ _ _ μ g tops slope precision cutoff weight hp hw hwint hwmeas K hK gap packets
    assigned stop value hv hassigned heligible root good hgood _ U a alpha mu
    hU ha ha3 hmu hmu1 hlog hne p n F phase cost hnU hnode count bad hterminal hpaths central S
  have hp0 : 0 < p := Real.sqrt_pos.mpr (zero_lt_one.trans_le hL)
  let roots := g.cellTops tops slope precision cutoff 0 root
  have hrtop {t : τ} (ht : t ∈ roots) : t ∈ tops :=
    ((g.mem_cellTops _ _ _ _ _ _ _).mp ht).1
  have hSn : 0 ≤ S := Finset.sum_nonneg fun t _ => integral_nonneg fun x => (hw t x).le
  have hrootS : (∑ t ∈ roots, ∫ x, weight t x ∂μ) ≤ S := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro t ht
      exact hrtop ht
    · intro t _ _
      exact integral_nonneg fun x => (hw t x).le
  have hnint : Integrable n μ := integrable_finsetSum roots (fun t ht => hwint t (hrtop ht))
  have hnpos : ∀ x, 0 < n x := by
    obtain ⟨t,ht⟩ := hne
    exact fun x => g.mass_pos_of_member tops slope precision cutoff weight hw 0 root x ht
  have hmass : (∫ x, n x ∂μ.restrict good) ≤ L^(0:ℝ)*S := by
    rw [Real.rpow_zero,one_mul]
    apply (integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall fun x => (hnpos x).le) hnint).trans
    rw [show (∫ x, n x ∂μ) = ∑ t ∈ roots, ∫ x, weight t x ∂μ from
      integral_finsetSum roots (fun t ht => hwint t (hrtop ht))]
    exact hrootS
  have hsmall (i : Fin K) (eta : Fin K → ℝ) (heta : Real.sqrt (∑ j, (eta j)^2) ≤ L^2) :
      (∫ x, ‖(n x^(alpha/p-1)) • F (phaseTubePoint (Pi.single i mu) eta) x‖^p
        ∂μ.restrict good)^(1/p) ≤ L^(2*q+1)*S^(1/p) := by
    obtain ⟨henv,hbad,hpi,hpb⟩ := hpaths i eta heta
    have ht := htree τ σ X κ μ g tops slope precision cutoff weight hp hw hwint hwmeas K gap packets
      assigned stop value hv (phase i eta) a alpha ha ha3 K hK i (count i) root good hgood
      (bad i eta) (by simpa only [ShiftedBlocks.endpoint_zero] using hne)
      (by simpa only [ShiftedBlocks.endpoint_zero] using hterminal i) henv
      (by simpa only [ShiftedBlocks.endpoint_zero] using hbad)
      (by simpa only [ShiftedBlocks.endpoint_zero] using hpi)
      (by simpa only [ShiftedBlocks.endpoint_zero] using hpb)
    have hb' : (∫ x, ‖(n x^(alpha/p-1)) • F (phaseTubePoint (Pi.single i mu) eta) x‖^p
        ∂μ.restrict good)^(1/p) ≤ L^(2*q+1)*
          (∑ t ∈ roots, ∫ x, weight t x ∂μ)^(1/p) := by
      simpa only [p,n,F,phase,roots,sourceShiftFamily,ShiftedBlocks.endpoint_zero] using ht.2
    apply hb'.trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Finset.sum_nonneg fun t _ => integral_nonneg fun x => (hw t x).le)
        hrootS (one_div_nonneg.mpr hp0.le)) (by positivity)
  have hi := hinterp τ σ X κ K hK (μ.restrict good) g tops slope precision cutoff weight hp hw hwmeas
    K hK gap packets assigned stop value hv hassigned heligible (ShiftedBlocks.tag hK)
    a 0 root n U S alpha mu (g.measurable_mass tops slope precision cutoff weight hwmeas 0 root)
    hnint.restrict hnpos (by
      filter_upwards [ae_restrict_mem hgood] with x hx
      exact hnU x hx) hU hSn ha ha3 hmu hmu1 hlog hmass
    (by
      intro i eta
      filter_upwards [ae_restrict_mem hgood] with x hx
      exact hnode i eta x hx) hsmall
  simpa only [p,central,F,Fintype.card_fin,IntegrableOn] using hi

end AngularGrid
end LipschitzHilbert

end

end OAI
