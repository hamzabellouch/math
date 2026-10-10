import OAI.Analysis.LipschitzHilbert.Phase.SourceFinitePhaseInterpolation
import OAI.Analysis.LipschitzHilbert.Trees.SourceTreeMomentBudget

namespace OAI

/-! The actual good-path integrals imply the root diagonal moment.
The phase count is chosen after L, and the spatial measure is restricted
to the common good set throughout analytic interpolation. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ σ X : Type*} {κ : Type} [MeasurableSpace X] [Fintype κ]

theorem eventually_source_root_diagonal_from_paths (q A B Pconst : ℝ)
    (hq : 0 ≤ q) (hA : 0 ≤ A) (hB : 0 ≤ B) (hP : 0 ≤ Pconst) :
    ∀ᶠ L : ℝ in atTop, ∀ (μ : Measure X)
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
  filter_upwards [eventually_source_tree_vertex_moment (X := X) (κ := κ)
      q A B Pconst hq hA hB hP,
    eventually_source_diagonal_finite_phases_ae (X := X) (κ := κ) (2*q) 0 (by norm_num),
    eventually_ge_atTop (1:ℝ)] with L htree hinterp hL
  intro μ g tops slope precision cutoff weight hp hw hwint hwmeas K hK gap packets
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
    have ht := htree μ g tops slope precision cutoff weight hp hw hwint hwmeas K gap packets
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
  have hi := hinterp K hK (μ.restrict good) g tops slope precision cutoff weight hp hw hwmeas
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

end LipschitzHilbert.AngularGrid

end

end OAI
