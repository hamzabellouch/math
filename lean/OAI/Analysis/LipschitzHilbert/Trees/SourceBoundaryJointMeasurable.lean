import OAI.Analysis.LipschitzHilbert.Packets.SourceBoundaryPacketError

namespace OAI

/-! Joint measurability in the common grid translation and physical
point, for the actual finite boundary coefficients and packet error. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ X : Type*} [MeasurableSpace X]

theorem measurable_path_mass_origin_point (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hw : ∀ t, Measurable (weight t)) (i : ℕ) (s : ℝ) :
    Measurable (fun z : ℝ×X => (g.withOrigin z.1).mass tops slope precision cutoff weight
      i ((g.withOrigin z.1).index i s) z.2) := by
  simp only [mass,cellTops,Finset.sum_filter]
  apply Finset.measurable_sum
  intro t _
  have hc : MeasurableSet {z : ℝ×X | (g.withOrigin z.1).index i (slope t) =
      (g.withOrigin z.1).index i s} := measurableSet_eq_fun
        ((g.measurable_index_withOrigin i (slope t)).comp measurable_fst)
        ((g.measurable_index_withOrigin i s).comp measurable_fst)
  by_cases he : g.eligible cutoff (precision t) i
  · simp only [show ∀ z : ℝ×X, (g.withOrigin z.1).eligible cutoff (precision t) i from fun _ => he,
      and_true]
    exact (hw t |>.comp measurable_snd).piecewise hc measurable_const
  · have he' : ∀ z : ℝ×X, ¬(g.withOrigin z.1).eligible cutoff (precision t) i := fun _ => he
    simp only [he',and_false,ite_false]
    exact measurable_const

theorem measurable_boundary_mass_origin_point (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hw : ∀ t, Measurable (weight t)) (base i : ℕ) (gap s : ℝ) :
    Measurable (fun z : ℝ×X => (g.withOrigin z.1).boundaryMass tops slope precision cutoff weight
      base i gap s z.2) := by
  simp_rw [boundary_mass_eq]
  apply (g.measurable_path_mass_origin_point tops slope precision cutoff weight hw i s).add
  simp only [outsideNearTops,cellTops,Finset.filter_filter,Finset.sum_filter]
  apply Finset.measurable_sum
  intro t _
  have hbase : MeasurableSet {z : ℝ×X | (g.withOrigin z.1).index base (slope t) =
      (g.withOrigin z.1).index base s} := measurableSet_eq_fun
        ((g.measurable_index_withOrigin base (slope t)).comp measurable_fst)
        ((g.measurable_index_withOrigin base s).comp measurable_fst)
  have hparent : MeasurableSet {z : ℝ×X | (g.withOrigin z.1).index i (slope t) ≠
      (g.withOrigin z.1).index i s} :=
    (measurableSet_eq_fun ((g.measurable_index_withOrigin i (slope t)).comp measurable_fst)
      ((g.measurable_index_withOrigin i s).comp measurable_fst)).compl
  have hnear : MeasurableSet {z : ℝ×X | (g.withOrigin z.1).neighbors (i+1) gap
      ((g.withOrigin z.1).index (i+1) s) ((g.withOrigin z.1).index (i+1) (slope t))} := by
    change MeasurableSet {z : ℝ×X | |(g.withOrigin z.1).center (i+1) ((g.withOrigin z.1).index (i+1) s)-
      (g.withOrigin z.1).center (i+1) ((g.withOrigin z.1).index (i+1) (slope t))| < gap+g.width (i+1)}
    exact measurableSet_lt
      (continuous_abs.measurable.comp
        (((g.measurable_center_withOrigin (i+1) s).comp measurable_fst).sub
          ((g.measurable_center_withOrigin (i+1) (slope t)).comp measurable_fst))) measurable_const
  have hel (j : ℕ) : MeasurableSet {z : ℝ×X | (g.withOrigin z.1).eligible cutoff (precision t) j} := by
    change MeasurableSet {z : ℝ×X | g.eligible cutoff (precision t) j}
    by_cases hh : g.eligible cutoff (precision t) j <;>
      simp only [hh,Set.ofPred_true,Set.ofPred_false] <;> measurability
  exact (hw t |>.comp measurable_snd).piecewise
    ((hbase.inter (hel base)).inter ((hel (i+1)).inter (hnear.inter hparent))) measurable_const

theorem measurable_sourceBoundaryLogLoss_origin_point (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hw : ∀ t, Measurable (weight t)) {K : ℕ} (hK : 0 < K)
    (gap : ℕ → ℝ) (N : ℕ) (top : τ) :
    Measurable (fun z : ℝ×X => (g.withOrigin z.1).sourceBoundaryLogLoss
      tops slope precision cutoff weight K gap N top z.2) := by
  unfold sourceBoundaryLogLoss
  apply Finset.measurable_sum
  intro i _
  simp_rw [sourceBoundaryMass_path _ tops slope precision cutoff weight hK gap]
  exact ((g.measurable_boundary_mass_origin_point tops slope precision cutoff weight hw
    (i+1-K) i (gap i) (slope top)).div
    (g.measurable_path_mass_origin_point tops slope precision cutoff weight hw i (slope top))).log

theorem measurable_sourceBoundaryCoefficient_origin_point (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    (hwm : ∀ t, Measurable (weight t)) {K : ℕ} (hK : 0 < K)
    (gap : ℕ → ℝ) (N : ℕ) (top : τ) (htop : top ∈ tops)
    (he : g.eligible cutoff (precision top) N) (a : ℝ) :
    Measurable (fun z : ℝ×X => (g.withOrigin z.1).sourceBoundaryCoefficient
      tops slope precision cutoff weight K gap N top a z.2) := by
  have heq : (fun z : ℝ×X => (g.withOrigin z.1).sourceBoundaryCoefficient
      tops slope precision cutoff weight K gap N top a z.2) =
      (fun z => Real.exp (-a*(g.withOrigin z.1).sourceBoundaryLogLoss
        tops slope precision cutoff weight K gap N top z.2)) := by
    funext z
    exact (g.withOrigin z.1).sourceBoundaryCoefficient_eq_exp tops slope precision cutoff weight
      hp hw hK gap N top htop he a z.2
  rw [heq]
  exact (measurable_const.mul (g.measurable_sourceBoundaryLogLoss_origin_point tops slope precision
    cutoff weight hwm hK gap N top)).exp

variable {σ E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem measurable_source_boundary_error_origin_point (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    (hwm : ∀ t, Measurable (weight t)) {K : ℕ} (hK : 0 < K)
    (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
    (hassigned : ∀ s ∈ packets, assigned s ∈ tops)
    (he : ∀ s ∈ packets, g.eligible cutoff (precision (assigned s)) (stop s))
    (a : ℝ) (value : X → σ → E) (hv : ∀ s, Measurable (fun x => value x s)) :
    Measurable (fun z : ℝ×X => ‖(∑ s ∈ packets, value z.2 s)-
      ∑ s ∈ packets, (((g.withOrigin z.1).sourceBoundaryCoefficient tops slope precision cutoff
        weight K gap (stop s) (assigned s) a z.2 : ℝ):ℂ) • value z.2 s‖) := by
  apply Measurable.norm
  apply Measurable.sub
  · apply Finset.measurable_sum
    intro s _
    exact (hv s).comp measurable_snd
  · apply Finset.measurable_sum
    intro s hs
    apply Measurable.smul _ ((hv s).comp measurable_snd)
    exact Complex.continuous_ofReal.measurable.comp
      (g.measurable_sourceBoundaryCoefficient_origin_point tops slope precision cutoff weight hp hw hwm
        hK gap (stop s) (assigned s) (hassigned s hs) (he s hs) a)

end LipschitzHilbert.AngularGrid

end

end OAI
