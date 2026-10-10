import Mathlib
import OAI.Probability.Ballisticity.Coupling.CountableFreshBuffer
import OAI.Probability.Ballisticity.Estimates.BufferTree
import OAI.Probability.Ballisticity.Coupling.FreshBufferAE

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def positiveBufferPlan {d : ℕ} (ν : Measure (Row d)) (e f : Direction d) (r : ℝ) : ℕ :=
  max 1 ⌊fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
    (commonIncrementProcess (realPosition (step e)) f 0) r⌋₊

lemma positiveBufferPlan_pos {d : ℕ} (ν : Measure (Row d)) (e f : Direction d) (r : ℝ) :
    0 < positiveBufferPlan ν e f r := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

def BufferChanceData {d : ℕ} (ν : Measure (Row d)) (e f : Direction d)
    (α c ε g R : ℝ) : Prop :=
  ∀ r : ℝ, R ≤ r →
    positiveBufferPlan ν e f r = ⌊fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r⌋₊ ∧
    ∀ z₀ : ℝ, ∀ π : Measure (Lattice d × Lattice d), IsProbabilityMeasure π →
      (∀ᵐ x ∂π, z₀+r ≤ signedCoordinate f (x.2-x.1)) →
      ENNReal.ofReal c ≤ environmentLaw ν {ω | BufferStageEvent (realPosition (step e)) f
        (positiveBufferPlan ν e f r) z₀ r ε α g π ω}

lemma bufferStageEvent_threshold_mono {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (H : ℕ) (z₀ r ε α : ℝ) {g g' : ℝ} (hgg : g' ≤ g)
    (π : Measure (Lattice d × Lattice d)) (ω : Environment d) :
    BufferStageEvent ℓ f H z₀ r ε α g π ω → BufferStageEvent ℓ f H z₀ r ε α g' π ω := by
  rintro ⟨ht,hf⟩
  exact ⟨fun j hj hjH => (ENNReal.ofReal_le_ofReal hgg).trans (ht j hj hjH),
    (ENNReal.ofReal_le_ofReal hgg).trans hf⟩

theorem actual_buffer_chance_data {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ α c : ℝ, 0 < α ∧ 0 < c ∧ ∀ ε : ℝ, 0 < ε →
      ∃ g R : ℝ, 0 < g ∧ g ≤ 1 ∧ 0 < R ∧ BufferChanceData ν e f α c ε g R := by
  obtain ⟨α,c,hα,hc,hchance⟩ := buffer_stage_success_probability ν hue e f hef htrans
  refine ⟨α,c,hα,hc,fun ε hε => ?_⟩
  obtain ⟨g,R,hg,hR,hgood⟩ := hchance ε hε
  refine ⟨min g 1,R,lt_min hg zero_lt_one,min_le_right _ _,hR,?_⟩
  intro r hr
  obtain ⟨hH,hπ⟩ := hgood r hr
  have hplan : positiveBufferPlan ν e f r = ⌊fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r⌋₊ := max_eq_right hH
  refine ⟨hplan,fun z₀ π hp hgap => ?_⟩
  have hh := hπ z₀ π hp hgap
  have hb : ENNReal.ofReal c ≤ environmentLaw ν {ω | BufferStageEvent (realPosition (step e)) f
      (positiveBufferPlan ν e f r) z₀ r ε α g π ω} := by
    rw [hplan]
    have he : {ω | BufferStageEvent (realPosition (step e)) f
        ⌊fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
          (commonIncrementProcess (realPosition (step e)) f 0) r⌋₊ z₀ r ε α g π ω} =
        {ω | BufferStageSuccess (realPosition (step e)) f
        ⌊fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
          (commonIncrementProcess (realPosition (step e)) f 0) r⌋₊ z₀ r ε α g π ω} := by
      ext ω
      exact bufferStageEvent_iff e f hH z₀ r ε α hg.le π ω
    rw [he]
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mpr hh
  exact hb.trans (measure_mono fun ω hω => bufferStageEvent_threshold_mono _ _ _ _ _ _ _
    (min_le_left g 1) π ω hω)
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma bufferTree_weighted_success {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (hef : e.1 ≠ f.1) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (z₀ ε α g c : ℝ) {κ : ℝ≥0} (hκpos : 0 < κ) (hκ1 : κ ≤ 1)
    (hκae : ∀ᵐ ω ∂environmentLaw ν, ∀ y u, κ ≤ (ω y).1 u)
    (hg : 0 < g) (hg1 : g ≤ 1) (hε : 0 ≤ ε)
    (hdata : BufferChanceData ν e f α c ε g R₀) (root : AdaptedBufferNode e)
    (hr : R₀ ≤ root.radius) (hroot : BufferNodeValid e f z₀ κ root)
    (hactive : root.active=Set.univ) (s : ℝ) (n : ℕ) :
    let B := bufferTreeSuccess e f hef R₀ z₀ ε α g κ (positiveBufferPlan ν e f)
      (positiveBufferPlan_pos ν e f) root
    ENNReal.ofReal c*(∫⁻ ω, ENNReal.ofReal (failureWeight B s n ω) ∂environmentLaw ν) ≤
      ∫⁻ ω in B n, ENNReal.ofReal (failureWeight B s n ω) ∂environmentLaw ν := by
  let H := positiveBufferPlan ν e f
  let hH := positiveBufferPlan_pos ν e f
  let nodes := fun l : BufferWords n => bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root l.val
  let A := fun l : BufferWords n => (nodes l).active
  let E := fun l : BufferWords n => {ω | BufferStageEvent (realPosition (step e)) f (H (nodes l).radius)
    z₀ (nodes l).radius ε α g ((nodes l).law ω).val ω}
  let B := bufferTreeSuccess e f hef R₀ z₀ ε α g κ H hH root
  let w := fun ω => ENNReal.ofReal (failureWeight B s n ω)
  have hAm (l) : MeasurableSet (A l) := rowSigma_le _ _ (nodes l).active_rows
  have hEm (l) : MeasurableSet (E l) := by
    have hp := (nodes l).law_rows.mono (rowSigma_le _) le_rfl
    exact (measurableSet_bufferStageEvent_rows (realPosition (step e)) f (hH _) z₀ (nodes l).radius ε α g
      (PairAtHeight (realPosition (step e)) (nodes l).level) Set.univ
      (fun x hx => ⟨Set.subset_univ _,Set.subset_univ _⟩)).preimage
        (hp.prodMk (measurable_id.mono le_rfl (rowSigma_le Set.univ)))
  have hpart := bufferWords_partition e f hef R₀ z₀ ε α g κ H hH root n
  have hbound (l : BufferWords n) : ENNReal.ofReal c*(∫⁻ ω in A l, w ω ∂environmentLaw ν) ≤
      ∫⁻ ω in A l ∩ E l, w ω ∂environmentLaw ν := by
    let N := nodes l
    let D := BelowHeight (realPosition (step e)) N.level
    have hC (x : Lattice d × Lattice d) (hx : x ∈ PairAtHeight (realPosition (step e)) N.level) :
        Strip (realPosition (step e)) x.1 (H N.radius) ⊆ Dᶜ ∧
        Strip (realPosition (step e)) x.2 (H N.radius) ⊆ Dᶜ := by
      constructor
      · intro y hy
        change ¬ dot (realPosition y) (realPosition (step e)) < N.level
        have hh := hy.1
        rw [hx.1] at hh
        exact not_lt_of_ge hh
      · intro y hy
        change ¬ dot (realPosition y) (realPosition (step e)) < N.level
        have hh := hy.1
        rw [hx.2] at hh
        exact not_lt_of_ge hh
    have hNr : R₀ ≤ N.radius := bufferNodeAt_radius e f hef R₀ z₀ ε α g κ H hH root hr l.val
    have hNv := bufferNodeAt_valid e f hef hR₀.le z₀ ε α g hκpos hκ1 hg hg1 hε H hH root hr hroot l.val
    have hvalid : ∀ᵐ ω ∂environmentLaw ν, ω ∈ N.active → IsProbabilityMeasure (N.law ω).val ∧
        ∀ᵐ x ∂(N.law ω).val, z₀+N.radius ≤ signedCoordinate f (x.2-x.1) :=
      hκae.mono fun ω hω hA => hNv ω hω hA
    have hw := buffer_failureWeight_on_branch e f hef R₀ z₀ ε α g κ H hH root s n l
    have hh := fresh_buffer_weight_ae_valid ν (realPosition (step e)) f (hH N.radius)
      z₀ N.radius ε α g c (PairAtHeight (realPosition (step e)) N.level) D Dᶜ
      disjoint_compl_right hC (fun π hp hgap => (hdata N.radius hNr).2 z₀ π.val hp hgap)
      N.law N.law_rows N.active N.active_rows hvalid (N.active.indicator w) hw
    have hleft : (∫⁻ ω in N.active, N.active.indicator w ω ∂environmentLaw ν) =
        ∫⁻ ω in N.active, w ω ∂environmentLaw ν := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (hAm l)] with ω hω
      exact Set.indicator_of_mem hω _
    have hright : (∫⁻ ω in N.active ∩ E l, N.active.indicator w ω ∂environmentLaw ν) =
        ∫⁻ ω in N.active ∩ E l, w ω ∂environmentLaw ν := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem ((hAm l).inter (hEm l))] with ω hω
      exact Set.indicator_of_mem hω.1 _
    change ENNReal.ofReal c*(∫⁻ ω in N.active, N.active.indicator w ω ∂environmentLaw ν) ≤
      ∫⁻ ω in N.active ∩ E l, N.active.indicator w ω ∂environmentLaw ν at hh
    rw [hleft,hright] at hh
    exact hh
  have hh := weighted_countable_partition_lower (environmentLaw ν) A (fun l => A l ∩ E l) hAm
    (fun l => (hAm l).inter (hEm l)) hpart.2 (fun _ => Set.inter_subset_left) w (ENNReal.ofReal c) hbound
  have ha : (⋃ l, A l)=Set.univ := hpart.1.trans hactive
  have hb : (⋃ l, A l ∩ E l)=B n := by
    unfold B bufferTreeSuccess
    congr 1
    funext l
    ext ω
    simp only [A,E,nodes,bufferNodeDecision,Set.mem_inter_iff,Set.mem_ofPred,decide_eq_true_eq]
  rw [ha,Measure.restrict_univ,hb] at hh
  exact hh

lemma bufferTree_real_success {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (hef : e.1 ≠ f.1) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (z₀ ε α g c : ℝ) (hc : 0 ≤ c) {κ : ℝ≥0} (hκpos : 0 < κ) (hκ1 : κ ≤ 1)
    (hκae : ∀ᵐ ω ∂environmentLaw ν, ∀ y u, κ ≤ (ω y).1 u)
    (hg : 0 < g) (hg1 : g ≤ 1) (hε : 0 ≤ ε)
    (hdata : BufferChanceData ν e f α c ε g R₀) (root : AdaptedBufferNode e)
    (hr : R₀ ≤ root.radius) (hroot : BufferNodeValid e f z₀ κ root)
    (hactive : root.active=Set.univ) (n : ℕ) :
    let B := bufferTreeSuccess e f hef R₀ z₀ ε α g κ (positiveBufferPlan ν e f)
      (positiveBufferPlan_pos ν e f) root
    c*(∫ ω, failureWeight B c n ω ∂environmentLaw ν) ≤
      ∫ ω in B n, failureWeight B c n ω ∂environmentLaw ν := by
  let B := bufferTreeSuccess e f hef R₀ z₀ ε α g κ (positiveBufferPlan ν e f)
      (positiveBufferPlan_pos ν e f) root
  have hBm := bufferTreeSuccess_measurable e f hef R₀ z₀ ε α g κ
    (positiveBufferPlan ν e f) (positiveBufferPlan_pos ν e f) root
  have hi := failureWeight_integrable (environmentLaw ν) B hBm c n
  have hp (ω) : 0 ≤ failureWeight B c n ω := (Real.exp_pos _).le
  have hh := bufferTree_weighted_success ν e f hef hR₀ z₀ ε α g c hκpos hκ1 hκae hg hg1 hε hdata root hr hroot hactive c n
  change ENNReal.ofReal c*(∫⁻ ω, ENNReal.ofReal (failureWeight B c n ω) ∂environmentLaw ν) ≤
      ∫⁻ ω in B n, ENNReal.ofReal (failureWeight B c n ω) ∂environmentLaw ν at hh
  rw [←ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hp),
    ←ofReal_integral_eq_lintegral_ofReal hi.restrict (ae_of_all _ hp),←ENNReal.ofReal_mul hc] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg hp)).mp hh
end DirectionalTransience

end

end

end OAI
