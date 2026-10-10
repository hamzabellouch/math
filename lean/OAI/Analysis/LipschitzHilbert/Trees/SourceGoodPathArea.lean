import OAI.Analysis.LipschitzHilbert.Trees.SourceGoodPathSet
import OAI.Analysis.LipschitzHilbert.Trees.SourceBadEventUnion

namespace OAI

/-! The actual local reference tails, including every shift, give the
full weighted good-path set with its prescribed area loss. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal BigOperators
namespace LipschitzHilbert

/-- All spatial intervals are retained. The hypotheses concern individual
reference events, while the conclusion is the original weighted good set. -/
theorem eventually_source_good_path_area (K D a : ℝ) (hK : 1 ≤ K) (hD : 2 < D) :
    ∀ᶠ L : ℝ in atTop, ∀ (ι σ : Type*) (tops : Finset ι) (T : ι → SlopeBox)
      (events : ι → Finset σ) (event : ι → σ → Set (ℝ×ℝ)) (bad : ι → Set (ℝ×ℝ))
      (base : Set (ℝ×ℝ)), MeasurableSet base →
      (∀ t ∈ tops, MeasurableSet (bad t)) →
      (∀ t ∈ tops, bad t ⊆ ⋃ i ∈ events t, event t i) →
      (∀ t ∈ tops, ((events t).card:ℝ) ≤ L^a) →
      (∀ t ∈ tops, ∀ᵐ y : ℝ ∂volume, ∀ k : ℤ, ∀ i ∈ events t,
        (volume.restrict (sourceLineTile (T t).length k))
          {x | (x,y+(T t).slope*x) ∈ event t i} ≤
        ENNReal.ofReal (Real.exp (-12*L))*
          (volume.restrict (sourceLineTile (T t).length k)) univ) →
      let good := sourceGoodPathSet base tops (fun t => (T t).weight K D) bad L
      MeasurableSet good ∧ good ⊆ base ∧
        (volume.prod volume) (base \ good) ≤ ENNReal.ofReal
          ((∑ t ∈ tops, (T t).length*(T t).width)*Real.exp (-9*L)) := by
  let c := (Real.exp (2*D)*(2^D*∫ z, topProfile D z ∂volume.prod volume))*K^2
  filter_upwards [eventually_source_bad_event_tail a 11,
    eventually_source_polynomial_exp (|c|+1) 0 10 (by positivity)] with L htail hsmall
  intro ι σ tops T events event bad base hbase hbad hcover hcard hevent
  have hlocal : ∀ t ∈ tops, ∀ᵐ y : ℝ ∂volume, ∀ k : ℤ,
      (volume.restrict (sourceLineTile (T t).length k)).real
        {x | (x,y+(T t).slope*x) ∈ bad t} ≤ Real.exp (-11*L)*(T t).length := by
    intro t ht
    filter_upwards [hevent t ht] with y hy
    intro k
    let μ := volume.restrict (sourceLineTile (T t).length k)
    have h := htail σ ℝ μ (events t)
      (fun i => {x | (x,y+(T t).slope*x) ∈ event t i}) (hcard t ht) (by
        intro i hi
        simpa only [show -(11+1:ℝ)*L = -12*L by ring] using hy k i hi)
    have hsub : {x | (x,y+(T t).slope*x) ∈ bad t} ⊆
        ⋃ i ∈ events t, {x | (x,y+(T t).slope*x) ∈ event t i} := by
      intro x hx
      simpa only [mem_iUnion,mem_ofPred_eq] using hcover t ht hx
    have hlen : μ univ = ENNReal.ofReal (T t).length := by
      simp only [μ,Measure.restrict_apply_univ,sourceLineTile,Real.volume_Ico]
      congr 1
      ring
    have hb := (measure_mono hsub).trans h
    rw [hlen,← ENNReal.ofReal_mul (Real.exp_pos _).le] at hb
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq
      (ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le (T t).length_pos.le))
  have hweighted := source_weighted_bad_path_area tops T bad hbad hK hD
    (Real.exp_pos (-11*L)).le hlocal
  have hconstant : c*Real.exp (-11*L) ≤ Real.exp (-10*L) := by
    apply (mul_le_mul_of_nonneg_right (show c ≤ |c|+1 by exact (le_abs_self c).trans (by linarith))
      (Real.exp_pos (-11*L)).le).trans
    simpa only [Real.rpow_zero,mul_one,show -(10+1:ℝ)*L = -11*L by ring] using hsmall
  apply source_good_path_set_area (volume.prod volume) base hbase tops
    (fun t => (T t).weight K D) bad
    (fun t _ => ((T t).continuous_weight (zero_lt_one.trans_le hK) D).measurable)
    (fun t x => ((T t).weight_pos (zero_lt_one.trans_le hK) D x).le)
    hbad L (∑ t ∈ tops, (T t).length*(T t).width) hweighted.1
  calc
    _ ≤ (((Real.exp (2*D)*Real.exp (-11*L))*
        (2^D*∫ z, topProfile D z ∂volume.prod volume))*K^2)*
          ∑ t ∈ tops, (T t).length*(T t).width := hweighted.2
    _ = (c*Real.exp (-11*L))*(∑ t ∈ tops, (T t).length*(T t).width) := by dsimp [c]; ring
    _ ≤ Real.exp (-10*L)*(∑ t ∈ tops, (T t).length*(T t).width) :=
      mul_le_mul_of_nonneg_right hconstant
        (Finset.sum_nonneg fun t _ => mul_nonneg (T t).length_pos.le (T t).width_pos.le)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
