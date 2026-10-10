import OAI.Analysis.LipschitzHilbert.Trees.SourceGoodPathArea

namespace OAI

/-! Polynomial weight scales are admitted before forming the common
reference bad set. The weighted bad mass retains its integral bound,
and Markov's inequality gives the same area loss for the common good set. -/
noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal BigOperators
namespace LipschitzHilbert

theorem eventually_source_polynomial_good_path_area
    (D eventPower weightPower : ℝ) (hD : 2 < D) :
    ∀ᶠ L : ℝ in atTop, ∀ (K : ℝ), 1 ≤ K → K ≤ L^weightPower →
    ∀ (ι σ : Type*) (tops : Finset ι) (T : ι → SlopeBox)
      (events : ι → Finset σ) (event : ι → σ → Set (ℝ×ℝ))
      (bad : ι → Set (ℝ×ℝ)) (base : Set (ℝ×ℝ)), MeasurableSet base →
      (∀ t ∈ tops, MeasurableSet (bad t)) →
      (∀ t ∈ tops, bad t ⊆ ⋃ i ∈ events t, event t i) →
      (∀ t ∈ tops, ((events t).card:ℝ) ≤ L^eventPower) →
      (∀ t ∈ tops, ∀ᵐ y : ℝ ∂volume, ∀ k : ℤ, ∀ i ∈ events t,
        (volume.restrict (sourceLineTile (T t).length k))
          {x | (x,y+(T t).slope*x) ∈ event t i} ≤
        ENNReal.ofReal (Real.exp (-12*L))*
          (volume.restrict (sourceLineTile (T t).length k)) univ) →
    let weight := fun t => (T t).weight K D
    let S := ∑ t ∈ tops, (T t).length*(T t).width
    let good := sourceGoodPathSet base tops weight bad L
    Integrable (sourceBadPathMass tops weight bad) (volume.prod volume) ∧
      (∫ z, sourceBadPathMass tops weight bad z ∂volume.prod volume) ≤
        S*Real.exp (-10*L) ∧
      MeasurableSet good ∧ good ⊆ base ∧
      (volume.prod volume) (base \ good) ≤ ENNReal.ofReal (S*Real.exp (-9*L)) := by
  let c := Real.exp (2*D)*(2^D*∫ z, topProfile D z ∂volume.prod volume)
  filter_upwards [eventually_source_bad_event_tail eventPower 11,
    eventually_source_polynomial_exp (|c|+1) (2*weightPower) 10 (by positivity),
    eventually_ge_atTop (1:ℝ)] with L htail hsmall hL
  intro K hK hKL ι σ tops T events event bad base hbase hbad hcover hcard hevent
    weight S good
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
  have hKsq : K^2 ≤ L^(2*weightPower) := by
    calc
      K^2 ≤ (L^weightPower)^2 := pow_le_pow_left₀ (by linarith) hKL 2
      _ = L^(2*weightPower) := by
        rw [← Real.rpow_two,← Real.rpow_mul (zero_le_one.trans hL)]
        congr 1
        ring
  have hconstant : c*K^2*Real.exp (-11*L) ≤ Real.exp (-10*L) := by
    apply (mul_le_mul_of_nonneg_right
      (mul_le_mul (show c ≤ |c|+1 from (le_abs_self c).trans (by linarith)) hKsq
        (sq_nonneg K) (by positivity)) (Real.exp_pos _).le).trans
    simpa only [show -(10+1:ℝ)*L = -11*L by ring] using hsmall
  have hbound : (∫ z, sourceBadPathMass tops weight bad z ∂volume.prod volume) ≤
      S*Real.exp (-10*L) := by
    calc
      _ ≤ (((Real.exp (2*D)*Real.exp (-11*L))*
        (2^D*∫ z, topProfile D z ∂volume.prod volume))*K^2)*S := hweighted.2
      _ = (c*K^2*Real.exp (-11*L))*S := by dsimp only [c]; ring
      _ ≤ Real.exp (-10*L)*S := mul_le_mul_of_nonneg_right hconstant
        (Finset.sum_nonneg fun t _ => mul_nonneg (T t).length_pos.le (T t).width_pos.le)
      _ = _ := mul_comm _ _
  have hgood := source_good_path_set_area (volume.prod volume) base hbase tops weight bad
    (fun t _ => ((T t).continuous_weight (zero_lt_one.trans_le hK) D).measurable)
    (fun t z => ((T t).weight_pos (zero_lt_one.trans_le hK) D z).le)
    hbad L S hweighted.1 hbound
  exact ⟨hweighted.1,hbound,hgood⟩

end LipschitzHilbert

end

end OAI
