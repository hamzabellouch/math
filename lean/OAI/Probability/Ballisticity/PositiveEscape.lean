import OAI.Probability.Ballisticity.RowBridge

namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

namespace DirectionalTransience

lemma uniformElliptic_directional_zero_one {d : ℕ} (hd : 3 ≤ d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (hue : UniformElliptic ν)
    (ℓ : Vector d) (hℓ : ℓ ≠ 0) :
    annealedLaw ν (TransientPaths ℓ) = 0 ∨ annealedLaw ν (TransientPaths ℓ) = 1 := by
  have h := DirectionalZeroOne.directional_zero_one d hd (RowBridge.rowLaw ν)
    (RowBridge.strictEllipticity ν hue) ℓ hℓ
  change DirectionalZeroOne.annealed (RowBridge.rowLaw ν) 0 (TransientPaths ℓ) = 0 ∨
    DirectionalZeroOne.annealed (RowBridge.rowLaw ν) 0 (TransientPaths ℓ) = 1 at h
  rwa [← RowBridge.annealedLaw_eq ν] at h

lemma dot_div_right {d : ℕ} (v ℓ : Vector d) (r : ℝ) :
    dot v (fun i => ℓ i / r) = dot v ℓ / r := by
  simp only [dot, mul_div_assoc, Finset.sum_div]

lemma dot_self_pos_of_ne_zero {d : ℕ} (ℓ : Vector d) (hℓ : ℓ ≠ 0) :
    0 < dot ℓ ℓ := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hℓ
  change ℓ i ≠ 0 at hi
  exact (mul_self_pos.mpr hi).trans_le
    (Finset.single_le_sum (fun j _ => mul_self_nonneg (ℓ j)) (Finset.mem_univ i))

lemma transientPaths_div_pos {d : ℕ} (ℓ : Vector d) {r : ℝ} (hr : 0 < r) :
    TransientPaths (fun i => ℓ i / r) = TransientPaths ℓ := by
  ext X
  simp only [TransientPaths, Set.mem_ofPred_eq, dot_div_right]
  exact tendsto_div_const_atTop_of_pos hr

lemma velocity_of_positive_escape {d : ℕ} (hd : 3 ≤ d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (hue : UniformElliptic ν)
    (ℓ : Vector d) (hℓ : ℓ ≠ 0) (hpos : 0 < annealedLaw ν (TransientPaths ℓ)) :
    ∃ v : Vector d, 0 < dot v ℓ ∧ HasVelocity ν v := by
  have hprob : annealedLaw ν (TransientPaths ℓ) = 1 :=
    (uniformElliptic_directional_zero_one hd ν hue ℓ hℓ).resolve_left hpos.ne'
  have hs : 0 < dot ℓ ℓ := dot_self_pos_of_ne_zero ℓ hℓ
  let r : ℝ := Real.sqrt (dot ℓ ℓ)
  have hr : 0 < r := Real.sqrt_pos.mpr hs
  let u : Vector d := fun i => ℓ i / r
  have hu : dot u u = 1 := by
    have he : dot u u = dot ℓ ℓ / (r * r) := by
      simp only [u, dot, div_mul_div_comm, Finset.sum_div]
    rw [he, show r * r = dot ℓ ℓ from Real.mul_self_sqrt hs.le, div_self hs.ne']
  have htrans : DirectionallyTransient ν u := by
    apply (mem_ae_iff_prob_eq_one (measurableSet_transientPaths u)).mpr
    rw [transientPaths_div_pos ℓ hr]
    exact hprob
  obtain ⟨v, hvu, hv⟩ := directional_transience_implies_ballisticity_unit
    (by omega : 2 ≤ d) ν hue u hu htrans
  refine ⟨v, ?_, hv⟩
  have hp : 0 < dot v ℓ / r := by simpa only [u, dot_div_right] using hvu
  exact (div_pos_iff_of_pos_right hr).mp hp

lemma escape_probability_one_of_velocity {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (v u : Vector d) (hv : HasVelocity ν v)
    (hvu : 0 < dot v u) : annealedLaw ν (TransientPaths u) = 1 := by
  apply (mem_ae_iff_prob_eq_one (measurableSet_transientPaths u)).mp
  filter_upwards [hv] with X hX
  have hproj := velocityPaths_projection v u X hX
  have hprod := hproj.pos_mul_atTop hvu
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact div_mul_cancel₀ _ (by exact_mod_cast hn.ne')

lemma unit_direction_ne_zero {d : ℕ} (u : Vector d) (hu : dot u u = 1) : u ≠ 0 := by
  intro h
  subst u
  simp [dot] at hu

end DirectionalTransience

end OAI
