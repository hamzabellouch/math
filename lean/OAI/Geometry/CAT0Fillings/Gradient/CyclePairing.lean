import Mathlib
import OAI.Geometry.CAT0Fillings.Gradient.Pairing

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology ENNReal NNReal BigOperators

namespace CAT0Fillings

lemma BoundedLip.memLp {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] {μ : Measure X} [IsFiniteMeasure μ] {u : X → ℝ}
    (hu : BoundedLip u) (p : ℝ≥0∞) : MemLp u p μ := by
  obtain ⟨K,hK⟩ := hu.1
  obtain ⟨B,hB⟩ := hu.2
  exact MemLp.of_bound hK.continuous.aestronglyMeasurable B
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hB x)

namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

include q in
lemma integerRectifiable : IntegerRectifiable T :=
  ⟨q.chart,q.disjoint,q.current,q.summable,q.action⟩

lemma abs_pairing_gradient_cycle_le (hz : IsCycle T)
    (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hπ : ∀ j, LipschitzWith (K j) (π j)) {b u : X → ℝ} {Kb Ku : ℝ≥0}
    (hb : LipschitzWith Kb b) (hu : LipschitzWith Ku u) :
    |q.pairing π b (q.gradient hu)| ≤
      ((Kb : ℝ)*(∏ j, (K j : ℝ))*Real.sqrt ((MassMeasure.currentMassMeasure hT).real univ))*
        lpNorm u 2 (MassMeasure.currentMassMeasure hT) := by
  have hb' := Foundations.boundedLip_of_lipschitz hb
  have hu' := Foundations.boundedLip_of_lipschitz hu
  rw [q.pairing_gradient π K hπ hu hb']
  change |T b (Matrix.vecCons u π)| ≤ _
  rw [Foundations.IntegerRectifiable.cycle_product_rule q.integerRectifiable hz hb' hu' π
      (fun j => ⟨K j,hπ j⟩),abs_neg]
  have hKs : ∀ j, LipschitzWith (Matrix.vecCons Kb K j) (Matrix.vecCons b π j) := by
    intro j
    refine Fin.cases ?_ (fun a => ?_) j
    · exact hb
    · exact hπ a
  have hh := hT.mass_bound (MassMeasure.currentMassMeasure_controls hT) hu' (Matrix.vecCons Kb K) hKs
  have hm : (∏ j, ((Matrix.vecCons Kb K j : ℝ≥0) : ℝ)) = (Kb : ℝ)*∏ j, (K j : ℝ) := by
    rw [Fin.prod_univ_succ]; rfl
  rw [hm] at hh
  have h1 := integral_norm_le_lpNorm_two (hu'.memLp (μ := MassMeasure.currentMassMeasure hT) 2)
  simp only [Real.norm_eq_abs] at h1
  exact (hh.trans (mul_le_mul_of_nonneg_left h1
    (mul_nonneg Kb.coe_nonneg (Finset.prod_nonneg fun j _ => (K j).coe_nonneg)))).trans_eq (by ring)

lemma pairing_eq_zero_of_gradient_limit (hz : IsCycle T)
    (u : ℕ → X → ℝ) (Ku : ℕ → ℝ≥0) (hu : ∀ j, LipschitzWith (Ku j) (u j))
    (hu0 : Tendsto (fun j => lpNorm (u j) 2 (MassMeasure.currentMassMeasure hT)) atTop (𝓝 0))
    (L : Lp (Euc (k+1)) 2 q.atlasMeasure)
    (hL : Tendsto (fun j => q.gradient (hu j)) atTop (𝓝 L))
    (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hπ : ∀ j, LipschitzWith (K j) (π j)) {b : X → ℝ} (hb : BoundedLip b) :
    q.pairing π b L = 0 := by
  obtain ⟨Kb,hbK⟩ := hb.1
  have hh : Tendsto (fun j => q.pairing π b (q.gradient (hu j))) atTop (𝓝 0) := by
    have hbound (j : ℕ) : ‖q.pairing π b (q.gradient (hu j))‖ ≤
        ((Kb : ℝ)*(∏ i, (K i : ℝ))*Real.sqrt ((MassMeasure.currentMassMeasure hT).real univ))*
          lpNorm (u j) 2 (MassMeasure.currentMassMeasure hT) := by
      exact q.abs_pairing_gradient_cycle_le hz π K hπ hbK (hu j)
    apply squeeze_zero_norm hbound
    simpa only [mul_zero] using hu0.const_mul
      ((Kb : ℝ)*(∏ j, (K j : ℝ))*Real.sqrt ((MassMeasure.currentMassMeasure hT).real univ))
  exact tendsto_nhds_unique ((q.continuous_pairing π K hπ hb).tendsto L |>.comp hL) hh

lemma testWeight_eq_zero_of_pairings (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hπ : ∀ j, LipschitzWith (K j) (π j)) (L : Lp (Euc (k+1)) 2 q.atlasMeasure)
    (hnull : ∀ b, BoundedLip b → q.pairing π b L = 0) :
    q.testWeight π L =ᵐ[q.atlasMeasure] 0 := by
  have hi := (q.memLp_testWeight π K hπ (Lp.memLp L)).integrable (by norm_num)
  have hdom := signed_chart_control_dominates_on q.atlasMeasure (0 : Measure X)
    q.measurable_atlasParam q.ae_mem_atlasDomain q.measurableEmbedding_atlas hi
    (fun b hb => by change |q.pairing π b L| ≤ _; simp [hnull b hb])
  have he : densityPush q.atlasMeasure q.atlasParam (fun w => |q.testWeight π L w|) = 0 :=
    le_antisymm hdom bot_le
  have ht := congrArg (fun μ : Measure X => μ univ) he
  simp only [densityPush,Measure.map_apply q.measurable_atlasParam MeasurableSet.univ,
    preimage_univ,withDensity_apply _ MeasurableSet.univ,Measure.coe_zero,Pi.zero_apply,Measure.restrict_univ] at ht
  have hw := (lintegral_eq_zero_iff' hi.aestronglyMeasurable.aemeasurable.abs.ennreal_ofReal).mp ht
  filter_upwards [hw] with w hw
  simpa only [Pi.zero_apply,ENNReal.ofReal_eq_zero,abs_nonpos_iff] using hw

end ChartGeometry
end CAT0Fillings
end

section

open Set Filter MeasureTheory Matrix
open scoped Topology ENNReal NNReal BigOperators

namespace CAT0Fillings

lemma vecCons_omitted_rows {n : ℕ} (v : Fin (n+1) → ℝ) (j : Fin (n+1)) :
    Matrix.vecCons v (fun a => (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
      (Equiv.swap 0 j a.succ)) =
    (((1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ).updateRow j v).submatrix
      (Equiv.swap 0 j) id) := by
  ext a b
  refine Fin.cases ?_ (fun a => ?_) a
  · simp [Matrix.submatrix_apply,Matrix.updateRow_apply]
  · have hne : Equiv.swap 0 j a.succ ≠ j := by
      intro h
      have he : Equiv.swap 0 j a.succ = Equiv.swap 0 j 0 := by simpa using h
      exact Fin.succ_ne_zero a ((Equiv.swap 0 j).injective he)
    simp [Matrix.submatrix_apply,Matrix.updateRow_apply,hne]

lemma component_zero_of_omitted_det {n : ℕ} (v : Fin (n+1) → ℝ) (j : Fin (n+1))
    (h : Matrix.det (Matrix.vecCons v (fun a =>
      (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (Equiv.swap 0 j a.succ))) = 0) : v j = 0 := by
  rw [vecCons_omitted_rows,Matrix.det_permute,det_updateRow_identity] at h
  have hh := congrArg abs h
  simp only [abs_mul,abs_unit_intCast,one_mul,abs_zero] at hh
  exact abs_eq_zero.mp hh

end CAT0Fillings
end

end OAI
