import OAI.Probability.SLE.Loewner.TargetCutoffTrajectory
import OAI.Probability.SLE.Loewner.TargetDriverContinuation

namespace OAI

/-! Joint measurability and finite-prefix dependence of the prescribed
cutoff flow. The variable initial point is encoded as a displacement in
the already constructed measurable Picard equation. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Target

lemma measurable_cutoffField (κ : ℝ) (j : ℕ) :
    Measurable (fun q : (ℝ × Driver) × ℂ => cutoffField κ q.1.2 j q.1.1 q.2) := by
  have hb : Measurable (fun q : (ℝ × Driver) × ℂ =>
      q.1.2 q.1.1.toNNReal) :=
    continuous_eval.measurable.comp ((measurable_snd.comp measurable_fst).prodMk
      (continuous_real_toNNReal.measurable.comp (measurable_fst.comp measurable_fst)))
  have hv : Measurable (fun q : (ℝ × Driver) × ℂ =>
      q.2 - (q.1.2 q.1.1.toNNReal : ℂ)) := measurable_snd.sub hb.complex_ofReal
  exact (measurable_const.mul (Complex.continuous_conj.measurable.comp hv)).div
    ((hv.norm.pow_const 2).max measurable_const).complex_ofReal

lemma measurable_cutoffFlow (κ : ℝ) (j : ℕ) (hj : 1 ≤ j) :
    Measurable (fun q : ℝ≥0 × (Driver × ℂ) => cutoffFlow κ q.2.1 j q.2.2 q.1) := by
  obtain ⟨L,K,hL,hK⟩ := cutoffField_bounds κ j hj
  let V (t : ℝ) (x : Driver × ℂ) (v : ℂ) := cutoffField κ x.1 j t (v+x.2)
  have hV : Measurable (fun q : (ℝ × (Driver × ℂ)) × ℂ => V q.1.1 q.1.2 q.2) := by
    have hpair : Measurable (fun q : (ℝ × (Driver × ℂ)) × ℂ =>
        ((q.1.1,q.1.2.1),q.2+q.1.2.2)) :=
      ((measurable_fst.fst.prodMk measurable_fst.snd.fst).prodMk
        (measurable_snd.add measurable_fst.snd.snd))
    exact @Measurable.comp ((ℝ × (Driver × ℂ)) × ℂ) ((ℝ × Driver) × ℂ) ℂ
      inferInstance inferInstance inferInstance
      (fun q => cutoffField κ q.1.2 j q.1.1 q.2)
      (fun q => ((q.1.1,q.1.2.1),q.2+q.1.2.2)) (measurable_cutoffField κ j) hpair
  have hc (x : Driver × ℂ) (v : ℂ) : Continuous (fun t => V t x v) :=
    (continuous_cutoffField κ x.1 j hj).comp (continuous_id.prodMk continuous_const)
  have hl (x : Driver × ℂ) (t : ℝ) : LipschitzWith K (V t x) := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    simpa only [V,dist_add_right] using (hK x.1 t).dist_le_mul (v+x.2) (w+x.2)
  obtain ⟨X,hXm,hXl,hX0,hXd,_⟩ := exists_measurable_global_bounded_ode_picard
    V 0 L K hV hc hl (fun x t v => hL x.1 t (v+x.2))
  have he (t : ℝ≥0) (x : Driver × ℂ) :
      cutoffFlow κ x.1 j x.2 t = X t x+x.2 := by
    apply cutoffFlow_eq_solution κ x.1 j hj x.2 L K (hL x.1) (hK x.1)
      (fun s => X s x+x.2) ((hXl x).continuous.add continuous_const)
    · simp only [hX0,zero_add]
    · intro s hs
      simpa only [V] using (hXd x s hs).add_const x.2
    · exact t.coe_nonneg
  have hm : Measurable (fun q : ℝ≥0 × (Driver × ℂ) => X q.1 q.2+q.2.2) :=
    (hXm.comp (measurable_fst.coe_nnreal_real.prodMk measurable_snd)).add measurable_snd.snd
  convert hm using 1
  exact funext (fun q => he q.1 q.2)

def stopDriver (b : Driver) (T : ℝ≥0) : Driver where
  toFun t := b (min t T)
  continuous_toFun := (map_continuous b).comp (continuous_id.min continuous_const)
  map_zero' := by simp

@[simp] lemma stopDriver_apply (b : Driver) (T t : ℝ≥0) :
    stopDriver b T t = b (min t T) := rfl

lemma stopDriver_measurable_past (T : ℝ≥0) :
    Measurable[driverFiltration T] (fun b => stopDriver b T) := by
  have hm (t : ℝ≥0) : Measurable[driverFiltration T]
      (fun b : Driver => b (min t T)) :=
    ((Filtration.stronglyAdapted_natural
      (fun u => (show Measurable (fun b : Driver => b u) from
        (continuous_eval_const u).measurable).stronglyMeasurable) (min t T)).measurable).mono
          (driverFiltration.mono (min_le_right t T)) le_rfl
  apply ContinuousMapZero.isClosedEmbedding_toContinuousMap.measurableEmbedding.measurable_comp_iff.mp
  let : MeasurableSpace Driver := driverFiltration T
  apply source_path_measurable
  intro t
  exact hm t

lemma cutoffFlow_eq_of_driver_prefix (κ : ℝ) (b c : Driver) (j : ℕ) (hj : 1 ≤ j)
    (z : ℂ) (T : ℝ) (hT : 0 ≤ T)
    (he : ∀ s ∈ Icc 0 T, driverValue b s = driverValue c s) :
    ∀ t ∈ Icc 0 T, cutoffFlow κ b j z t = cutoffFlow κ c j z t := by
  apply cutoffFlow_eq_of_trajectory κ b j hj z T hT (cutoffFlow κ c j z)
    ((cutoffFlow_continuousOn κ c j hj z).mono Icc_subset_Ici_self)
    (cutoffFlow_zero κ c j hj z)
  intro s hs
  have hv : cutoffField κ b j s (cutoffFlow κ c j z s) =
      cutoffField κ c j s (cutoffFlow κ c j z s) := by
    simp only [cutoffField,he s (Ico_subset_Icc_self hs)]
  rw [hv]
  exact (cutoffFlow_hasDerivWithinAt κ c j hj z s hs.1).mono
    (Ici_subset_Ici.mpr hs.1)

lemma cutoffFlow_stopDriver (κ : ℝ) (b : Driver) (j : ℕ) (hj : 1 ≤ j)
    (z : ℂ) (T : ℝ≥0) (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    cutoffFlow κ (stopDriver b T) j z t = cutoffFlow κ b j z t := by
  apply cutoffFlow_eq_of_driver_prefix κ _ _ j hj z T T.coe_nonneg ?_ t ht
  intro s hs
  simp only [driverValue,stopDriver_apply,
    min_eq_left ((Real.toNNReal_le_iff_le_coe).mpr hs.2)]

lemma cutoffFlow_measurable_past (κ : ℝ) (j : ℕ) (hj : 1 ≤ j) (T t : ℝ≥0)
    (ht : t ≤ T) :
    Measurable[(driverFiltration T).prod (borel ℂ)]
      (fun q : Driver × ℂ => cutoffFlow κ q.1 j q.2 t) := by
  have hpair : Measurable[(driverFiltration T).prod (borel ℂ)]
      (fun q : Driver × ℂ => (t,(stopDriver q.1 T,q.2))) :=
    measurable_const.prodMk (((stopDriver_measurable_past T).comp measurable_fst).prodMk
      measurable_snd)
  have hm : Measurable[(driverFiltration T).prod (borel ℂ)]
      (fun q : Driver × ℂ => cutoffFlow κ (stopDriver q.1 T) j q.2 t) :=
    @Measurable.comp (Driver × ℂ) (ℝ≥0 × (Driver × ℂ)) ℂ
      ((driverFiltration T).prod (borel ℂ)) inferInstance inferInstance
      (fun q => cutoffFlow κ q.2.1 j q.2.2 q.1)
      (fun q => (t,(stopDriver q.1 T,q.2))) (measurable_cutoffFlow κ j hj) hpair
  convert hm using 1
  exact funext (fun q => (cutoffFlow_stopDriver κ q.1 j hj q.2 T t
    ⟨t.coe_nonneg,show (t : ℝ) ≤ T from ht⟩).symm)

end SLEExactGauge.Target

end

end OAI
