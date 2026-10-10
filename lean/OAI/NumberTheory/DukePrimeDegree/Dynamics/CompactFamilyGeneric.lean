import OAI.NumberTheory.DukePrimeDegree.Dynamics.RealFlowWindows
import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingMeasureLimits

namespace OAI

/-!
# A fixed generic set for a compact family of observables

The limiting shear is selected after the generic set. Compactness of the
possible shears gives a compact family of translated observables in the
uniform norm. A finite approximation therefore suffices for one common
generic set and time threshold. No commutation of the translating group
with the averaging flow is required.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction

namespace DukePrimeDegree

theorem exists_finite_uniform_real_flow_generic_set
    {Y I : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [MulAction (Multiplicative ℝ) Y] [ContinuousSMul (Multiplicative ℝ) Y]
    [Fintype I]
    (μ : Measure Y) [IsProbabilityMeasure μ] [ErgodicSMul (Multiplicative ℝ) Y μ]
    (f : I → Y →ᵇ ℝ) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ G : Set Y, MeasurableSet G ∧ μ Gᶜ ≤ ENNReal.ofReal δ ∧
      ∃ R : ℝ, 1 ≤ R ∧ ∀ x ∈ G, ∀ i, ∀ T ≥ R,
        |T⁻¹ * (∫ t in (0 : ℝ)..T, f i (realActionTime t x)) -
          ∫ y, f i y ∂μ| ≤ ε := by
  classical
  let a : ℝ := δ / (Fintype.card I + 1)
  have ha : 0 < a := div_pos hδ (by positivity)
  choose G hG hGμ R hR hgood using
    fun i => exists_uniform_real_flow_generic_set μ (f i) ε a hε ha
  let N := Finset.univ.sup (fun i => ⌈R i⌉₊)
  refine ⟨⋂ i, G i, MeasurableSet.iInter hG, ?_, max 1 (N : ℝ), le_max_left _ _, ?_⟩
  · rw [compl_iInter]
    calc
      μ (⋃ i, (G i)ᶜ) ≤ ∑ i, μ (G i)ᶜ := measure_iUnion_fintype_le μ _
      _ ≤ ∑ _i : I, ENNReal.ofReal a := Finset.sum_le_sum (fun i _ => hGμ i)
      _ = ENNReal.ofReal ((Fintype.card I : ℝ) * a) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => ha.le)]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ENNReal.ofReal δ := by
        apply ENNReal.ofReal_le_ofReal
        dsimp only [a]
        rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < Fintype.card I + 1)]
        nlinarith
  · intro x hx i T hT
    apply hgood i x (mem_iInter.mp hx i) T
    have hi : ⌈R i⌉₊ ≤ N := Finset.le_sup (f := fun i => ⌈R i⌉₊) (Finset.mem_univ i)
    have hi' : (⌈R i⌉₊ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hi
    exact (Nat.le_ceil (R i)).trans (hi'.trans
      ((le_max_right 1 (N : ℝ)).trans hT))

lemma flow_average_error_of_uniform_approximation
    {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [MulAction (Multiplicative ℝ) Y] [ContinuousSMul (Multiplicative ℝ) Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (f g : Y →ᵇ ℝ) (b ε : ℝ) (_hb : 0 ≤ b)
    (hfg : dist f g ≤ b) (x : Y) (T : ℝ) (hT : 0 < T)
    (hf : |T⁻¹ * (∫ t in (0 : ℝ)..T, f (realActionTime t x)) -
      ∫ y, f y ∂μ| ≤ ε) :
    |T⁻¹ * (∫ t in (0 : ℝ)..T, g (realActionTime t x)) -
      ∫ y, g y ∂μ| ≤ ε + 2 * b := by
  have hpoint (y : Y) : |f y - g y| ≤ b := by
    simpa only [Real.dist_eq] using
      (BoundedContinuousFunction.dist_coe_le_dist (f := f) (g := g) y).trans hfg
  have hmean : |(∫ y, f y ∂μ) - ∫ y, g y ∂μ| ≤ b := by
    rw [← integral_sub (f.integrable (μ := μ)) (g.integrable (μ := μ))]
    have h := norm_integral_le_of_norm_le_const (μ := μ)
      (f := fun y => f y - g y) (C := b)
      (ae_of_all _ (fun y => by simpa only [Real.norm_eq_abs] using hpoint y))
    have hμ : μ.real univ = 1 := by simp
    simpa only [Real.norm_eq_abs, hμ, mul_one] using h
  have hfi : IntervalIntegrable (fun t => f (realActionTime t x)) volume 0 T :=
    ((continuous_flow_observable f).comp
      (continuous_id.prodMk continuous_const)).intervalIntegrable 0 T
  have hgi : IntervalIntegrable (fun t => g (realActionTime t x)) volume 0 T :=
    ((continuous_flow_observable g).comp
      (continuous_id.prodMk continuous_const)).intervalIntegrable 0 T
  have havg : |T⁻¹ * (∫ t in (0 : ℝ)..T, f (realActionTime t x)) -
      T⁻¹ * (∫ t in (0 : ℝ)..T, g (realActionTime t x))| ≤ b := by
    rw [← mul_sub, ← intervalIntegral.integral_sub hfi hgi, abs_mul,
      abs_of_pos (inv_pos.mpr hT)]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun t => f (realActionTime t x) - g (realActionTime t x))
      (a := 0) (b := T) (C := b)
      (fun t _ => by simpa only [Real.norm_eq_abs] using hpoint (realActionTime t x))
    have h' : |∫ t in (0 : ℝ)..T,
        f (realActionTime t x) - g (realActionTime t x)| ≤ b * T := by
      simpa only [Real.norm_eq_abs, sub_zero, abs_of_pos hT] using h
    calc
      _ ≤ T⁻¹ * (b * T) := mul_le_mul_of_nonneg_left h' (inv_nonneg.mpr hT.le)
      _ = b := by field_simp
  have hd : T⁻¹ * (∫ t in (0 : ℝ)..T, g (realActionTime t x)) - ∫ y, g y ∂μ =
      (T⁻¹ * (∫ t in (0 : ℝ)..T, g (realActionTime t x)) -
        T⁻¹ * (∫ t in (0 : ℝ)..T, f (realActionTime t x))) +
      (T⁻¹ * (∫ t in (0 : ℝ)..T, f (realActionTime t x)) - ∫ y, f y ∂μ) +
      ((∫ y, f y ∂μ) - ∫ y, g y ∂μ) := by ring
  rw [hd]
  calc
    _ ≤ |T⁻¹ * (∫ t in (0 : ℝ)..T, g (realActionTime t x)) -
          T⁻¹ * (∫ t in (0 : ℝ)..T, f (realActionTime t x))| +
        |T⁻¹ * (∫ t in (0 : ℝ)..T, f (realActionTime t x)) - ∫ y, f y ∂μ| +
        |(∫ y, f y ∂μ) - ∫ y, g y ∂μ| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ b + ε + b := add_le_add
      (add_le_add (by simpa only [abs_sub_comm] using havg) hf) hmean
    _ = ε + 2 * b := by ring

/-- Compactness is in the uniform norm on bounded continuous functions. -/
theorem exists_compact_family_real_flow_generic_set
    {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [MulAction (Multiplicative ℝ) Y] [ContinuousSMul (Multiplicative ℝ) Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] [ErgodicSMul (Multiplicative ℝ) Y μ]
    (K : Set (Y →ᵇ ℝ)) (hK : IsCompact K)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ G : Set Y, MeasurableSet G ∧ μ Gᶜ ≤ ENNReal.ofReal δ ∧
      ∃ R : ℝ, 1 ≤ R ∧ ∀ x ∈ G, ∀ f ∈ K, ∀ T ≥ R,
        |T⁻¹ * (∫ t in (0 : ℝ)..T, f (realActionTime t x)) -
          ∫ y, f y ∂μ| ≤ ε := by
  classical
  obtain ⟨J, hJ⟩ := hK.elim_finite_subcover
    (fun f : K => Metric.ball f.val (ε / 4)) (fun _ => Metric.isOpen_ball)
    (fun f hf => mem_iUnion.mpr ⟨⟨f, hf⟩, Metric.mem_ball_self (by positivity)⟩)
  obtain ⟨G, hG, hGμ, R, hR, hgood⟩ :=
    exists_finite_uniform_real_flow_generic_set μ
      (fun i : J => i.val.val) (ε / 2) δ (by positivity) hδ
  refine ⟨G, hG, hGμ, R, hR, ?_⟩
  intro x hx f hf T hT
  obtain ⟨g, hg, hfg⟩ := mem_iUnion₂.mp (hJ hf)
  have hdist : dist g.val f ≤ ε / 4 := by
    simpa only [dist_comm] using (Metric.mem_ball.mp hfg).le
  have h := flow_average_error_of_uniform_approximation μ g.val f
    (ε / 4) (ε / 2) (by positivity) hdist x T
    (lt_of_lt_of_le zero_lt_one (hR.trans hT)) (hgood x hx ⟨g, hg⟩ T hT)
  linarith

def compactObservableTranslate
    {H Y : Type*} [Group H] [TopologicalSpace H] [TopologicalSpace Y]
    [MulAction H Y] [ContinuousSMul H Y]
    (f : CompactlySupportedContinuousMap Y ℝ) (a : H) : Y →ᵇ ℝ :=
  f.toBoundedContinuousFunction.compContinuous ⟨fun x => a • x, continuous_const_smul a⟩

theorem continuous_compactObservableTranslate
    {H Y : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [WeaklyLocallyCompactSpace H] [TopologicalSpace Y]
    [MulAction H Y] [ContinuousSMul H Y]
    (f : CompactlySupportedContinuousMap Y ℝ) :
    Continuous (compactObservableTranslate (H := H) f) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  apply BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mpr
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [compact_observable_varying_smul f f.continuous f.hasCompactSupport
    (id : H → H) a tendsto_id ε hε] with b hb x
  simpa only [compactObservableTranslate, BoundedContinuousFunction.compContinuous_apply,
    ContinuousMap.coe_mk, CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply,
    id_eq, Real.dist_eq, abs_sub_comm] using hb x

/-- The translating element may be any later-selected point of a fixed
compact set. It is unrelated to the real averaging flow. -/
theorem exists_compact_translate_real_flow_generic_set
    {H Y : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [WeaklyLocallyCompactSpace H] [TopologicalSpace Y]
    [MulAction H Y] [ContinuousSMul H Y]
    [MeasurableSpace Y] [BorelSpace Y]
    [MulAction (Multiplicative ℝ) Y] [ContinuousSMul (Multiplicative ℝ) Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] [ErgodicSMul (Multiplicative ℝ) Y μ]
    (f : CompactlySupportedContinuousMap Y ℝ) (K : Set H) (hK : IsCompact K)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ G : Set Y, MeasurableSet G ∧ μ Gᶜ ≤ ENNReal.ofReal δ ∧
      ∃ R : ℝ, 1 ≤ R ∧ ∀ x ∈ G, ∀ a ∈ K, ∀ T ≥ R,
        |T⁻¹ * (∫ t in (0 : ℝ)..T, f (a • realActionTime t x)) -
          ∫ y, f (a • y) ∂μ| ≤ ε := by
  obtain ⟨G, hG, hGμ, R, hR, hgood⟩ :=
    exists_compact_family_real_flow_generic_set μ
      (compactObservableTranslate f '' K)
      (hK.image (continuous_compactObservableTranslate f)) ε δ hε hδ
  refine ⟨G, hG, hGμ, R, hR, ?_⟩
  intro x hx a ha T hT
  exact hgood x hx (compactObservableTranslate f a) ⟨a, ha, rfl⟩ T hT

end DukePrimeDegree

end

end OAI
