import OAI.MeasureTheory.Falconer.Angular.SphereCapBound
import OAI.MeasureTheory.Falconer.Measures.TestNormRepresentation
import OAI.MeasureTheory.Falconer.Measures.TestNormMeasurable
import OAI.MeasureTheory.Falconer.Measures.TestNormDensity
import OAI.MeasureTheory.Falconer.Radial.RadonLpDensity

namespace OAI

/-! Continuous test norms against the actual ambient surface measure.
These measure-duality lemmas match the published radial pushforward directly. -/

namespace Falconer
open Set MeasureTheory Filter PlanarFalconer
open scoped ENNReal NNReal Topology
variable {d : ℕ}

noncomputable def surfaceTestNorm (q : ℝ) (γ : Measure (Space (d+1))) : ℝ≥0∞ :=
  ⨆ (F : BoundedContinuousFunction (Space (d+1)) ℝ)
    (_ : eLpNorm F (ENNReal.ofReal q) (surfaceMeasure (d+1)) ≤ 1),
      ENNReal.ofReal ‖∫ w, F w ∂γ‖


theorem surfaceTestNorm_test_bound (γ : Measure (Space (d+1))) [IsFiniteMeasure γ]
    {q : ℝ} (hN : surfaceTestNorm q γ ≠ ∞)
    (F : BoundedContinuousFunction (Space (d+1)) ℝ) :
    ‖∫ ω, F ω ∂γ‖ ≤ (surfaceTestNorm q γ).toReal *
      (eLpNorm F (ENNReal.ofReal q) (surfaceMeasure (d+1))).toReal := by
  have hf : MemLp F (ENNReal.ofReal q) (surfaceMeasure (d+1)) :=
    (memLp_top_of_bound F.continuous.aestronglyMeasurable ‖F‖
      (Eventually.of_forall F.norm_coe_le_norm)).mono_exponent le_top
  have haux (a : ℝ) (ha : (eLpNorm F (ENNReal.ofReal q) (surfaceMeasure (d+1))).toReal < a) :
      ‖∫ ω, F ω ∂γ‖ ≤ (surfaceTestNorm q γ).toReal * a := by
    have ha0 : 0 < a := lt_of_le_of_lt ENNReal.toReal_nonneg ha
    let G : BoundedContinuousFunction (Space (d+1)) ℝ := a⁻¹ • F
    have hG : eLpNorm G (ENNReal.ofReal q) (surfaceMeasure (d+1)) ≤ 1 := by
      change eLpNorm (a⁻¹ • (F : (Space (d+1)) → ℝ)) _ _ ≤ _
      rw [eLpNorm_const_smul]
      have hn : eLpNorm F (ENNReal.ofReal q) (surfaceMeasure (d+1)) ≤ ENNReal.ofReal a :=
        (ENNReal.le_ofReal_iff_toReal_le hf.eLpNorm_ne_top ha0.le).mpr ha.le
      calc
        ‖a⁻¹‖ₑ * eLpNorm F (ENNReal.ofReal q) (surfaceMeasure (d+1)) ≤
            ENNReal.ofReal a⁻¹ * ENNReal.ofReal a := by
          rw [← ofReal_norm, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha0)]
          exact mul_le_mul_right hn _
        _ = 1 := by rw [← ENNReal.ofReal_mul (inv_nonneg.mpr ha0.le), inv_mul_cancel₀ ha0.ne', ENNReal.ofReal_one]
    have hb : ENNReal.ofReal ‖∫ ω, G ω ∂γ‖ ≤ surfaceTestNorm q γ :=
      le_iSup_of_le G (le_iSup_of_le hG le_rfl)
    have hb' := (ENNReal.ofReal_le_iff_le_toReal hN).mp hb
    change ‖∫ ω, a⁻¹ • F ω ∂γ‖ ≤ _ at hb'
    rw [integral_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha0)] at hb'
    calc
      ‖∫ ω, F ω ∂γ‖ = a * (a⁻¹ * ‖∫ ω, F ω ∂γ‖) := by
        rw [← mul_assoc, mul_inv_cancel₀ ha0.ne', one_mul]
      _ ≤ a * (surfaceTestNorm q γ).toReal := mul_le_mul_of_nonneg_left hb' ha0.le
      _ = _ := mul_comm _ _
  apply ge_of_tendsto (f := fun a : ℝ => (surfaceTestNorm q γ).toReal * a)
    ((continuous_const.mul continuous_id).continuousAt.tendsto.mono_left
      (show 𝓝[>] (eLpNorm F (ENNReal.ofReal q) (surfaceMeasure (d+1))).toReal ≤
        𝓝 (eLpNorm F (ENNReal.ofReal q) (surfaceMeasure (d+1))).toReal from nhdsWithin_le_nhds))
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact haux a ha



theorem surfaceTestNorm_measurable_test_bound (γ : Measure (Space (d+1))) [IsFiniteMeasure γ]
    {q : ℝ} (hq : 1 ≤ q) (hN : surfaceTestNorm q γ ≠ ∞)
    (f : (Space (d+1)) → ℝ) (hf : MemLp f (ENNReal.ofReal q) (γ + (surfaceMeasure (d+1)))) :
    ‖∫ ω, f ω ∂γ‖ ≤ (surfaceTestNorm q γ).toReal *
      (eLpNorm f (ENNReal.ofReal q) (surfaceMeasure (d+1))).toReal := by
  let μ := γ + (surfaceMeasure (d+1))
  let Q := ENNReal.ofReal q
  have hQ : 1 ≤ Q := by simpa [Q] using ENNReal.ofReal_le_ofReal hq
  let : Fact (1 ≤ Q) := ⟨hQ⟩
  have hγ : γ ≤ μ := le_add_of_nonneg_right bot_le
  have hν : (surfaceMeasure (d+1)) ≤ μ := le_add_of_nonneg_left bot_le
  have hν' : (surfaceMeasure (d+1)) ≤ (1 : ℝ≥0∞) • μ := by simpa using hν
  let R : Lp ℝ Q μ →L[ℝ] Lp ℝ Q (surfaceMeasure (d+1)) :=
    Lp.LpToLpOfMeasureLeSMul ENNReal.one_ne_top hν'
  have hR (g : Lp ℝ Q μ) : R g =ᵐ[(surfaceMeasure (d+1))] g :=
    Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.one_ne_top hν' g
  have hd := BoundedContinuousFunction.toLp_denseRange ℝ μ ℝ (show Q ≠ ∞ from ENNReal.ofReal_ne_top)
  have hclosed : IsClosed {g : Lp ℝ Q μ | ‖∫ ω, g ω ∂γ‖ ≤
      (surfaceTestNorm q γ).toReal * ‖R g‖} :=
    isClosed_le (continuous_integral_Lp_of_le γ μ hγ hQ).norm
      (continuous_const.mul R.continuous.norm)
  have hall (g : Lp ℝ Q μ) : ‖∫ ω, g ω ∂γ‖ ≤ (surfaceTestNorm q γ).toReal * ‖R g‖ := by
    apply (hclosed.closure_subset_iff (s := Set.range (BoundedContinuousFunction.toLp Q μ ℝ))).mpr ?_ (hd g)
    rintro _ ⟨F, rfl⟩
    have hF := BoundedContinuousFunction.coeFn_toLp Q μ ℝ F
    have hi := integral_congr_ae (hγ.absolutelyContinuous.ae_eq hF)
    have hn : ‖R (BoundedContinuousFunction.toLp Q μ ℝ F)‖ =
        (eLpNorm F Q (surfaceMeasure (d+1))).toReal := by
      rw [Lp.norm_def, eLpNorm_congr_ae ((hR _).trans (hν.absolutelyContinuous.ae_eq hF))]
    change ‖∫ ω, (BoundedContinuousFunction.toLp Q μ ℝ F) ω ∂γ‖ ≤ _
    rw [hi, hn]
    exact surfaceTestNorm_test_bound γ hN F
  have hg := hall (hf.toLp f)
  have he := hf.coeFn_toLp
  rw [integral_congr_ae (hγ.absolutelyContinuous.ae_eq he)] at hg
  have hn : ‖R (hf.toLp f)‖ = (eLpNorm f Q (surfaceMeasure (d+1))).toReal := by
    rw [Lp.norm_def, eLpNorm_congr_ae ((hR _).trans (hν.absolutelyContinuous.ae_eq he))]
  rwa [hn] at hg

theorem surfaceTestNorm_absolutelyContinuous (γ : Measure (Space (d+1))) [IsFiniteMeasure γ]
    {q : ℝ} (hq : 1 ≤ q) (hN : surfaceTestNorm q γ ≠ ∞) : γ ≪ (surfaceMeasure (d+1)) := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hνs
  let f : (Space (d+1)) → ℝ := s.indicator (fun _ => 1)
  have hf : MemLp f (ENNReal.ofReal q) (γ + (surfaceMeasure (d+1))) :=
    memLp_indicator_const _ hs _ (Or.inr (measure_ne_top _ _))
  have hb := surfaceTestNorm_measurable_test_bound γ hq hN f hf
  have he : f =ᵐ[(surfaceMeasure (d+1))] 0 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hνs] with x hx
    exact Set.indicator_of_notMem hx _
  rw [eLpNorm_congr_ae he, eLpNorm_zero, ENNReal.toReal_zero, mul_zero] at hb
  have hi : (∫ x, f x ∂γ) = (γ s).toReal := by
    simp [f, integral_indicator hs, measureReal_def]
  rw [hi, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] at hb
  exact ((ENNReal.toReal_eq_zero_iff _).mp (le_antisymm hb ENNReal.toReal_nonneg)).resolve_right
    (measure_ne_top γ s)



theorem surfaceTestNorm_bounded_density_lower (γ : Measure (Space (d+1))) [IsFiniteMeasure γ]
    {p q : ℝ} (hpq : p.HolderConjugate q) (hN : surfaceTestNorm q γ ≠ ∞)
    (F : (Space (d+1)) → ℝ≥0∞) (hF : Measurable F) {B : ℝ≥0∞}
    (hB : B ≠ ∞) (hFB : ∀ x, F x ≤ B)
    (hFR : ∀ᵐ x ∂(surfaceMeasure (d+1)), F x ≤ γ.rnDeriv (surfaceMeasure (d+1)) x) :
    (∫⁻ x, F x^p ∂(surfaceMeasure (d+1)))^(1/p) ≤ surfaceTestNorm q γ := by
  let : γ.HaveLebesgueDecomposition (surfaceMeasure (d+1)) :=
    Measure.haveLebesgueDecomposition_of_finiteMeasure
  have hq : 1 ≤ q := (Real.holderConjugate_iff.mp hpq.symm).1.le
  have hAC := surfaceTestNorm_absolutelyContinuous γ hq hN
  have hmass : (∫⁻ x, F x^p ∂(surfaceMeasure (d+1))) ≠ ∞ := by
    apply ne_of_lt
    calc
      (∫⁻ x, F x^p ∂(surfaceMeasure (d+1))) ≤ ∫⁻ _, B^p ∂(surfaceMeasure (d+1)) :=
        lintegral_mono (fun x => ENNReal.rpow_le_rpow (hFB x) hpq.nonneg)
      _ < ∞ := by
        rw [lintegral_const]
        exact ENNReal.mul_lt_top (ENNReal.rpow_ne_top_of_nonneg hpq.nonneg hB).lt_top
          (measure_lt_top (surfaceMeasure (d+1)) univ)
  by_cases hzero : (∫⁻ x, F x^p ∂(surfaceMeasure (d+1))) = 0
  · rw [hzero, ENNReal.zero_rpow_of_pos (one_div_pos.mpr hpq.pos)]
    exact bot_le
  obtain ⟨h, hh, ⟨C, hC, hhC⟩, hnorm, hpair⟩ :=
    exists_bounded_normalized_dual_density (surfaceMeasure (d+1)) F hF hpq hB hFB hzero hmass
  have hht (x : (Space (d+1))) : h x ≠ ∞ := ne_of_lt ((hhC x).trans_lt hC.lt_top)
  have hen (x : (Space (d+1))) : ‖(h x).toReal‖ₑ = h x := by
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (hht x)]
  have hm : MemLp (fun x => (h x).toReal) (ENNReal.ofReal q) (γ + (surfaceMeasure (d+1))) :=
    (memLp_top_of_bound hh.ennreal_toReal.aestronglyMeasurable C.toReal
      (Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
        exact ENNReal.toReal_mono hC (hhC x)))).mono_exponent le_top
  have hn : eLpNorm (fun x => (h x).toReal) (ENNReal.ofReal q) (surfaceMeasure (d+1)) = 1 := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hpq.symm.pos).ne'
      ENNReal.ofReal_ne_top hh.ennreal_toReal.aestronglyMeasurable,
      ENNReal.toReal_ofReal hpq.symm.nonneg]
    simp_rw [hen]
    rw [hnorm, ENNReal.one_rpow]
  have hb := surfaceTestNorm_measurable_test_bound γ hq hN (fun x => (h x).toReal) hm
  rw [hn, ENNReal.toReal_one, mul_one] at hb
  have hi : Integrable (fun x => (h x).toReal) γ :=
    (hm.mono_measure (le_add_of_nonneg_right bot_le)).integrable
      (by simpa using ENNReal.ofReal_le_ofReal hq)
  have hlin : (∫⁻ x, h x ∂γ) ≤ surfaceTestNorm q γ := by
    have he : ENNReal.ofReal ‖∫ x, (h x).toReal ∂γ‖ = ∫⁻ x, h x ∂γ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => ENNReal.toReal_nonneg)),
        ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))]
      exact lintegral_congr (fun x => ENNReal.ofReal_toReal (hht x))
    rw [← he]
    exact (ENNReal.ofReal_le_iff_le_toReal hN).mpr hb
  rw [← hpair]
  calc
    (∫⁻ x, F x * h x ∂(surfaceMeasure (d+1))) ≤
        ∫⁻ x, γ.rnDeriv (surfaceMeasure (d+1)) x * h x ∂(surfaceMeasure (d+1)) :=
      lintegral_mono_ae (hFR.mono (fun x hx => mul_le_mul_left hx _))
    _ = ∫⁻ x, h x ∂γ := by
      have he := lintegral_withDensity_eq_lintegral_mul (surfaceMeasure (d+1))
        (Measure.measurable_rnDeriv γ (surfaceMeasure (d+1))) hh
      rw [Measure.withDensity_rnDeriv_eq γ (surfaceMeasure (d+1)) hAC] at he
      exact he.symm
    _ ≤ _ := hlin



theorem surfaceTestNorm_rnDeriv_eLpNorm_le (γ : Measure (Space (d+1))) [IsFiniteMeasure γ]
    {p q : ℝ} (hpq : p.HolderConjugate q) (hN : surfaceTestNorm q γ ≠ ∞) :
    eLpNorm (fun x => (γ.rnDeriv (surfaceMeasure (d+1)) x).toReal) (ENNReal.ofReal p) (surfaceMeasure (d+1)) ≤
      surfaceTestNorm q γ := by
  let R := γ.rnDeriv (surfaceMeasure (d+1))
  let F : ℕ → (Space (d+1)) → ℝ := fun n x => min (R x).toReal n
  have hm (n : ℕ) : Measurable (F n) :=
    (Measure.measurable_rnDeriv γ (surfaceMeasure (d+1))).ennreal_toReal.min measurable_const
  have hpos (n : ℕ) (x : (Space (d+1))) : 0 ≤ F n x :=
    le_min ENNReal.toReal_nonneg (Nat.cast_nonneg _)
  have hb (n : ℕ) : eLpNorm (F n) (ENNReal.ofReal p) (surfaceMeasure (d+1)) ≤ surfaceTestNorm q γ := by
    have h := surfaceTestNorm_bounded_density_lower γ hpq hN
      (fun x => ENNReal.ofReal (F n x)) (hm n).ennreal_ofReal ENNReal.ofReal_ne_top
      (fun x => ENNReal.ofReal_le_ofReal (min_le_right _ _))
      (Eventually.of_forall (fun x =>
        (ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans (ENNReal.ofReal_toReal_le)))
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hpq.pos).ne'
      ENNReal.ofReal_ne_top (hm n).aestronglyMeasurable,
      ENNReal.toReal_ofReal hpq.nonneg]
    simpa only [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hpos n _)] using h
  apply Lp.eLpNorm_le_of_ae_tendsto (u := atTop) (Eventually.of_forall hb)
    (fun index => (hm index).aestronglyMeasurable)
    (Measure.measurable_rnDeriv γ (surfaceMeasure (d+1))).ennreal_toReal.aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  obtain ⟨n, hn⟩ := exists_nat_ge (R x).toReal
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop n] with m hm
  exact (min_eq_left (hn.trans (by exact_mod_cast hm))).symm

theorem surfaceTestNorm_exists_Lp_density (γ : Measure (Space (d+1))) [IsFiniteMeasure γ]
    {p q : ℝ} (hpq : p.HolderConjugate q) (hN : surfaceTestNorm q γ ≠ ∞) :
    ∃ g : (Space (d+1)) → ℝ, Measurable g ∧ (∀ x, 0 ≤ g x) ∧
      MemLp g (ENNReal.ofReal p) (surfaceMeasure (d+1)) ∧
      (surfaceMeasure (d+1)).withDensity (fun x => ENNReal.ofReal (g x)) = γ ∧
      eLpNorm g (ENNReal.ofReal p) (surfaceMeasure (d+1)) ≤ surfaceTestNorm q γ := by
  let : γ.HaveLebesgueDecomposition (surfaceMeasure (d+1)) :=
    Measure.haveLebesgueDecomposition_of_finiteMeasure
  let g := fun x => (γ.rnDeriv (surfaceMeasure (d+1)) x).toReal
  have hg : Measurable g := (Measure.measurable_rnDeriv γ (surfaceMeasure (d+1))).ennreal_toReal
  have hb := surfaceTestNorm_rnDeriv_eLpNorm_le γ hpq hN
  refine ⟨g, hg, fun _ => ENNReal.toReal_nonneg, hb.trans_lt hN.lt_top, ?_, hb⟩
  have he : (fun x => ENNReal.ofReal (g x)) =ᵐ[(surfaceMeasure (d+1))] γ.rnDeriv (surfaceMeasure (d+1)) := by
    filter_upwards [Measure.rnDeriv_lt_top γ (surfaceMeasure (d+1))] with x hx
    exact ENNReal.ofReal_toReal hx.ne
  rw [withDensity_congr_ae he]
  exact Measure.withDensity_rnDeriv_eq γ (surfaceMeasure (d+1))
    (surfaceTestNorm_absolutelyContinuous γ (Real.holderConjugate_iff.mp hpq.symm).1.le hN)

end Falconer

end OAI
