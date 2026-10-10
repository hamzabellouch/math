import OAI.Analysis.IrrationalRotation.Model.UniformIntervalPhase
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Tactic
import Mathlib.Probability.ConditionalProbability

namespace OAI

open MeasureTheory Set
open scoped ENNReal

namespace Invariant233.UniformIntervalPhase

theorem map_interval_nat (a : ℝ) (n : ℕ) :
    (volume.restrict (Ioc a (a + n))).map (fun x : ℝ => (x : UnitAddCircle)) =
      (n : ℝ≥0∞) • (volume : Measure UnitAddCircle) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit : Ioc a (a + (n + 1 : ℕ)) =
        Ioc a (a + n) ∪ Ioc (a + n) (a + n + 1) := by
      rw [Ioc_union_Ioc_eq_Ioc (by linarith [Nat.cast_nonneg (α := ℝ) n] : a ≤ a + (n : ℝ)) (by linarith)]
      congr 1
      push_cast
      ring
    rw [hsplit, Measure.restrict_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc,
      Measure.map_add _ _ AddCircle.measurable_mk', ih]
    rw [(UnitAddCircle.measurePreserving_mk (a + n)).map_eq]
    simp [Nat.cast_add, add_smul]

theorem map_interval_le_haar {a r : ℝ} (hr : r ≤ 1) :
    (volume.restrict (Ioc a (a + r))).map (fun x : ℝ => (x : UnitAddCircle)) ≤
      (volume : Measure UnitAddCircle) := by
  calc
    _ ≤ (volume.restrict (Ioc a (a + 1))).map (fun x : ℝ => (x : UnitAddCircle)) :=
      Measure.map_mono (Measure.restrict_mono (Ioc_subset_Ioc_right (by linarith)) le_rfl)
        AddCircle.measurable_mk'
    _ = volume := (UnitAddCircle.measurePreserving_mk a).map_eq

theorem map_interval_sandwich (a L : ℝ) (hL : 0 ≤ L) :
    (⌊L⌋₊ : ℝ≥0∞) • (volume : Measure UnitAddCircle) ≤
        (volume.restrict (Ioc a (a + L))).map (fun x : ℝ => (x : UnitAddCircle)) ∧
      (volume.restrict (Ioc a (a + L))).map (fun x : ℝ => (x : UnitAddCircle)) ≤
        ((⌊L⌋₊ : ℝ≥0∞) + 1) • (volume : Measure UnitAddCircle) := by
  constructor
  · rw [← map_interval_nat a ⌊L⌋₊]
    apply Measure.map_mono _ AddCircle.measurable_mk'
    apply Measure.restrict_mono _ le_rfl
    exact Ioc_subset_Ioc_right (by linarith [Nat.floor_le hL])
  · calc
      _ ≤ (volume.restrict (Ioc a (a + (⌊L⌋₊ + 1 : ℕ)))).map
          (fun x : ℝ => (x : UnitAddCircle)) := by
        apply Measure.map_mono _ AddCircle.measurable_mk'
        apply Measure.restrict_mono _ le_rfl
        apply Ioc_subset_Ioc_right
        have h := (Nat.lt_floor_add_one L).le
        push_cast
        linarith
      _ = _ := by rw [map_interval_nat]; simp

theorem rnDeriv_le_const_of_le_smul
    {X : Type*} [MeasurableSpace X] {μ ν : Measure X} [SigmaFinite ν]
    {c : ℝ≥0∞} (h : μ ≤ c • ν) :
    ∀ᵐ x ∂ν, μ.rnDeriv ν x ≤ c := by
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (μ.measurable_rnDeriv ν)
  intro s hs hfinite
  calc
    (∫⁻ x in s, μ.rnDeriv ν x ∂ν) ≤ μ s := Measure.setLIntegral_rnDeriv_le s
    _ ≤ (c • ν) s := h s
    _ = ∫⁻ _ in s, c ∂ν := by simp

theorem const_le_rnDeriv_of_smul_le
    {X : Type*} [MeasurableSpace X] {μ ν : Measure X}
    [Measure.HaveLebesgueDecomposition μ ν] [SigmaFinite ν]
    {c : ℝ≥0∞} (hac : μ ≪ ν) (h : c • ν ≤ μ) :
    ∀ᵐ x ∂ν, c ≤ μ.rnDeriv ν x := by
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite measurable_const
  intro s hs hfinite
  calc
    (∫⁻ _ in s, c ∂ν) = (c • ν) s := by simp
    _ ≤ μ s := h s
    _ = ∫⁻ x in s, μ.rnDeriv ν x ∂ν := (Measure.setLIntegral_rnDeriv' hac hs).symm

theorem phaseLaw_sandwich (a L : ℝ) (hL : 0 < L) :
    ENNReal.ofReal ((⌊L⌋₊ : ℝ) / L) • (volume : Measure UnitAddCircle) ≤ phaseLaw a L ∧
      phaseLaw a L ≤ ENNReal.ofReal (((⌊L⌋₊ : ℝ) + 1) / L) •
        (volume : Measure UnitAddCircle) := by
  have h := map_interval_sandwich a L hL.le
  have hlow := smul_le_smul_left (ENNReal.ofReal (1 / L)) h.1
  have hupp := smul_le_smul_left (ENNReal.ofReal (1 / L)) h.2
  have hc0 : 0 ≤ 1 / L := by positivity
  have hlo : ENNReal.ofReal (1 / L) * (⌊L⌋₊ : ℝ≥0∞) =
      ENNReal.ofReal ((⌊L⌋₊ : ℝ) / L) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hc0]
    congr 1
    ring
  have hup : ENNReal.ofReal (1 / L) * ((⌊L⌋₊ : ℝ≥0∞) + 1) =
      ENNReal.ofReal (((⌊L⌋₊ : ℝ) + 1) / L) := by
    have hn : (⌊L⌋₊ : ℝ≥0∞) + 1 = ENNReal.ofReal ((⌊L⌋₊ : ℝ) + 1) := by
      rw [ENNReal.ofReal_add (by positivity) (by norm_num)]
      simp
    rw [hn, ← ENNReal.ofReal_mul hc0]
    congr 1
    ring
  constructor
  · simpa only [phaseLaw, intervalLaw,
      Measure.map_smul _ AddCircle.measurable_mk'.aemeasurable, smul_smul, hlo] using hlow
  · simpa only [phaseLaw, intervalLaw,
      Measure.map_smul _ AddCircle.measurable_mk'.aemeasurable, smul_smul, hup] using hupp

theorem real_density_spec_of_sandwich {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure ν] (L : ℝ) (hL : 0 < L)
    (hlow : ENNReal.ofReal ((⌊L⌋₊ : ℝ) / L) • ν ≤ μ)
    (hupp : μ ≤ ENNReal.ofReal (((⌊L⌋₊ : ℝ) + 1) / L) • ν) :
    Measurable (fun x => (μ.rnDeriv ν x).toReal) ∧
      (∀ᵐ x ∂ν, 0 ≤ (μ.rnDeriv ν x).toReal ∧
        |(μ.rnDeriv ν x).toReal - 1| ≤ 1 / L) ∧
      ν.withDensity (fun x => ENNReal.ofReal (μ.rnDeriv ν x).toReal) = μ := by
  let : IsFiniteMeasure (ENNReal.ofReal (((⌊L⌋₊ : ℝ) + 1) / L) •
      ν) := ν.smul_finite ENNReal.ofReal_ne_top
  let : IsFiniteMeasure μ :=
    isFiniteMeasure_of_le (ENNReal.ofReal (((⌊L⌋₊ : ℝ) + 1) / L) • ν) hupp
  have hac : μ ≪ ν :=
    Measure.absolutelyContinuous_of_le_smul hupp
  have hlo := const_le_rnDeriv_of_smul_le hac hlow
  have hup := rnDeriv_le_const_of_le_smul hupp
  have hfinite : ∀ᵐ x ∂ν,
      μ.rnDeriv ν x ≠ ⊤ := by
    filter_upwards [hup] with x hx
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hx
  refine ⟨(μ.measurable_rnDeriv ν).ennreal_toReal, ?_, ?_⟩
  · filter_upwards [hlo, hup, hfinite] with x hxlo hxup hxfin
    have hrlo : (⌊L⌋₊ : ℝ) / L ≤ (μ.rnDeriv ν x).toReal := by
      simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (⌊L⌋₊ : ℝ) / L)]
        using ENNReal.toReal_mono hxfin hxlo
    have hrup : (μ.rnDeriv ν x).toReal ≤ ((⌊L⌋₊ : ℝ) + 1) / L := by
      simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ ((⌊L⌋₊ : ℝ) + 1) / L)]
        using ENNReal.toReal_mono ENNReal.ofReal_ne_top hxup
    have hfloor := Nat.floor_le hL.le
    have hceil := Nat.lt_floor_add_one L
    have hrlo' := (div_le_iff₀ hL).mp hrlo
    have hrup' := (le_div_iff₀ hL).mp hrup
    have hinv : (1 / L) * L = 1 := by field_simp
    refine ⟨ENNReal.toReal_nonneg, abs_le.mpr ⟨?_, ?_⟩⟩ <;> nlinarith
  · calc
      _ = ν.withDensity (μ.rnDeriv ν) := by
        apply withDensity_congr_ae
        filter_upwards [hfinite] with x hx
        exact ENNReal.ofReal_toReal hx
      _ = μ := Measure.withDensity_rnDeriv_eq _ _ hac

theorem phaseDensity_spec (a L : ℝ) (hL : 0 < L) :
    Measurable (phaseDensity a L) ∧
      (∀ᵐ x ∂(volume : Measure UnitAddCircle),
        0 ≤ phaseDensity a L x ∧ |phaseDensity a L x - 1| ≤ 1 / L) ∧
      (volume : Measure UnitAddCircle).withDensity
        (fun x => ENNReal.ofReal (phaseDensity a L x)) = phaseLaw a L := by
  obtain ⟨hlow, hupp⟩ := phaseLaw_sandwich a L hL
  exact real_density_spec_of_sandwich (phaseLaw a L) volume L hL hlow hupp

theorem intervalLaw_map_mul (a L c : ℝ) (hL : 0 < L) (hc : 0 < c) :
    (intervalLaw a L).map (fun x => c * x) = intervalLaw (c * a) (c * L) := by
  have hpre : (fun x : ℝ => c * x) ⁻¹' Ioc (c * a) (c * (a + L)) =
      Ioc a (a + L) := by
    ext x
    simp only [mem_preimage, mem_Ioc, mul_lt_mul_iff_of_pos_left hc, mul_le_mul_iff_of_pos_left hc]
  have hm := (measurableEmbedding_mulLeft₀ hc.ne').restrict_map
    (volume : Measure ℝ) (Ioc (c * a) (c * (a + L)))
  rw [hpre, Real.map_volume_mul_left hc.ne', Measure.restrict_smul] at hm
  have hscale : ENNReal.ofReal (1 / L) * ENNReal.ofReal |c⁻¹| =
      ENNReal.ofReal (1 / (c * L)) := by
    rw [abs_of_pos (inv_pos.mpr hc), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  simp only [intervalLaw, Measure.map_smul _ (measurable_const_mul c).aemeasurable]
  rw [← hm, smul_smul, hscale, mul_add]

theorem sampled_phaseLaw (N₀ n : ℝ) (hN : 0 < N₀) (hn : 0 < n) :
    (intervalLaw (1 / N₀) (1 / N₀)).map
      (fun x : ℝ => ((n * x : ℝ) : UnitAddCircle)) =
      phaseLaw (n / N₀) (n / N₀) := by
  have heq : n / N₀ = n * (1 / N₀) := by ring
  rw [phaseLaw, heq, ← intervalLaw_map_mul (1 / N₀) (1 / N₀) n (by positivity) hn]
  rw [Measure.map_map AddCircle.measurable_mk' (measurable_const_mul n)]
  rfl

theorem lambdaLaw_eq_intervalLaw (N₀ : ℝ) :
    lambdaLaw N₀ = intervalLaw (1 / N₀) (1 / N₀) := by
  have heq : 1 / N₀ + 1 / N₀ = 2 / N₀ := by ring
  simp only [lambdaLaw, intervalLaw, one_div_one_div, heq,
    restrict_Ioc_eq_restrict_Icc]

theorem scalar_marginal_circle (N₀ n : ℝ) (hN : 0 < N₀) (hn : 0 < n) :
    Measurable (phaseDensity (n / N₀) (n / N₀)) ∧
      (∀ᵐ x ∂(volume : Measure UnitAddCircle),
        0 ≤ phaseDensity (n / N₀) (n / N₀) x ∧
          |phaseDensity (n / N₀) (n / N₀) x - 1| ≤ N₀ / n) ∧
      (volume : Measure UnitAddCircle).withDensity
        (fun x => ENNReal.ofReal (phaseDensity (n / N₀) (n / N₀) x)) =
        (lambdaLaw N₀).map (fun x : ℝ => ((n * x : ℝ) : UnitAddCircle)) := by
  rw [lambdaLaw_eq_intervalLaw, sampled_phaseLaw N₀ n hN hn]
  have heq : 1 / (n / N₀) = N₀ / n := by field_simp
  simpa only [heq] using phaseDensity_spec (n / N₀) (n / N₀) (div_pos hn hN)

theorem measurable_representative : Measurable representative :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable

@[simp] theorem representative_coe (x : ℝ) :
    representative (x : UnitAddCircle) = Int.fract x := by
  simp [representative]

theorem map_representative_haar :
    (volume : Measure UnitAddCircle).map representative =
      volume.restrict (Ico (0 : ℝ) 1) := by
  have hmk : (volume.restrict (Ico (0 : ℝ) 1)).map
      (fun x : ℝ => (x : UnitAddCircle)) = volume := by
    rw [restrict_Ico_eq_restrict_Ioc]
    simpa using (UnitAddCircle.measurePreserving_mk 0).map_eq
  rw [← hmk, Measure.map_map measurable_representative AddCircle.measurable_mk']
  have heq : (representative ∘ fun x : ℝ => (x : UnitAddCircle)) =ᵐ[
      volume.restrict (Ico (0 : ℝ) 1)] id := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    change representative (x : UnitAddCircle) = x
    unfold representative
    rw [AddCircle.equivIco_coe_eq (by simpa using hx)]
  rw [Measure.map_congr heq, Measure.map_id]

theorem fractionLaw_eq_map_phaseLaw (N₀ n : ℝ) (hN : 0 < N₀) (hn : 0 < n) :
    fractionLaw N₀ n = (phaseLaw (n / N₀) (n / N₀)).map representative := by
  have hnm : Measurable (fun x : ℝ => ((n * x : ℝ) : UnitAddCircle)) :=
    AddCircle.measurable_mk'.comp (measurable_const_mul n)
  rw [← sampled_phaseLaw N₀ n hN hn, Measure.map_map measurable_representative hnm]
  simp only [fractionLaw, lambdaLaw_eq_intervalLaw, Function.comp_def, representative_coe]

theorem scalar_marginal (N₀ n : ℝ) (hN : 0 < N₀) (hn : 0 < n) :
    Measurable (fractionDensity N₀ n) ∧
      (∀ᵐ x ∂volume.restrict (Ico (0 : ℝ) 1),
        0 ≤ fractionDensity N₀ n x ∧ |fractionDensity N₀ n x - 1| ≤ N₀ / n) ∧
      (volume.restrict (Ico (0 : ℝ) 1)).withDensity
        (fun x => ENNReal.ofReal (fractionDensity N₀ n x)) = fractionLaw N₀ n := by
  obtain ⟨hlow, hupp⟩ := phaseLaw_sandwich (n / N₀) (n / N₀) (div_pos hn hN)
  have hlo := Measure.map_mono hlow measurable_representative
  have hup := Measure.map_mono hupp measurable_representative
  rw [Measure.map_smul _ measurable_representative.aemeasurable, map_representative_haar,
    ← fractionLaw_eq_map_phaseLaw N₀ n hN hn] at hlo hup
  have heq : 1 / (n / N₀) = N₀ / n := by field_simp
  unfold fractionDensity
  simpa only [heq] using
    real_density_spec_of_sandwich (fractionLaw N₀ n)
      (volume.restrict (Ico (0 : ℝ) 1)) (n / N₀) (div_pos hn hN) hlo hup

theorem lambdaLaw_probability (N₀ : ℝ) (hN : 0 < N₀) :
    IsProbabilityMeasure (lambdaLaw N₀) := by
  constructor
  have heq : 2 / N₀ - 1 / N₀ = 1 / N₀ := by ring
  simp only [lambdaLaw, Measure.smul_apply, Measure.restrict_apply_univ,
    Real.volume_Icc, heq, smul_eq_mul]
  rw [← ENNReal.ofReal_mul hN.le]
  have heq' : N₀ * (1 / N₀) = 1 := by field_simp
  rw [heq', ENNReal.ofReal_one]

theorem fractionDensity_le_two (N₀ n : ℝ) (hN : 0 < N₀) (hn : N₀ ≤ n) :
    ∀ᵐ x ∂volume.restrict (Ico (0 : ℝ) 1), fractionDensity N₀ n x ≤ 2 := by
  have hn0 : 0 < n := hN.trans_le hn
  filter_upwards [(scalar_marginal N₀ n hN hn0).2.1] with x hx
  have hratio : N₀ / n ≤ 1 := (div_le_one hn0).mpr hn
  have hupper := (abs_le.mp hx.2).2
  linarith

theorem lambdaLaw_eq_cond (N₀ : ℝ) (hN : 0 < N₀) :
    lambdaLaw N₀ = ProbabilityTheory.cond volume (Icc (1 / N₀) (2 / N₀)) := by
  have heq : 2 / N₀ - 1 / N₀ = 1 / N₀ := by ring
  simp only [lambdaLaw, ProbabilityTheory.cond, Real.volume_Icc]
  rw [heq, one_div, ENNReal.ofReal_inv_of_pos hN, inv_inv]

theorem sampled_circle_le_two (N₀ n : ℝ) (hN : 0 < N₀) (hn : N₀ ≤ n) :
    (lambdaLaw N₀).map (fun x : ℝ => ((n * x : ℝ) : UnitAddCircle)) ≤
      (2 : ℝ≥0∞) • (volume : Measure UnitAddCircle) := by
  have hn0 : 0 < n := hN.trans_le hn
  have hL : 0 < n / N₀ := div_pos hn0 hN
  have hone : 1 ≤ n / N₀ := (le_div_iff₀ hN).mpr (by simpa using hn)
  rw [lambdaLaw_eq_intervalLaw, sampled_phaseLaw N₀ n hN hn0]
  refine (phaseLaw_sandwich (n / N₀) (n / N₀) hL).2.trans ?_
  have hc : ENNReal.ofReal (((⌊n / N₀⌋₊ : ℝ) + 1) / (n / N₀)) ≤ (2 : ℝ≥0∞) := by
    have hr : ((⌊n / N₀⌋₊ : ℝ) + 1) / (n / N₀) ≤ 2 := by
      apply (div_le_iff₀ hL).mpr
      linarith [Nat.floor_le hL.le]
    exact_mod_cast ENNReal.ofReal_le_ofReal hr
  intro s
  change ENNReal.ofReal (((⌊n / N₀⌋₊ : ℝ) + 1) / (n / N₀)) * volume s ≤
    (2 : ℝ≥0∞) * volume s
  exact mul_le_mul_left hc _

theorem integral_sample_le_two (N₀ n : ℝ) (hN : 0 < N₀) (hn : N₀ ≤ n)
    (f : UnitAddCircle → ℝ) (hf : Integrable f volume)
    (hf0 : ∀ᵐ x ∂(volume : Measure UnitAddCircle), 0 ≤ f x) :
    Integrable (fun x : ℝ => f ((n * x : ℝ) : UnitAddCircle)) (lambdaLaw N₀) ∧
      (∫ x : ℝ, f ((n * x : ℝ) : UnitAddCircle) ∂lambdaLaw N₀) ≤
        2 * ∫ x : UnitAddCircle, f x := by
  have hmap := sampled_circle_le_two N₀ n hN hn
  have hfi := (hf.smul_measure (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).mono_measure hmap
  have hnm : Measurable (fun x : ℝ => ((n * x : ℝ) : UnitAddCircle)) :=
    AddCircle.measurable_mk'.comp (measurable_const_mul n)
  refine ⟨hfi.comp_measurable hnm, ?_⟩
  rw [← integral_map hnm.aemeasurable hfi.aestronglyMeasurable]
  have hbound := integral_mono_measure hmap (Measure.ae_smul_measure hf0 (2 : ℝ≥0∞))
    (hf.smul_measure (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
  simpa [integral_smul_measure] using hbound

theorem norm_integral_phase_sub_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (a L : ℝ) (hL : 0 < L)
    (f : UnitAddCircle → E) (hf : Integrable f volume) :
    Integrable f (phaseLaw a L) ∧
      ‖(∫ x, f x ∂phaseLaw a L) - (∫ x : UnitAddCircle, f x)‖ ≤
        (1 / L) * ∫ x : UnitAddCircle, ‖f x‖ := by
  have hupp := (phaseLaw_sandwich a L hL).2
  let : IsFiniteMeasure (ENNReal.ofReal (((⌊L⌋₊ : ℝ) + 1) / L) •
      (volume : Measure UnitAddCircle)) := volume.smul_finite ENNReal.ofReal_ne_top
  let : IsFiniteMeasure (phaseLaw a L) :=
    isFiniteMeasure_of_le (ENNReal.ofReal (((⌊L⌋₊ : ℝ) + 1) / L) • volume) hupp
  have hac : phaseLaw a L ≪ (volume : Measure UnitAddCircle) :=
    Measure.absolutelyContinuous_of_le_smul hupp
  obtain ⟨hp, hbound, _⟩ := phaseDensity_spec a L hL
  have hpbound : ∀ᵐ x ∂(volume : Measure UnitAddCircle),
      ‖phaseDensity a L x‖ ≤ 1 + 1 / L := by
    filter_upwards [hbound] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
    linarith [(abs_le.mp hx.2).2]
  have hpf : Integrable (fun x => phaseDensity a L x • f x) volume :=
    hf.bdd_smul (1 + 1 / L) hp.aestronglyMeasurable hpbound
  have hfi : Integrable f (phaseLaw a L) :=
    (integrable_rnDeriv_smul_iff hac).mp hpf
  have hint : (∫ x, phaseDensity a L x • f x) = ∫ x, f x ∂phaseLaw a L :=
    integral_rnDeriv_smul hac
  refine ⟨hfi, ?_⟩
  rw [← hint, ← integral_sub hpf hf]
  calc
    _ ≤ ∫ x : UnitAddCircle, (1 / L) * ‖f x‖ := by
      apply norm_integral_le_of_norm_le (hf.norm.const_mul (1 / L))
      filter_upwards [hbound] with x hx
      have heq : phaseDensity a L x • f x - f x =
          (phaseDensity a L x - 1) • f x := by rw [sub_smul, one_smul]
      rw [heq, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hx.2 (norm_nonneg _)
    _ = _ := integral_const_mul _ _

theorem norm_integral_sample_sub_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (N₀ n : ℝ) (hN : 0 < N₀) (hn : 0 < n)
    (f : UnitAddCircle → E) (hf : Integrable f volume) :
    Integrable (fun x : ℝ => f ((n * x : ℝ) : UnitAddCircle)) (lambdaLaw N₀) ∧
      ‖(∫ x : ℝ, f ((n * x : ℝ) : UnitAddCircle) ∂lambdaLaw N₀) -
          (∫ x : UnitAddCircle, f x)‖ ≤ (N₀ / n) * ∫ x : UnitAddCircle, ‖f x‖ := by
  obtain ⟨hfi, hbound⟩ := norm_integral_phase_sub_le
    (n / N₀) (n / N₀) (div_pos hn hN) f hf
  have heq : phaseLaw (n / N₀) (n / N₀) =
      (lambdaLaw N₀).map (fun x : ℝ => ((n * x : ℝ) : UnitAddCircle)) := by
    rw [lambdaLaw_eq_intervalLaw, sampled_phaseLaw N₀ n hN hn]
  rw [heq] at hfi hbound
  have hnm : Measurable (fun x : ℝ => ((n * x : ℝ) : UnitAddCircle)) :=
    AddCircle.measurable_mk'.comp (measurable_const_mul n)
  have hratio : 1 / (n / N₀) = N₀ / n := by field_simp
  refine ⟨hfi.comp_measurable hnm, ?_⟩
  rw [integral_map hnm.aemeasurable hfi.aestronglyMeasurable, hratio] at hbound
  exact hbound

end Invariant233.UniformIntervalPhase

end OAI
