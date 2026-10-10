import OAI.Analysis.FourierLLogL.Fourier.Endpoint
/-! # Using period one in real coordinates -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal BigOperators Topology Real

namespace OAI

namespace FourierLLogL

namespace Period

def unitInt : Set ℝ := Ico 0 1

noncomputable def μ₁ : Measure ℝ := volume.restrict unitInt

def circle (x : ℝ) : Torus := ((2 * π) * x : ℝ)

lemma measurable_unitInt : MeasurableSet unitInt := measurableSet_Ico

instance : IsProbabilityMeasure μ₁ := by
  constructor
  simp [μ₁, unitInt]

theorem measurable_circle : Measurable circle :=
  AddCircle.measurable_mk'.comp (measurable_const.mul measurable_id)

lemma map_circle_volume : Measure.map circle μ₁ = circleMeasure := by
  let t : ℝ := 2*π
  have ht : 0 < t := Real.two_pi_pos
  let φ (x : ℝ) := t*x
  have h : Measurable φ := measurable_const.mul measurable_id
  change Measure.map (((↑) : ℝ → AddCircle t) ∘ φ) μ₁ = _
  rw [← Measure.map_map AddCircle.measurable_mk' h]
  have hf : φ ⁻¹' Ico 0 (0+t) = unitInt := by
    ext x
    simp only [unitInt, mem_Ico, mem_preimage, zero_add, φ]
    constructor
    · intro ⟨hx, hy⟩; constructor <;> nlinarith
    · intro ⟨hx, hy⟩; constructor <;> nlinarith
  rw [μ₁, ← hf, ← Measure.restrict_map h measurableSet_Ico,
    Real.map_volume_mul_left ht.ne', Measure.restrict_smul,
    Measure.restrict_congr_set Ico_ae_eq_Ioc, Measure.map_smul,
    (AddCircle.measurePreserving_mk t 0).map_eq, AddCircle.volume_eq_smul_haarAddCircle,
    smul_smul, abs_of_pos (inv_pos.mpr ht), ← ENNReal.ofReal_mul (inv_pos.mpr ht).le,
    inv_mul_cancel₀ ht.ne', ENNReal.ofReal_one, one_smul]
  all_goals first
    | rfl
    | exact AddCircle.measurable_mk'.aemeasurable

lemma periodic_circle : Function.Periodic circle 1 := by
  intro x
  simp only [circle, mul_add, mul_one, AddCircle.coe_add_period]

def coord (x : Torus) : ℝ :=
  ((AddCircle.measurableEquivIco (2*π) 0 x).val) / (2*π)

theorem measurable_coord : Measurable coord :=
  (measurable_subtype_coe.comp (AddCircle.measurableEquivIco (2*π) 0).measurable).div_const _

lemma coord_circle_eq {x : ℝ} (hx : x ∈ unitInt) : coord (circle x) = x := by
  let t := (2 * π)
  have ht : (0:ℝ) < t := Real.two_pi_pos
  change (((AddCircle.equivIco t 0 ((t*x:ℝ):AddCircle t)).val) / t) = x
  have h : t * x ∈ Ico 0 (0+t) := by
    rcases hx with ⟨h1,h2⟩
    simp only [mem_Ico]
    constructor <;> nlinarith
  rw [AddCircle.equivIco_coe_eq h]
  exact mul_div_cancel_left₀ _ ht.ne'

/-- Character with cycles-per-unit real frequency. -/
def phase (u x : ℝ) : ℂ :=
  Complex.exp (Complex.I * ↑(u*((2*π) * x)))

lemma phase_cont (u) : Continuous (phase u) := by unfold phase; fun_prop
lemma phase_unimod (u x) : ‖phase u x‖ = 1 := by
  simp [phase, Complex.norm_exp]

lemma fourier_circle (n : ℤ) (x : ℝ) : fourier n (circle x) = phase n x := by
  simp only [circle, fourier_of_real, phase, Complex.ofReal_mul, Complex.ofReal_intCast,
    mul_assoc]

lemma phase_periodic (n : ℤ) : Function.Periodic (phase n) 1 :=
  fun x => by rw [← fourier_circle, ← fourier_circle, periodic_circle x]

def sumReal (f : ℝ → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), (∫ y, f y * phase (-(k:ℤ):ℤ) y ∂μ₁) * phase k x

def maxReal (f : ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ N : ℕ, ENNReal.ofReal ‖sumReal f N x‖

lemma sum_eq (f : Torus → ℂ) (hf : Measurable f) (N x) :
    symmetricPartialSum f N (circle x) = sumReal (f ∘ circle) N x := by
  simp only [symmetricPartialSum, sumReal, fourierCoeff_eq_integral, ← map_circle_volume]
  refine Finset.sum_congr rfl ?_
  intro n _
  rw [integral_map (f:=fun x => f x * fourier (-n) x) measurable_circle.aemeasurable
    ((hf.mul (fourier _).continuous.measurable).aestronglyMeasurable)]
  simp only [fourier_circle, Function.comp_def]

def RealGoodBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ j : ℕ in atTop, ∀ (f : ℝ → ℝ),
    Measurable f → Function.Periodic f 1 → (∀ x, 0 ≤ f x) → (∫ x, f x ∂μ₁) ≤ 1 →
    (∀ x, f x ≤ Real.exp ((2 : ℝ)^j)) →
    ∃ G : Set ℝ, MeasurableSet G ∧
      μ₁ Gᶜ ≤ ENNReal.ofReal (C / ((j:ℝ) + 1)^2) ∧
      (∫⁻ x in G, maxReal (fun y => (f y : ℂ)) x ∂μ₁) ≤ ENNReal.ofReal (C * (2:ℝ)^j)

end Period

def HasMaxCost (f : Torus → ℂ) (j : ℕ) (C : ℝ) : Prop :=
    ∃ G : Set Torus, MeasurableSet G ∧
      circleMeasure Gᶜ ≤ ENNReal.ofReal (C / ((j:ℝ) + 1)^2) ∧
      (∫⁻ x in G, symmetricMaximal f x ∂circleMeasure) ≤ ENNReal.ofReal (C * (2:ℝ)^j)

namespace Period

lemma cost_transfer (f : Torus → ℂ) (hf : Measurable f)
    (j : ℕ) (C : ℝ) (G : Set ℝ) (hG : MeasurableSet G)
    (hsize : μ₁ Gᶜ ≤ ENNReal.ofReal (C / ((j:ℝ) + 1)^2))
    (hint : (∫⁻ x in G, maxReal (f ∘ circle) x ∂μ₁) ≤ ENNReal.ofReal (C * (2:ℝ)^j)) :
    HasMaxCost f j C := by
  let S := coord ⁻¹' G
  have hS : MeasurableSet S := measurable_coord hG
  refine ⟨S, hS, ?_, ?_⟩
  · rw [← map_circle_volume, Measure.map_apply measurable_circle hS.compl]
    have heq : circle ⁻¹' Sᶜ =ᵐ[μ₁] Gᶜ := by
      filter_upwards [ae_restrict_mem (μ:=volume) measurable_unitInt] with x hx
      change (coord (circle x) ∉ G) = (x ∉ G)
      rw [coord_circle_eq hx]
    rwa [measure_congr heq]
  · rw [← lintegral_indicator hS, ← map_circle_volume,
      lintegral_map ((measurable_symmetricMaximal _).indicator hS) measurable_circle]
    rw [← lintegral_indicator hG] at hint
    convert hint using 1
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (μ:=volume) measurable_unitInt] with x hx
    have heq : symmetricMaximal f (circle x) = maxReal (f ∘ circle) x := by
      simp only [symmetricMaximal, maxReal, sum_eq f hf]
    by_cases h : x ∈ G <;> simp [S, coord_circle_eq hx, heq, h]

end Period

lemma HasMaxCost.add {f g : Torus → ℂ} {C D : ℝ} {j : ℕ}
    (hF : HasMaxCost f j C) (hG : HasMaxCost g j D)
    (hf : Integrable f circleMeasure) (hg : Integrable g circleMeasure)
    (hC : 0 ≤ C) (hD : 0 ≤ D) : HasMaxCost (f+g) j (C+D) := by
  obtain ⟨F, hFm, hFs, hFi⟩ := hF
  obtain ⟨G, hGm, hGs, hGi⟩ := hG
  refine ⟨F ∩ G, hFm.inter hGm, ?_, ?_⟩
  · rw [add_div, ENNReal.ofReal_add (by positivity) (by positivity), Set.compl_inter]
    exact (measure_union_le _ _).trans (add_le_add hFs hGs)
  · have h (x : Torus) :
        symmetricMaximal (f + g) x ≤ symmetricMaximal f x + symmetricMaximal g x := by
      unfold symmetricMaximal
      refine iSup_le fun n => ?_
      rw [symmetricPartialSum_add hf hg]
      refine (ENNReal.ofReal_le_ofReal
        (norm_add_le (symmetricPartialSum f n x) (symmetricPartialSum g n x))).trans ?_
      rw [ENNReal.ofReal_add (by positivity) (by positivity)]
      exact add_le_add (le_iSup (fun N => ENNReal.ofReal ‖symmetricPartialSum f N x‖) n)
        (le_iSup (fun N => ENNReal.ofReal ‖symmetricPartialSum g N x‖) n)
    refine (lintegral_mono h).trans ?_
    rw [lintegral_add_left (measurable_symmetricMaximal _), add_mul,
      ENNReal.ofReal_add (by positivity) (by positivity)]
    exact add_le_add ((lintegral_mono_set inter_subset_left).trans hFi)
      ((lintegral_mono_set inter_subset_right).trans hGi)

lemma HasMaxCost.rot {f j C} (h : HasMaxCost f j C)
    (c : ℂ) (hc : ‖c‖ = 1) : HasMaxCost (fun x => c * f x) j C := by
  simpa [HasMaxCost, symmetricMaximal_mul, hc] using h


theorem Period.RealGoodBound.goodBound (hb : Period.RealGoodBound) : GoodBound := by
  obtain ⟨C, hC, h⟩ := hb
  refine ⟨C+C+(C+C), by positivity, ?_⟩
  filter_upwards [h] with j hj
  intro f hf ha he
  let f₀ := hf.aestronglyMeasurable.mk f
  let g (x : Torus) := if ‖f₀ x‖ ≤ Real.exp ((2:ℝ)^j) then f₀ x else 0
  have hf₀ : Measurable f₀ := hf.aestronglyMeasurable.measurable_mk
  have hg : Measurable g :=
    Measurable.ite (measurableSet_le hf₀.norm measurable_const) hf₀ measurable_const
  have hfg : f =ᵐ[circleMeasure] g := by
    filter_upwards [hf.aestronglyMeasurable.ae_eq_mk, he] with x hx hx'
    change f x = f₀ x at hx
    simp only [g, ← hx, hx', ite_true]
  have hgb (x : Torus) : ‖g x‖ ≤ Real.exp ((2:ℝ)^j) := by
    dsimp only [g]
    split_ifs with HH
    · exact HH
    · rw [norm_zero]; positivity
  have hgi : Integrable g circleMeasure := hf.congr hfg
  have hgm : (∫ x, ‖g x‖ ∂circleMeasure) ≤ 1 :=
    (integral_congr_ae (hfg.symm.fun_comp (‖·‖))).le.trans ha
  have hpart (w : Torus → ℝ) (hw : Measurable w)
      (hw0 : ∀ x, 0 ≤ w x) (hwn : ∀ x, w x ≤ ‖g x‖) :
      HasMaxCost (fun x => (w x : ℂ)) j C ∧
        Integrable (fun x => (w x : ℂ)) circleMeasure := by
    have hc : Measurable (fun x => (w x : ℂ)) := Complex.continuous_ofReal.measurable.comp hw
    have hwi : Integrable w circleMeasure := Integrable.of_bound hw.aestronglyMeasurable _
      (ae_of_all _ (fun x => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hw0 x)] using
          (hwn x).trans (hgb x)))
    have hwci : Integrable (fun x => (w x : ℂ)) circleMeasure :=
      Integrable.of_bound hc.aestronglyMeasurable _ (ae_of_all _ (fun x => by
        simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw0 x)] using
          (hwn x).trans (hgb x)))
    have hm : (∫ x, (w ∘ circle) x ∂μ₁) ≤ 1 := by
      simp only [Function.comp_apply, ← integral_map (f:=w)
        measurable_circle.aemeasurable hw.aestronglyMeasurable, map_circle_volume]
      exact (integral_mono hwi hgi.norm hwn).trans hgm
    obtain ⟨G,hG,hsize,hInt⟩ := hj (w ∘ circle) (hw.comp measurable_circle)
      (fun x => congrArg w (periodic_circle x))
      (fun x => hw0 _) hm (fun x => (hwn _).trans (hgb _))
    exact ⟨cost_transfer _ hc j C G hG hsize hInt, hwci⟩
  have hdiff (w : Torus → ℝ) (hw : Measurable w) (hwn : ∀ x, |w x| ≤ ‖g x‖) :
      HasMaxCost (fun x => (w x : ℂ)) j (C+C) ∧
        Integrable (fun x => (w x : ℂ)) circleMeasure := by
    obtain ⟨hp, hpi⟩ := hpart (fun x => max 0 (w x)) (measurable_const.max hw) (fun x => le_max_left _ _)
      (fun x => max_le (norm_nonneg _) ((abs_le.mp (hwn x)).2))
    obtain ⟨hn, hni⟩ := hpart (fun x => max 0 (-w x)) (measurable_const.max hw.neg)
      (fun x => le_max_left _ _) (fun x => max_le (norm_nonneg _) (by have := (abs_le.mp (hwn x)).1; linarith))
    rw [show (fun x => (w x : ℂ)) = (fun x => ((max 0 (w x) : ℝ) : ℂ))
          + (fun x => (-1:ℂ) * ((max 0 (-w x) : ℝ) : ℂ)) by
      ext1 x
      rcases le_total 0 (w x) with hwx| hwx
      · simp [hwx]
      · simp [hwx]]
    exact ⟨hp.add (hn.rot _ (by simp)) hpi (hni.const_mul _) hC hC, hpi.add (hni.const_mul _)⟩
  obtain ⟨hr, hri⟩ := hdiff (fun x => (g x).re)
    (Complex.continuous_re.measurable.comp hg) (fun x => Complex.abs_re_le_norm _)
  obtain ⟨hi, hii⟩ := hdiff (fun x => (g x).im)
    (Complex.continuous_im.measurable.comp hg) (fun x => Complex.abs_im_le_norm _)
  have H : HasMaxCost g j (C+C+(C+C)) := by
    have H := hr.add (hi.rot Complex.I (by simp)) hri (hii.const_mul Complex.I)
      (by linarith) (by linarith)
    convert H using 1
    ext1 x
    rw [Pi.add_apply, mul_comm, Complex.re_add_im]
  have eq : symmetricMaximal f = symmetricMaximal g := by
    ext1 x
    simp only [symmetricMaximal, symmetricPartialSum_congr_ae hfg]
  rw [eq]
  exact H

end FourierLLogL

end OAI
