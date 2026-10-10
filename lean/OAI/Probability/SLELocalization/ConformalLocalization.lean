import Mathlib
import OAI.Probability.SLELocalization.EuclideanApproach

namespace OAI


/-! Conformal localization and Rectangle Energy estimates. -/

section
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
namespace SLEExactGauge.RectangleEnergy

theorem strip_slab_half_mean {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im})
    (hinj : InjOn F {z : ℂ | 0 < z.im}) {Fbar : ℂ → OnePoint ℂ}
    (hext : ∀ z, 0 < z.im → Fbar z = (F z : OnePoint ℂ))
    (hcont : ContinuousOn Fbar {z : ℂ | 0 ≤ z.im})
    {H r : ℝ} (hH : 0 < H) (hr : 0 < r) (q : ℂ)
    {η : ℝ → ℂ} (hη : ContinuousOn η (Icc 0 1)) (hη0 : η 0 = 0)
    (hη1 : ‖η 1‖ = 1) (hηH : ∀ t ∈ Icc 0 1, 0 ≤ (η t).im)
    (haccess : ∀ t ∈ Icc 0 1, Fbar (η t) ∈
      (fun w : ℂ => (w : OnePoint ℂ)) '' closedBall q r)
    (hlarge : 32*Real.pi*localizationMeanConstant ≤ H)
    (j : ℤ) (hj : (j:ℝ) ≤ localizationStripWidth*H) :
    stripMean H q r Fbar (unitSlab j) ≤ H/2 := by
  let K := localizationMeanConstant
  let E := totalStripEnergy H q r Fbar
  have hK : 0 < K := localizationMeanConstant_pos
  have hE : 0 ≤ E := totalStripEnergy_nonneg _ _ _ _
  have hEt := totalStripEnergy_bound hF hinj hext hH hr q
  change E ≤ 2*Real.pi*H at hEt
  have hKc : slabMeanCoefficient ≤ K := by dsimp [K,localizationMeanConstant]; linarith [Real.pi_pos]
  have hKπ : Real.pi ≤ K := by dsimp [K,localizationMeanConstant]; linarith [slabMeanCoefficient_pos]
  have hm : (stripMean H q r Fbar (unitSlab j))^2 ≤ K*(max (j:ℝ) 0+2)*E := by
    by_cases hj0 : 0 ≤ j
    · have hjr : (0:ℝ) ≤ j := by exact_mod_cast hj0
      rw [max_eq_left hjr]
      exact (positive_unitSlab_mean hF hinj hext hcont hH hr q hη hη0 hη1 hηH haccess j hjr).trans
        (by gcongr)
    · have hjr : (j:ℝ) ≤ -1 := by exact_mod_cast (show j ≤ -1 by omega)
      rw [max_eq_right (by linarith : (j:ℝ) ≤ 0),zero_add]
      exact (negative_unitSlab_mean hF hinj hext hcont hH hr q hη hη0 hη1 hηH haccess j hjr).trans
        (mul_le_mul_of_nonneg_right (by linarith) hE)
  have hmax : max (j:ℝ) 0 ≤ localizationStripWidth*H :=
    max_le hj (mul_nonneg localizationStripWidth_pos.le hH.le)
  have hbpos := localizationStripWidth_pos
  have hfinal : K*(max (j:ℝ) 0+2)*E ≤ (H/2)^2 := by
    calc
      _ ≤ K*(localizationStripWidth*H+2)*(2*Real.pi*H) := by gcongr
      _ = H^2/16+4*Real.pi*K*H := by
        unfold localizationStripWidth
        change K*((1/(32*Real.pi*K))*H+2)*(2*Real.pi*H) = _
        field_simp
        ring
      _ ≤ (H/2)^2 := by
        have ht := mul_le_mul_of_nonneg_right hlarge hH.le
        change (32*Real.pi*K)*H ≤ H*H at ht
        nlinarith
  have hh := hm.trans hfinal
  nlinarith [sq_nonneg (stripMean H q r Fbar (unitSlab j)+H/2)]

lemma unitSlab_cells_disjoint : Pairwise (fun j k : ℤ => Disjoint (unitSlab j).cells (unitSlab k).cells) := by
  intro j k hjk
  have hdis (j k : ℤ) (hjk : j < k) : Disjoint (unitSlab j).cells (unitSlab k).cells := by
    apply disjoint_left.mpr
    intro x hx hy
    change x.1 ∈ Ioc (j:ℝ) (j+1) ∧ _ at hx
    change x.1 ∈ Ioc (k:ℝ) (k+1) ∧ _ at hy
    have hjk' : (j:ℝ)+1 ≤ k := by exact_mod_cast (show j+1 ≤ k by omega)
    linarith [hx.1.2,hy.1.1]
  rcases lt_or_gt_of_ne hjk with h | h
  · exact hdis j k h
  · exact (hdis k j h).symm

lemma DRect.measure_eq_restrict (Q : DRect) : Q.measure = volume.restrict Q.cells := by
  rw [DRect.measure,DRect.cells,Measure.volume_eq_prod]
  change _ = (volume.prod volume).restrict ((Ioc Q.a Q.b) ×ˢ (Ioc Q.c Q.d))
  rw [← Measure.prod_restrict]

theorem strip_slab_energy_sum {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im})
    (hinj : InjOn F {z : ℂ | 0 < z.im}) {Fbar : ℂ → OnePoint ℂ}
    (hext : ∀ z, 0 < z.im → Fbar z = (F z : OnePoint ℂ))
    {H r : ℝ} (hH : 0 < H) (hr : 0 < r) (q : ℂ) :
    (∑' j : ℤ, ENNReal.ofReal (stripEnergy H q r Fbar (unitSlab j))) ≤
      ENNReal.ofReal (2*Real.pi*H) := by
  let G := fun p : ℝ × ℝ => ‖fderiv ℝ (stripPotential H q r Fbar) ((p.1:ℂ)+(p.2:ℂ)*Complex.I)‖^2
  let ν := (volume : Measure (ℝ × ℝ)).withDensity (fun p => ENNReal.ofReal (G p))
  let S := (univ : Set ℝ).prod (Ioc (0:ℝ) Real.pi)
  have hmeas (Q : DRect) : MeasurableSet Q.cells := measurableSet_Ioc.prod measurableSet_Ioc
  have he (j : ℤ) : ENNReal.ofReal (stripEnergy H q r Fbar (unitSlab j)) = ν (unitSlab j).cells := by
    rw [withDensity_apply _ (hmeas _)]
    have hi := (strip_gradient_rect_memLp hF hinj hext hH hr q (j:ℝ) (j+1) le_rfl le_rfl).integrable_sq
    change Integrable G (unitSlab j).measure at hi
    rw [DRect.measure_eq_restrict] at hi
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun p => sq_nonneg _))]
    congr 1
    exact congrArg (fun μ => ∫ p, G p ∂μ) (DRect.measure_eq_restrict _)
  have hS : ν S = ENNReal.ofReal (totalStripEnergy H q r Fbar) := by
    change ((volume : Measure (ℝ × ℝ)).withDensity (fun p => ENNReal.ofReal (G p)))
      ((univ : Set ℝ) ×ˢ Ioc (0:ℝ) Real.pi) = _
    rw [withDensity_apply _ (MeasurableSet.univ.prod measurableSet_Ioc)]
    change (∫⁻ p, ENNReal.ofReal (G p) ∂(volume.prod volume).restrict ((univ : Set ℝ) ×ˢ Ioc (0:ℝ) Real.pi)) = _
    rw [← Measure.prod_restrict,Measure.restrict_univ]
    have hi := strip_energy_integrable_prod hF hinj hext hH hr q
    rw [restrict_Ioo_eq_restrict_Ioc] at hi
    exact (ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun p => sq_nonneg _))).symm
  rw [tsum_congr he,← measure_iUnion unitSlab_cells_disjoint (fun j => hmeas (unitSlab j))]
  calc
    _ ≤ ν S := measure_mono (by
      intro p hp
      obtain ⟨j,hj⟩ := mem_iUnion.mp hp
      exact ⟨mem_univ _,hj.2⟩)
    _ = ENNReal.ofReal (totalStripEnergy H q r Fbar) := hS
    _ ≤ _ := ENNReal.ofReal_le_ofReal (totalStripEnergy_bound hF hinj hext hH hr q)

end SLEExactGauge.RectangleEnergy

end

end

section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal
namespace SLEExactGauge.RectangleEnergy

lemma energy_exp_linearize {A a H E : ℝ} (hA : 0 ≤ A) (ha : 0 ≤ a)
    (hH : 0 < H) (hE : 0 ≤ E) (hEt : E ≤ 2*Real.pi*H) :
    A*(E/H^2)*Real.exp (-a*H^2/E) ≤
      ((A/H^2)*Real.exp (-(a/(2*Real.pi))*H))*E := by
  by_cases h0 : E = 0
  · simp [h0]
  have hEp : 0 < E := lt_of_le_of_ne hE (Ne.symm h0)
  have hexp : -a*H^2/E ≤ -(a/(2*Real.pi))*H := by
    rw [div_le_iff₀ hEp]
    have hmul := mul_le_mul_of_nonneg_left hEt
      (by positivity : 0 ≤ a*H/(2*Real.pi))
    have hh : (a*H/(2*Real.pi))*(2*Real.pi*H) = a*H^2 := by
      field_simp
    rw [hh] at hmul
    convert neg_le_neg hmul using 1 <;> ring
  calc
    _ ≤ A*(E/H^2)*Real.exp (-(a/(2*Real.pi))*H) := by gcongr
    _ = _ := by ring

theorem energy_event_union {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
    (P : Measure Ω) (events : ι → Set Ω) (E : ι → ℝ)
    {A a H : ℝ} (hA : 0 ≤ A) (ha : 0 ≤ a) (hH : 1 ≤ H)
    (hE : ∀ j, 0 ≤ E j) (hEt : ∀ j, E j ≤ 2*Real.pi*H)
    (hsum : (∑' j, ENNReal.ofReal (E j)) ≤ ENNReal.ofReal (2*Real.pi*H))
    (hhit : ∀ j, P (events j) ≤ ENNReal.ofReal (A*(E j/H^2)*Real.exp (-a*H^2/E j))) :
    P (⋃ j, events j) ≤ ENNReal.ofReal ((2*Real.pi*A)*Real.exp (-(a/(2*Real.pi))*H)) := by
  have hHp : 0 < H := lt_of_lt_of_le zero_lt_one hH
  let k := (A/H^2)*Real.exp (-(a/(2*Real.pi))*H)
  have hk : 0 ≤ k := by dsimp [k]; positivity
  calc
    _ ≤ ∑' j, P (events j) := measure_iUnion_le _
    _ ≤ ∑' j, ENNReal.ofReal (k*E j) := ENNReal.tsum_le_tsum (fun j =>
      (hhit j).trans (ENNReal.ofReal_le_ofReal (energy_exp_linearize hA ha hHp (hE j) (hEt j))))
    _ = ENNReal.ofReal k*(∑' j, ENNReal.ofReal (E j)) := by
      simp_rw [ENNReal.ofReal_mul hk]
      exact ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal k*ENNReal.ofReal (2*Real.pi*H) := by gcongr
    _ = ENNReal.ofReal (k*(2*Real.pi*H)) := (ENNReal.ofReal_mul hk).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      have hid : k*(2*Real.pi*H) = (2*Real.pi*A/H)*Real.exp (-(a/(2*Real.pi))*H) := by
        dsimp [k]
        field_simp
      rw [hid]
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact div_le_self (by positivity) hH)

end SLEExactGauge.RectangleEnergy

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology ENNReal NNReal
namespace SLEExactGauge.RectangleEnergy

def logEnergyExit {Ω : Type*} (γ : Ω → ℝ → ℂ) (Fbar : ℂ → OnePoint ℂ)
    (H : ℝ) (q : ℂ) (r : ℝ) (ω : Ω) : Prop :=
  ∃ x ∈ logTrace γ ω, x.1 ≤ localizationStripWidth*H ∧ 0 ≤ x.2 ∧ x.2 ≤ Real.pi ∧
    stripPotential H q r Fbar ((x.1:ℂ)+(x.2:ℂ)*Complex.I) = H

lemma rectCoefficient_unitSlab (j : ℝ) :
    rectCoefficient (unitSlab j) = rectCoefficient (unitSlab 0) := by
  unfold rectCoefficient unitSlab
  dsimp only
  rw [show j+1-j=1 by ring]
  norm_num

theorem logTrace_localization (κ : ℝ) (hκ : 0 < κ ∧ κ < 8) :
    ∃ c C H₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < H₀ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ≥0 → Ω → ℝ) (_hB : IsBrownianReal B P)
        (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
        (_hγ : ∀ t, 0 ≤ t → AEMeasurable (fun sample => γ sample t) P)
        (_hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
          (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
        (F : ℂ → ℂ) (_hF : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im})
        (_hinj : InjOn F {z : ℂ | 0 < z.im}) (Fbar : ℂ → OnePoint ℂ)
        (_hext : ∀ z, 0 < z.im → Fbar z = (F z : OnePoint ℂ))
        (_hcont : ContinuousOn Fbar {z : ℂ | 0 ≤ z.im})
        (q : ℂ) (r : ℝ) (_hr : 0 < r)
        (η : ℝ → ℂ) (_hη : ContinuousOn η (Icc 0 1)) (_hη0 : η 0 = 0)
        (_hη1 : ‖η 1‖ = 1) (_hηH : ∀ t ∈ Icc 0 1, 0 ≤ (η t).im)
        (_haccess : ∀ t ∈ Icc 0 1, Fbar (η t) ∈
          (fun w : ℂ => (w : OnePoint ℂ)) '' closedBall q r)
        (H : ℝ), H₀ ≤ H → P {ω | logEnergyExit γ Fbar H q r ω} ≤
          ENNReal.ofReal (C*Real.exp (-c*H)) := by
  obtain ⟨C₀,ρ,hC₀,hρ,hρ1,hhit⟩ := logTrace_dyadic_hitting κ hκ
  let D := rectCoefficient (unitSlab 0)
  let T := ∑' j : ℕ, (((j:ℝ)+1)*((j:ℝ)+2))^2*ρ^j
  let A := 64*D*(C₀+1)*(T+1)/ρ
  let a := (-Real.log ρ)/(48*D)
  let H₀ := max 1 (32*Real.pi*localizationMeanConstant)
  have hD : 0 < D := rectCoefficient_pos _
  have hT : 0 ≤ T := tsum_nonneg (fun j => mul_nonneg (sq_nonneg _) (pow_nonneg hρ.le j))
  have hA : 0 < A := by dsimp [A]; positivity
  have ha : 0 < a := div_pos (neg_pos.2 (Real.log_neg hρ hρ1)) (by positivity)
  have hH₀ : 0 < H₀ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨a/(2*Real.pi),2*Real.pi*A,H₀,by positivity,by positivity,hH₀,?_⟩
  intro Ω _ P _ B hB γ g f hγ hmaps F hF hinj Fbar hext hcont q r hr η hη hη0 hη1 hηH haccess H hlarge
  have hH1 : 1 ≤ H := (le_max_left _ _).trans hlarge
  have hH : 0 < H := lt_of_lt_of_le zero_lt_one hH1
  have hHH : 32*Real.pi*localizationMeanConstant ≤ H := (le_max_right _ _).trans hlarge
  let E := fun j : ℤ => stripEnergy H q r Fbar (unitSlab j)
  let events := fun j : ℤ => {ω | (j:ℝ) ≤ localizationStripWidth*H ∧
    ∃ x ∈ logTrace γ ω, x ∈ (unitSlab j).closed ∧
      stripPotential H q r Fbar ((x.1:ℂ)+(x.2:ℂ)*Complex.I) = H}
  have hsub : {ω | logEnergyExit γ Fbar H q r ω} ⊆ ⋃ j, events j := by
    rintro ω ⟨x,hx,hxv,hx0,hxπ,hxH⟩
    apply mem_iUnion.mpr
    refine ⟨Int.floor x.1,?_,x,hx,?_,hxH⟩
    · exact (Int.floor_le x.1).trans hxv
    · exact ⟨⟨Int.floor_le x.1,(Int.lt_floor_add_one x.1).le⟩,hx0,hxπ⟩
  have hE : ∀ j, 0 ≤ E j := fun j => integral_nonneg (fun _ => sq_nonneg _)
  have hEt : ∀ j, E j ≤ 2*Real.pi*H := fun j =>
    (stripEnergy_le_total hF hinj hext hH hr q (unitSlab j) le_rfl le_rfl).trans
      (totalStripEnergy_bound hF hinj hext hH hr q)
  have hsum := strip_slab_energy_sum hF hinj hext hH hr q
  have hev (j : ℤ) : P (events j) ≤ ENNReal.ofReal (A*(E j/H^2)*Real.exp (-a*H^2/E j)) := by
    by_cases hj : (j:ℝ) ≤ localizationStripWidth*H
    · have hm := strip_slab_half_mean hF hinj hext hcont hH hr q hη hη0 hη1 hηH haccess hHH j hj
      have hb := strip_rectangle_hitting hF hinj hext hcont hH hr q (unitSlab j) le_rfl le_rfl hm
        P (logTrace γ) hC₀.le hρ hρ1 (hhit P B hB γ g f hγ hmaps j)
      dsimp only at hb
      rw [rectCoefficient_unitSlab] at hb
      change P _ ≤ ENNReal.ofReal (A*(E j/H^2)*Real.exp (-a*H^2/E j)) at hb
      exact (measure_mono (fun ω hω => hω.2)).trans hb
    · have he : events j = ∅ := by ext ω; simp [events,hj]
      rw [he,measure_empty]
      exact bot_le
  exact (measure_mono hsub).trans (energy_event_union P events E hA.le ha.le hH1 hE hEt hsum hev)

end SLEExactGauge.RectangleEnergy

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology ENNReal NNReal OnePoint
namespace SLEExactGauge
open RectangleEnergy

def conformalExit (Fbar : ℂ → OnePoint ℂ) (γ : ℝ → ℂ)
    (q : ℂ) (radius A : ℝ) : Prop :=
  ∃ t : ℝ, 0 ≤ t ∧ (∀ s : ℝ, 0 ≤ s → s < t → ‖γ s‖ < A) ∧
    Fbar (γ t) ∉ (fun w : ℂ => (w : OnePoint ℂ)) '' Metric.ball q radius

lemma norm_le_of_pre_modulus {γ : ℝ → ℂ} (hc : ContinuousOn γ (Ici 0))
    (h0 : γ 0 = 0) {t A : ℝ} (ht : 0 ≤ t) (hA : 0 < A)
    (hpre : ∀ s : ℝ, 0 ≤ s → s < t → ‖γ s‖ < A) : ‖γ t‖ ≤ A := by
  by_contra hn
  have hgt : A < ‖γ t‖ := lt_of_not_ge hn
  have hm : A ∈ Icc ‖γ 0‖ ‖γ t‖ := by simpa [h0] using And.intro hA.le hgt.le
  obtain ⟨s,hs,he⟩ := intermediate_value_Icc ht (hc.mono Icc_subset_Ici_self).norm hm
  have hst : s < t := lt_of_le_of_ne hs.2 (by intro heq; subst s; linarith)
  exact (ne_of_lt (hpre s hs.1 hst)) he

lemma conformalExit_logEnergyExit {Ω : Type*} {γ : Ω → ℝ → ℂ}
    {ω : Ω} {Fbar : ℂ → OnePoint ℂ} {q : ℂ} {r L : ℝ}
    (hr : 0 < r) (hL : 1 < L) (hc : ContinuousOn (γ ω) (Ici 0))
    (h0 : γ ω 0 = 0) (hhalf : ∀ t, 0 ≤ t → 0 ≤ (γ ω t).im)
    (hstart : Fbar 0 ∈ (fun w : ℂ => (w : OnePoint ℂ)) '' closedBall q r)
    (hexit : conformalExit Fbar (γ ω) q (L*r) (L^localizationStripWidth)) :
      logEnergyExit γ Fbar (Real.log L) q r ω := by
  obtain ⟨t,ht,hpre,hout⟩ := hexit
  have hLp : 0 < L := zero_lt_one.trans hL
  have hz : γ ω t ≠ 0 := by
    intro he
    apply hout
    rw [he]
    obtain ⟨w,hw,heq⟩ := hstart
    refine ⟨w,?_,heq⟩
    exact mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hw) (by nlinarith))
  have hn := norm_le_of_pre_modulus hc h0 ht (Real.rpow_pos_of_pos hLp _) hpre
  let x : ℝ × ℝ := (Real.log ‖γ ω t‖, Complex.arg (γ ω t))
  have hexp : Complex.exp ((x.1:ℂ)+(x.2:ℂ)*Complex.I) = γ ω t := by
    change Complex.exp (Complex.log (γ ω t)) = γ ω t
    exact Complex.exp_log hz
  refine ⟨x,⟨t,ht,hexp.symm⟩,?_,Complex.arg_nonneg_iff.2 (hhalf t ht),Complex.arg_le_pi _,?_⟩
  · have hb := Real.log_le_log (norm_pos_iff.2 hz) hn
    rw [Real.log_rpow hLp] at hb
    exact hb
  · unfold stripPotential
    rw [hexp]
    apply sphereTruncation_top_of_outside (Real.log_pos hL).le hr q
    simpa [Real.exp_log hLp] using hout

theorem uniform_conformal_localization (κ : ℝ) (hκ : 0 < κ ∧ κ < 8) :
    ∃ b c C L₀ : ℝ, 0 < b ∧ 0 < c ∧ 0 < C ∧ 1 < L₀ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ≥0 → Ω → ℝ) (_hB : IsBrownianReal B P)
        (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
        (_hγ : ∀ t, 0 ≤ t → AEMeasurable (fun sample => γ sample t) P)
        (_hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
          (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
        (F : ℂ → ℂ) (Fbar : ℂ → OnePoint ℂ)
        (_hF : AnalyticOnNhd ℂ F halfPlane) (_hinj : Set.InjOn F halfPlane)
        (_hext : ∀ z ∈ halfPlane, Fbar z = (F z : OnePoint ℂ))
        (_hcont : ContinuousOn Fbar {z : ℂ | 0 ≤ z.im})
        (η : ℝ → ℂ) (_hη : ContinuousOn η (Icc 0 1)) (_hη0 : η 0 = 0)
        (_hη1 : ‖η 1‖ = 1) (_hηH : ∀ t ∈ Icc 0 1, 0 ≤ (η t).im)
        (q : ℂ) (r : ℝ) (_hr : 0 < r)
        (_haccess : ∀ t ∈ Icc 0 1, Fbar (η t) ∈
          (fun w : ℂ => (w : OnePoint ℂ)) '' Metric.closedBall q r)
        (L : ℝ), L₀ ≤ L →
        P {sample | conformalExit Fbar (γ sample) q (L*r) (L^b)} ≤
          ENNReal.ofReal (C*L^(-c)) := by
  obtain ⟨c,C,H₀,hc,hC,hH₀,hlog⟩ := logTrace_localization κ hκ
  refine ⟨localizationStripWidth,c,C,Real.exp (H₀+1),localizationStripWidth_pos,hc,hC,?_,?_⟩
  · exact Real.one_lt_exp_iff.2 (by linarith)
  intro Ω _ P _ B hB γ g f hγ hmaps F Fbar hF hinj hext hcont η hη hη0 hη1 hηH q r hr haccess L hlarge
  have hL : 1 < L := (Real.one_lt_exp_iff.2 (by linarith : 0 < H₀+1)).trans_le hlarge
  have hLp : 0 < L := zero_lt_one.trans hL
  have hH : H₀ ≤ Real.log L := by
    have hh := Real.log_le_log (Real.exp_pos (H₀+1)) hlarge
    rw [Real.log_exp] at hh
    linarith
  have hstart : Fbar 0 ∈ (fun w : ℂ => (w : OnePoint ℂ)) '' closedBall q r := by
    simpa [hη0] using haccess 0 (by norm_num : (0:ℝ) ∈ Icc 0 1)
  have hm : P {ω | conformalExit Fbar (γ ω) q (L*r) (L^localizationStripWidth)} ≤
      P {ω | logEnergyExit γ Fbar (Real.log L) q r ω} := by
    apply measure_mono_ae
    filter_upwards [hmaps] with ω hw
    intro hexit
    exact conformalExit_logEnergyExit hr hL hw.1 hw.2.1 hw.2.2.1 hstart hexit
  have hb := hlog P B hB γ g f hγ hmaps F hF hinj Fbar hext hcont q r hr η hη hη0 hη1 hηH haccess (Real.log L) hH
  have he : Real.exp (-c*Real.log L) = L^(-c) := by
    rw [Real.rpow_def_of_pos hLp]
    congr 1
    ring
  rw [he] at hb
  exact hm.trans hb

end SLEExactGauge

end

end

end OAI
