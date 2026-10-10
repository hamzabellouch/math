import Mathlib
import OAI.Probability.SLE.PhysicalMeshWindowCore
import OAI.Probability.SLE.WindowBGeometry

namespace OAI

/-! Physical Mesh Past for chordal SLE. -/

section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable

lemma source_mesh_shift_integral (c : ℂ) (D : Set ℂ) (f : ℂ → ℝ) :
    (∫ z in ((fun z : ℂ => z+c) ⁻¹' D), f (z+c)) = ∫ z in D, f z := by
  exact (measurePreserving_add_right volume c).setIntegral_preimage_emb
    (MeasurableEquiv.addRight c).measurableEmbedding f D

lemma source_mesh_shifted_weighted_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ℱ : Filtration ℝ≥0 mΩ} {D : Set ℂ} {r R K : ℝ} {γ : ℝ≥0 → Ω → ℂ}
    {σ τ : ℂ → Ω → WithTop ℝ≥0} {Y μ : ℂ → Ω → ℝ} (c : ℂ)
    (h : SourceDisjointWindows P ℱ ((fun z : ℂ => z+c) ⁻¹' D) r R K γ
      (fun z => σ (z+c)) (fun z => τ (z+c)) (fun z => Y (z+c)) (fun z => μ (z+c)))
    (hs : ∀ z, IsStoppingTime ℱ (σ z))
    (hK : 0 < K) {b : ℝ} (hb : 0 < b)
    {W : Ω → ℝ} (hWa : Measurable[mΩ] W)
    (hWs : ∀ z, Measurable[(hs z).measurableSpace] W)
    (hW0 : ∀ ω, 0 ≤ W ω) (hWb : ∃ M, ∀ ω, W ω ≤ M) :
    (∫ ω, W ω*(if b < ∫ z in D, (Y z ω-μ z ω) then (1:ℝ) else 0) ∂P) ≤
      (∫ ω, W ω ∂P)*Real.exp (-(1/512:ℝ)*b^2/(K^2*R^2)) := by
  have hh := window_source_weighted_tail h hK hb hWa (fun z => hWs (z+c)) hW0 hWb
  have he (ω : Ω) : (∫ z in ((fun z : ℂ => z+c) ⁻¹' D), (Y (z+c) ω-μ (z+c) ω)) =
      ∫ z in D, (Y z ω-μ z ω) := source_mesh_shift_integral c D (fun z => Y z ω-μ z ω)
  simpa only [he] using hh

lemma source_mesh_center_before
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (D : Set ℂ) (c : ℂ) (hD : D ⊆ ball c 1) (η r : ℝ)
    (hη : 0 < η) (hr : r < η/2) (hc : 1+η ≤ c.im)
    (hy : ∀ z ∈ D, r ≤ z.im) (z : ℂ) (ω : a.samples) :
    spatialHitTime (γ ω) c (1+η/2) ≤ sourceCollarStart D (γ ω) z r := by
  by_cases hz : z ∈ D
  · simp only [sourceCollarStart,ite_eq_left hz]
    by_cases hn : liveSpatialHitTime (γ ω) z r = ⊤
    · rw [hn]; exact le_top
    obtain ⟨T,hT⟩ := WithTop.ne_top_iff_exists.mp hn
    have hcontact := (source_liveHit_mem (a.trace_continuous ω) z r
      (source_window_origin_bound a z r (hy z hz) ω) T hT.symm).2
    have hd : dist (γ ω T) c < 1+η/2 := by
      have hz' := hD hz
      change dist z c < 1 at hz'
      have ht := dist_triangle (γ ω T) z c
      linarith
    have hstart : 1+η/2 ≤ dist (γ ω 0) c := by
      rw [(a.witness ω).2.1,dist_zero_left]
      have hi : c.im ≤ ‖c‖ := (le_abs_self _).trans (Complex.abs_im_le_norm c)
      linarith
    rw [← hT]
    exact (spatialHitTime_lt_of_dist_lt (a.trace_continuous ω) c _ hstart T hd).le
  · rw [sourceCollarStart,ite_eq_right hz]
    exact le_top

lemma source_mesh_center_stopping
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (c : ℂ) (η : ℝ) :
    IsStoppingTime a.filtration (fun ω : a.samples => spatialHitTime (γ ω) c (1+η/2)) := by
  let X (t : ℝ≥0) (ω : a.samples) := dist (γ ω t) c - (1+η/2)
  have ha : Adapted a.filtration X := by
    intro t
    let : MeasurableSpace a.samples := a.filtration t
    exact ((a.trace_adapted t).dist measurable_const).sub_const _
  exact continuous_zero_hit_stopping a.filtration X ha
    (fun ω => ((a.trace_continuous ω).dist continuous_const).sub continuous_const) 0

lemma source_mesh_free_im {γ : ℝ≥0 → ℂ} {s : ℝ≥0} {c : ℂ} {η : ℝ}
    (hη : 0 < η) (hfree : closedBall c (1+η) ⊆ survivingDomain γ s) :
    1+η < c.im := by
  let z := c-((1+η:ℝ):ℂ)*Complex.I
  have hz : z ∈ closedBall c (1+η) := by
    rw [mem_closedBall,dist_eq_norm]
    simp only [z,sub_sub_cancel_left,norm_neg,norm_mul,Complex.norm_real,Complex.norm_I,mul_one]
    rw [Real.norm_eq_abs,abs_of_pos (by linarith)]
  have hi := (hfree hz).1.1
  change 0 < z.im at hi
  simpa [z] using hi

lemma source_mesh_free_before_center {γ : ℝ≥0 → ℂ} (hγ : Continuous γ)
    (s : ℝ≥0) (c : ℂ) (η : ℝ) (hη : 0 < η)
    (hfree : closedBall c (1+η) ⊆ survivingDomain γ s) :
    (s : WithTop ℝ≥0) ≤ spatialHitTime γ c (1+η/2) := by
  by_contra! hn
  obtain ⟨t,ht,hcontact⟩ := (spatialHitTime_le_iff hγ c (1+η/2) s).mp hn.le
  have hin : γ t ∈ closedBall c (1+η) := by
    rw [mem_closedBall,hcontact]; linarith
  exact (hfree hin).1.2 (mem_image_of_mem γ ht)

lemma source_past_indicator_at_start
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {ℱ : Filtration ℝ≥0 mΩ}
    {ρ τ σ : Ω → WithTop ℝ≥0} (hρ : IsStoppingTime ℱ ρ)
    (hτ : IsStoppingTime ℱ τ) (hσ : IsStoppingTime ℱ σ) (hle : ∀ ω, τ ω ≤ σ ω)
    (A : Set Ω) (hA : MeasurableSet[hρ.measurableSpace] A) :
    Measurable[hσ.measurableSpace] (fun ω => if ω ∈ A ∧ ρ ω ≤ τ ω then (1:ℝ) else 0) := by
  have hB : MeasurableSet[hσ.measurableSpace] {ω | ρ ω ≤ τ ω} :=
    (hτ.measurableSpace_mono hσ hle) _ (hρ.measurableSet_stopping_time_le hτ)
  have hI : Measurable[hρ.measurableSpace] (fun ω => if ω ∈ A then (1:ℝ) else 0) :=
    Measurable.ite hA measurable_const measurable_const
  have hh := window_measurable_on_event hσ hρ hI hB (fun ω hω => hω.trans (hle ω)) 0
  convert hh using 1
  funext ω
  by_cases ha : ω ∈ A <;> by_cases hb : ρ ω ≤ τ ω <;> simp [ha,hb]

end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable

lemma source_mesh_integrated_step
    {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (W W' I I' H V B : X → ℝ) (p q r C A b : ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hr : 0 < r) (hp : 0 < p)
    (_hW : Integrable W ν) (hW' : Integrable W' ν)
    (_hI : Integrable I ν) (hI' : Integrable I' ν)
    (hH : Integrable H ν) (hV : Integrable V ν) (hB : Integrable B ν)
    (hb : 0 ≤ b)
    (hmissI : ∀ᵐ z ∂ν, I' z ≤ H z+B z)
    (hmissW : ∀ᵐ z ∂ν, W' z ≤ r^(-p)*V z+(q*r)^(-p)*B z)
    (hmeanH : (∫ z, H z ∂ν) ≤ C*(q*r)^p*(∫ z, W z ∂ν)+b)
    (hmeanV : (∫ z, V z ∂ν) ≤ r^p*(∫ z, W z ∂ν)+b)
    (hmeanB : (∫ z, B z ∂ν) ≤ A*(∫ z, I z ∂ν)+b) :
    (∫ z, W' z ∂ν) ≤ (∫ z, W z ∂ν)+(A*q^(-p))*(r^(-p)*(∫ z, I z ∂ν))+
       (2*q^(-p))*r^(-p)*b ∧
    (q*r)^(-p)*(∫ z, I' z ∂ν) ≤ C*(∫ z, W z ∂ν)+
       (A*q^(-p))*(r^(-p)*(∫ z, I z ∂ν))+(2*q^(-p))*r^(-p)*b := by
  have hrp : 0 ≤ r^(-p) := (Real.rpow_pos_of_pos hr _).le
  have hqp : 0 ≤ (q*r)^(-p) := (Real.rpow_pos_of_pos (mul_pos hq hr) _).le
  have hq1p : 1 ≤ q^(-p) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hq hq1.le (neg_nonpos.mpr hp.le)
  have hcancel : r^(-p)*r^p = 1 := by rw [←Real.rpow_add hr,neg_add_cancel,Real.rpow_zero]
  have hcancelq : (q*r)^(-p)*(q*r)^p = 1 := by rw [←Real.rpow_add (mul_pos hq hr),neg_add_cancel,Real.rpow_zero]
  have hmul : (q*r)^(-p) = q^(-p)*r^(-p) := Real.mul_rpow hq.le hr.le
  constructor
  · calc
      _ ≤ ∫ z, (r^(-p)*V z+(q*r)^(-p)*B z) ∂ν :=
        integral_mono_ae hW' ((hV.const_mul _).add (hB.const_mul _)) hmissW
      _ = r^(-p)*(∫ z, V z ∂ν)+(q*r)^(-p)*(∫ z, B z ∂ν) := by
        rw [integral_add (hV.const_mul _) (hB.const_mul _),integral_const_mul,integral_const_mul]
      _ ≤ r^(-p)*(r^p*(∫ z, W z ∂ν)+b)+(q*r)^(-p)*(A*(∫ z,I z ∂ν)+b) :=
        add_le_add (mul_le_mul_of_nonneg_left hmeanV hrp) (mul_le_mul_of_nonneg_left hmeanB hqp)
      _ ≤ _ := by rw [mul_add,←mul_assoc,hcancel,one_mul,hmul]; nlinarith [mul_nonneg (sub_nonneg.mpr hq1p) (mul_nonneg hrp hb)]
  · calc
      _ ≤ (q*r)^(-p)*(∫ z, (H z+B z) ∂ν) := mul_le_mul_of_nonneg_left
        (integral_mono_ae hI' (hH.add hB) hmissI) hqp
      _ = (q*r)^(-p)*((∫ z,H z ∂ν)+(∫ z,B z ∂ν)) := by rw [integral_add hH hB]
      _ ≤ (q*r)^(-p)*(C*(q*r)^p*(∫ z,W z ∂ν)+b+(A*(∫ z,I z ∂ν)+b)) :=
        mul_le_mul_of_nonneg_left (add_le_add hmeanH hmeanB) hqp
      _ = _ := by
        calc
          _ = C*((q*r)^(-p)*(q*r)^p)*(∫ z,W z ∂ν)+(q*r)^(-p)*(A*(∫ z,I z ∂ν))+2*(q*r)^(-p)*b := by ring
          _ = _ := by rw [hcancelq,hmul]; ring

lemma source_collar_missed
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) (hκ8 : κ < 8) (D : Set ℂ) (q r L : ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hr : 0 < r) (hL : 1 < L)
    (hy : ∀ z ∈ D, r ≤ z.im) (ω : a.samples) (z : ℂ) (hz : z ∈ D) :
    (if sourceCollarStart D (γ ω) z (q*r) = ⊤ then (0:ℝ) else 1) ≤
      sourceCollarH D (γ ω) z r (q*r) (L*r)+sourceCollarB D (γ ω) z r (q*r) (L*r) ∧
    spatialGreenWeight κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z (q*r) ≤
      r^(-codimension κ)*(r^codimension κ*spatialGreenWeight κ
        (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z (q*r)*sourceCollarH D (γ ω) z r (q*r) (L*r))+
      (q*r)^(-codimension κ)*sourceCollarB D (γ ω) z r (q*r) (L*r) := by
  have hh := sourceSpatialWindowGeometry_proved (fun t => Real.sqrt κ*a.B t ω)
    (γ ω) (a.G ω) (a.F ω) ((a.continuous_B ω).const_mul _) (a.witness ω) κ hκ hκ8
    z (q*r) r (L*r) (mul_pos hq hr) (by nlinarith) (by nlinarith) (hy z hz)
  simp only [sourceCollarStart,sourceCollarH,sourceCollarB,ite_eq_left hz]
  refine ⟨hh.2.2.2.2.2.2.2.2.2.2.1,?_⟩
  have he : r^(-codimension κ)*r^codimension κ = 1 := by
    rw [←Real.rpow_add hr,neg_add_cancel,Real.rpow_zero]
  simpa only [←mul_assoc,he,one_mul] using hh.2.2.2.2.2.2.2.2.2.2.2

lemma source_mesh_bounded_integrable {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsFiniteMeasure ν] {f : X → ℝ} {K : ℝ}
    (hm : Measurable f) (hb : ∀ x, 0 ≤ f x ∧ f x ≤ K) : Integrable f ν := by
  apply Integrable.of_bound hm.aestronglyMeasurable K
  exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hb x).1] using (hb x).2)

end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable

lemma source_mesh_shifted_integral_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ} {D : Set ℂ} {r R K : ℝ} {γ : ℝ≥0 → Ω → ℂ}
    {σ τ : ℂ → Ω → WithTop ℝ≥0} {Y μ : ℂ → Ω → ℝ} (c : ℂ)
    (h : SourceDisjointWindows P ℱ ((fun z : ℂ => z+c) ⁻¹' D) r R K γ
      (fun z => σ (z+c)) (fun z => τ (z+c)) (fun z => Y (z+c)) (fun z => μ (z+c))) :
    Measurable (fun ω => ∫ z in D, (Y z ω-μ z ω)) := by
  have hm := window_source_integral_measurable h
  have he (ω : Ω) : (∫ z in ((fun z : ℂ => z+c) ⁻¹' D), (Y (z+c) ω-μ (z+c) ω)) =
      ∫ z in D, (Y z ω-μ z ω) := source_mesh_shift_integral c D (fun z => Y z ω-μ z ω)
  simpa only [he] using hm

lemma source_mesh_shifted_restricted_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ℱ : Filtration ℝ≥0 mΩ} {D : Set ℂ} {r R K : ℝ} {γ : ℝ≥0 → Ω → ℂ}
    {σ τ : ℂ → Ω → WithTop ℝ≥0} {Y μ : ℂ → Ω → ℝ} (c : ℂ)
    (h : SourceDisjointWindows P ℱ ((fun z : ℂ => z+c) ⁻¹' D) r R K γ
      (fun z => σ (z+c)) (fun z => τ (z+c)) (fun z => Y (z+c)) (fun z => μ (z+c)))
    (hs : ∀ z, IsStoppingTime ℱ (σ z))
    (hK : 0 < K) {b : ℝ} (hb : 0 < b)
    (E : Set Ω) (hE : MeasurableSet[mΩ] E) (hEs : ∀ z, MeasurableSet[(hs z).measurableSpace] E) :
    (P.restrict E) {ω | b < ∫ z in D, (Y z ω-μ z ω)} ≤
      ENNReal.ofReal (P.real E*Real.exp (-(1/512:ℝ)*b^2/(K^2*R^2))) := by
  let F := {ω | b < ∫ z in D, (Y z ω-μ z ω)}
  have hF : MeasurableSet F := measurableSet_lt measurable_const (source_mesh_shifted_integral_measurable c h)
  have hWm : Measurable (fun ω => if ω ∈ E then (1:ℝ) else 0) :=
    Measurable.ite hE measurable_const measurable_const
  have hWs : ∀ z, Measurable[(hs z).measurableSpace] (fun ω => if ω ∈ E then (1:ℝ) else 0) :=
    fun z => Measurable.ite (hEs z) measurable_const measurable_const
  have hh := source_mesh_shifted_weighted_tail c h hs hK hb hWm hWs
    (fun ω => by split_ifs <;> norm_num) ⟨1,fun ω => by split_ifs <;> norm_num⟩
  have hi : (fun ω => (if ω ∈ E then (1:ℝ) else 0)*(if ω ∈ F then (1:ℝ) else 0)) =
      (F∩E).indicator 1 := by
    funext ω; by_cases he : ω ∈ E <;> by_cases hf : ω ∈ F <;> simp [he,hf]
  change (∫ ω, (if ω ∈ E then (1:ℝ) else 0)*(if ω ∈ F then (1:ℝ) else 0) ∂P) ≤ _ at hh
  rw [hi,integral_indicator_one (hF.inter hE)] at hh
  have hiE : (fun ω => if ω ∈ E then (1:ℝ) else 0) = E.indicator 1 := rfl
  rw [hiE,integral_indicator_one hE] at hh
  rw [Measure.restrict_apply hF]
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).mpr hh

end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable

noncomputable def sourceMeshCount (p : ℝ) (D : Set ℂ) (γ : ℝ≥0 → ℂ) (r : ℝ) : ℝ :=
  r^(-p)*∫ z in D, if sourceCollarStart D γ z r = ⊤ then (0:ℝ) else 1

lemma source_mesh_I_integrable
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (D : Set ℂ) (hD : MeasurableSet D) [IsFiniteMeasure (volume.restrict D)]
    (v : ℝ) (hy : ∀ z ∈ D, v ≤ z.im) (ω : a.samples) :
    IntegrableOn (fun z => if sourceCollarStart D (γ ω) z v = ⊤ then (0:ℝ) else 1) D := by
  have hm : Measurable (fun p : ℂ × a.samples =>
      if sourceCollarStart D (γ p.2) p.1 v = ⊤ then (0:ℝ) else 1) :=
    Measurable.ite (measurableSet_eq_fun (source_collarStart_joint a D hD v hy) measurable_const)
      measurable_const measurable_const
  exact source_mesh_bounded_integrable (K := 1)
    (hm.comp (measurable_id.prodMk (measurable_const : Measurable (fun _ : ℂ => ω)))) (fun z => by split_ifs <;> norm_num)

lemma source_mesh_integral_recurrences
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (D : Set ℂ) (hD : MeasurableSet D) (c₀ : ℂ) (hDc : D ⊆ ball c₀ 1)
    (q r L C Cbad c b : ℝ) (hq : 0 < q) (hq1 : q < 1) (hr : 0 < r)
    (hL : 1 < L) (hb : 0 ≤ b) (hy : ∀ z ∈ D, r ≤ z.im) (ω : a.samples) :
    let p := codimension κ
    let W := fun v z => spatialGreenWeight κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z v
    let Ic := fun v z => if sourceCollarStart D (γ ω) z v = ⊤ then (0:ℝ) else 1
    let H := fun z => sourceCollarH D (γ ω) z r (q*r) (L*r)
    let B := fun z => sourceCollarB D (γ ω) z r (q*r) (L*r)
    let V := fun z => r^p*W (q*r) z*H z
    let μH := fun z => C*(q*r)^p*(if z ∈ D then W r z else 0)
    let μV := fun z => r^p*(if z ∈ D then W r z else 0)
    let μB := fun z => Cbad*L^(-c)*Ic r z
    (∫ z in D, (H z-μH z)) ≤ b → (∫ z in D, (V z-μV z)) ≤ b → (∫ z in D, (B z-μB z)) ≤ b →
      spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (q*r) D ≤
        spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) r D+
        (Cbad*L^(-c)*q^(-p))*sourceMeshCount p D (γ ω) r+(2*q^(-p))*r^(-p)*b ∧
      sourceMeshCount p D (γ ω) (q*r) ≤
        C*spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) r D+
        (Cbad*L^(-c)*q^(-p))*sourceMeshCount p D (γ ω) r+(2*q^(-p))*r^(-p)*b := by
  intro p W Ic H B V μH μV μB hFH hFV hFB
  change (∫ z in D, W (q*r) z) ≤ (∫ z in D, W r z)+
    (Cbad*L^(-c)*q^(-p))*(r^(-p)*(∫ z in D, Ic r z))+(2*q^(-p))*r^(-p)*b ∧
    (q*r)^(-p)*(∫ z in D, Ic (q*r) z) ≤ C*(∫ z in D, W r z)+
    (Cbad*L^(-c)*q^(-p))*(r^(-p)*(∫ z in D, Ic r z))+(2*q^(-p))*r^(-p)*b
  have hp : 0 < p := by dsimp [p,codimension,dimension]; linarith
  have hfin : volume D ≠ ∞ := ne_top_of_le_ne_top (by finiteness : volume (ball c₀ 1) ≠ ∞) (measure_mono hDc)
  let : IsFiniteMeasure (volume.restrict D) := ⟨by simpa only [Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr hfin⟩
  have hqr : q*r ≤ r := (mul_le_mul_of_nonneg_right hq1.le hr.le).trans_eq (one_mul _)
  have hWi (v : ℝ) (hv : 0 < v) (hvr : v ≤ r) : IntegrableOn (fun z => W v z) D :=
    a.spatialGreenWeight_spatial_integrable hκ hκ8 v hv D hD hfin (fun z hz => hvr.trans (hy z hz)) ω
  have hIi (v : ℝ) (hvr : v ≤ r) : IntegrableOn (fun z => Ic v z) D :=
    source_mesh_I_integrable a D hD v (fun z hz => hvr.trans (hy z hz)) ω
  have hHi : IntegrableOn (fun z => H z) D := source_mesh_bounded_integrable
    ((source_collarHB_joint a D hD r (q*r) (L*r) hy).1.comp (measurable_id.prodMk (measurable_const : Measurable (fun _ : ℂ => ω))))
    (fun z => (source_collar_HB_bounds D (γ ω) z r (q*r) (L*r)).1)
  have hBi : IntegrableOn (fun z => B z) D := source_mesh_bounded_integrable
    ((source_collarHB_joint a D hD r (q*r) (L*r) hy).2.comp (measurable_id.prodMk (measurable_const : Measurable (fun _ : ℂ => ω))))
    (fun z => (source_collar_HB_bounds D (γ ω) z r (q*r) (L*r)).2)
  have hVm : Measurable (fun p : ℂ × a.samples => r^codimension κ*spatialGreenWeight κ
      (fun t => Real.sqrt κ*a.B t p.2) (γ p.2) (a.G p.2) p.1 (q*r)*sourceCollarH D (γ p.2) p.1 r (q*r) (L*r)) := by
    simpa only [add_zero] using source_collar_V_joint a D hD 0 q r L hy
  have hmsec : Measurable (fun z : ℂ => (z,ω)) := measurable_id.prodMk measurable_const
  have hVsec := hVm.comp hmsec
  simp only [Function.comp_def] at hVsec
  have hVi : IntegrableOn V D := source_mesh_bounded_integrable hVsec
    (fun z => source_collar_V_bounds a hκ hκ8 D q r (L*r) hq hq1 hr hy z ω)
  have hWceq : (fun z => if z ∈ D then W r z else 0) =ᵐ[volume.restrict D] (fun z => W r z) := by
    filter_upwards [ae_restrict_mem hD] with z hz; simp only [ite_eq_left hz]
  have hWci : IntegrableOn (fun z => if z ∈ D then W r z else 0) D := (hWi r hr le_rfl).congr hWceq.symm
  have hiH : (∫ z in D, μH z) = C*(q*r)^p*(∫ z in D, W r z) := by
    rw [show (∫ z in D, μH z) = C*(q*r)^p*(∫ z in D, if z ∈ D then W r z else 0) from integral_const_mul _ _,integral_congr_ae hWceq]
  have hiV : (∫ z in D, μV z) = r^p*(∫ z in D, W r z) := by
    rw [show (∫ z in D, μV z) = r^p*(∫ z in D, if z ∈ D then W r z else 0) from integral_const_mul _ _,integral_congr_ae hWceq]
  have hiB : (∫ z in D, μB z) = Cbad*L^(-c)*(∫ z in D, Ic r z) := integral_const_mul _ _
  rw [integral_sub hHi (hWci.const_mul _),hiH] at hFH
  rw [integral_sub hVi (hWci.const_mul _),hiV] at hFV
  rw [integral_sub hBi ((hIi r le_rfl).const_mul _),hiB] at hFB
  have hmiss : ∀ᵐ z ∂volume.restrict D,
      Ic (q*r) z ≤ H z+B z ∧ W (q*r) z ≤ r^(-p)*V z+(q*r)^(-p)*B z := by
    filter_upwards [ae_restrict_mem hD] with z hz
    exact source_collar_missed a hκ hκ8 D q r L hq hq1 hr hL hy ω z hz
  exact source_mesh_integrated_step (volume.restrict D) (fun z => W r z) (fun z => W (q*r) z)
    (fun z => Ic r z) (fun z => Ic (q*r) z) (fun z => H z) (fun z => V z) (fun z => B z)
    p q r C (Cbad*L^(-c)) b hq hq1 hr hp (hWi r hr le_rfl) (hWi (q*r) (mul_pos hq hr) hqr)
    (hIi r le_rfl) (hIi (q*r) hqr) hHi hVi hBi hb (hmiss.mono fun _ h => h.1) (hmiss.mono fun _ h => h.2)
    (sub_le_iff_le_add'.mp hFH) (sub_le_iff_le_add'.mp hFV) (sub_le_iff_le_add'.mp hFB)

end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable

lemma source_mesh_step
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (D : Set ℂ) (hD : MeasurableSet D) (c₀ : ℂ) (hDc : D ⊆ ball c₀ 1)
    (q r L C Cbad c b : ℝ) (hq : 0 < q) (hq1 : q < 1) (hr : 0 < r)
    (hL : 1 < L) (hR : 3*(L*r) ≤ 1) (hC : 0 ≤ C) (hCb : 0 ≤ Cbad) (hb : 0 < b)
    (hy : ∀ z ∈ D, r ≤ z.im)
    (hmean : ∀ z (hz : z ∈ D),
      let μ := P.comap (Subtype.val : a.samples → Ω)
      let W := fun v (ω : a.samples) => spatialGreenWeight κ
        (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z v
      let H := fun ω : a.samples => sourceSpatialWindowH (γ ω) z r (q*r) (L*r)
      let B := fun ω : a.samples => sourceSpatialWindowB (γ ω) z r (q*r) (L*r)
      let hs := source_liveHit_stopping a z r (hy z hz)
      μ[H | hs.measurableSpace] ≤ᵐ[μ] (fun ω => C*(q*r)^codimension κ*W r ω) ∧
      μ[(fun ω => r^codimension κ*W (q*r) ω*H ω) | hs.measurableSpace] ≤ᵐ[μ]
        (fun ω => r^codimension κ*W r ω) ∧
      μ[B | hs.measurableSpace] ≤ᵐ[μ]
        (fun ω => Cbad*L^(-c)*(if liveSpatialHitTime (γ ω) z r = ⊤ then 0 else 1)))
    (E : Set a.samples) (hE : MeasurableSet E)
    (hEs : ∀ z, MeasurableSet[(source_collarStart_stopping a D r hy z).measurableSpace] E) :
    ∃ F : Set a.samples, MeasurableSet F ∧
      ((P.comap Subtype.val).restrict E) F ≤ ENNReal.ofReal
        (3*(P.comap Subtype.val).real E*Real.exp (-(1/512:ℝ)*b^2/((q^(-codimension κ))^2*(L*r)^2))) ∧
      ∀ ω ∉ F,
      spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (q*r) D ≤
        spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) r D+
        (Cbad*L^(-c)*q^(-codimension κ))*sourceMeshCount (codimension κ) D (γ ω) r+
        (2*q^(-codimension κ))*r^(-codimension κ)*b ∧
      sourceMeshCount (codimension κ) D (γ ω) (q*r) ≤
        C*spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) r D+
        (Cbad*L^(-c)*q^(-codimension κ))*sourceMeshCount (codimension κ) D (γ ω) r+
        (2*q^(-codimension κ))*r^(-codimension κ)*b := by
  let p := codimension κ
  let μ := P.comap (Subtype.val : a.samples → Ω)
  let W (v : ℝ) (z : ℂ) (ω : a.samples) := spatialGreenWeight κ
    (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z v
  let Ic (v : ℝ) (z : ℂ) (ω : a.samples) : ℝ := if sourceCollarStart D (γ ω) z v = ⊤ then 0 else 1
  let H (z : ℂ) (ω : a.samples) := sourceCollarH D (γ ω) z r (q*r) (L*r)
  let B (z : ℂ) (ω : a.samples) := sourceCollarB D (γ ω) z r (q*r) (L*r)
  let V (z : ℂ) (ω : a.samples) := r^p*W (q*r) z ω*H z ω
  let μH (z : ℂ) (ω : a.samples) := C*(q*r)^p*(if z ∈ D then W r z ω else 0)
  let μV (z : ℂ) (ω : a.samples) := r^p*(if z ∈ D then W r z ω else 0)
  let μB (z : ℂ) (ω : a.samples) := Cbad*L^(-c)*Ic r z ω
  let FH := {ω | b < ∫ z in D, (H z ω-μH z ω)}
  let FV := {ω | b < ∫ z in D, (V z ω-μV z ω)}
  let FB := {ω | b < ∫ z in D, (B z ω-μB z ω)}
  let σ := fun z (ω : a.samples) => sourceCollarStart D (γ ω) z r
  let τ := fun z (ω : a.samples) => sourceCollarFinish D (γ ω) z r (q*r) (L*r)
  have hWinH := source_mesh_H_window a hκ hκ8 D hD c₀ hDc q r L C hq hq1 hr hL hR hC hy (fun z hz => (hmean z hz).1)
  have hWinV := source_mesh_V_window a hκ hκ8 D hD c₀ hDc q r L hq hq1 hr hL hR hy (fun z hz => (hmean z hz).2.1)
  have hWinB := source_mesh_B_window a D hD c₀ hDc q r L Cbad c hq hq1 hr hL hR hCb hy (fun z hz => (hmean z hz).2.2)
  have hmH : MeasurableSet FH := measurableSet_lt measurable_const (source_mesh_shifted_integral_measurable (σ := σ) (τ := τ) (Y := H) (μ := μH) c₀ hWinH)
  have hmV : MeasurableSet FV := measurableSet_lt measurable_const (source_mesh_shifted_integral_measurable (σ := σ) (τ := τ) (Y := V) (μ := μV) c₀ hWinV)
  have hmB : MeasurableSet FB := measurableSet_lt measurable_const (source_mesh_shifted_integral_measurable (σ := σ) (τ := τ) (Y := B) (μ := μB) c₀ hWinB)
  have hp : 0 < p := by dsimp [p,codimension,dimension]; linarith
  have hK1 : 1 ≤ q^(-p) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hq hq1.le (neg_nonpos.mpr hp.le)
  have hK : 0 < q^(-p) := Real.rpow_pos_of_pos hq _
  have hTailH := source_mesh_shifted_restricted_tail (σ := σ) (τ := τ) (Y := H) (μ := μH) c₀ hWinH
    (source_collarStart_stopping a D r hy) zero_lt_one hb E hE hEs
  have hTailV := source_mesh_shifted_restricted_tail (σ := σ) (τ := τ) (Y := V) (μ := μV) c₀ hWinV
    (source_collarStart_stopping a D r hy) hK hb E hE hEs
  have hTailB := source_mesh_shifted_restricted_tail (σ := σ) (τ := τ) (Y := B) (μ := μB) c₀ hWinB
    (source_collarStart_stopping a D r hy) zero_lt_one hb E hE hEs
  have hexp : Real.exp (-(1/512:ℝ)*b^2/(1^2*(L*r)^2)) ≤
      Real.exp (-(1/512:ℝ)*b^2/((q^(-p))^2*(L*r)^2)) := by
    apply Real.exp_le_exp.mpr
    have hr0 : 0 < L*r := mul_pos (by linarith) hr
    have hden : (L*r)^2 ≤ (q^(-p))^2*(L*r)^2 := by nlinarith [sq_nonneg (q^(-p)-1),sq_nonneg (L*r)]
    have hh := div_le_div_of_nonneg_left (show 0 ≤ (1/512:ℝ)*b^2 by positivity) (sq_pos_of_pos hr0) hden
    simpa only [one_pow,one_mul,neg_mul,neg_div] using neg_le_neg hh
  have hTail (F : Set a.samples) (hh : (μ.restrict E) F ≤ ENNReal.ofReal
      (μ.real E*Real.exp (-(1/512:ℝ)*b^2/(1^2*(L*r)^2)))) :
      (μ.restrict E) F ≤ ENNReal.ofReal (μ.real E*Real.exp (-(1/512:ℝ)*b^2/((q^(-p))^2*(L*r)^2))) :=
    hh.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hexp (measureReal_nonneg)))
  refine ⟨FH∪FV∪FB,(hmH.union hmV).union hmB,?_,?_⟩
  · calc
      _ ≤ (μ.restrict E) FH+(μ.restrict E) FV+(μ.restrict E) FB :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ ≤ ENNReal.ofReal (μ.real E*Real.exp (-(1/512:ℝ)*b^2/((q^(-p))^2*(L*r)^2)))+
           ENNReal.ofReal (μ.real E*Real.exp (-(1/512:ℝ)*b^2/((q^(-p))^2*(L*r)^2)))+
           ENNReal.ofReal (μ.real E*Real.exp (-(1/512:ℝ)*b^2/((q^(-p))^2*(L*r)^2))) :=
        add_le_add (add_le_add (hTail FH hTailH) hTailV) (hTail FB hTailB)
      _ = _ := by rw [←ENNReal.ofReal_add (by positivity) (by positivity),←ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  · intro ω hω
    have hFH : (∫ z in D, (H z ω-μH z ω)) ≤ b := le_of_not_gt (fun hh => hω (Or.inl (Or.inl hh)))
    have hFV : (∫ z in D, (V z ω-μV z ω)) ≤ b := le_of_not_gt (fun hh => hω (Or.inl (Or.inr hh)))
    have hFB : (∫ z in D, (B z ω-μB z ω)) ≤ b := le_of_not_gt (fun hh => hω (Or.inr hh))
    exact source_mesh_integral_recurrences a hκ hκ8 D hD c₀ hDc q r L C Cbad c b
      hq hq1 hr hL hb.le hy ω hFH hFV hFB

end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section

lemma source_mesh_power_growth {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q) (hq1 : q < 1) :
    ∃ u β : ℝ, 1 < u ∧ u*q < 1 ∧ 1 < q^p/(u*q) ∧ β = (q^p/(u*q))^2 ∧ 1 < β ∧
      ∀ c : ℝ, 0 < c → 0 < u^(-c) ∧ u^(-c) < 1 := by
  have hqp : q < q^p := by
    have hh := Real.rpow_lt_rpow_of_exponent_gt hq hq1 hp1
    simpa only [Real.rpow_one] using hh
  have hqp1 : q^p < 1 := Real.rpow_lt_one hq.le hq1 hp
  let u := (1+q^p/q)/2
  have hu : 1 < u := by dsimp [u]; have : 1 < q^p/q := (lt_div_iff₀ hq).mpr (by simpa using hqp); linarith
  have huq : u*q < q^p := by dsimp [u]; field_simp; nlinarith
  have hratio : 1 < q^p/(u*q) := (lt_div_iff₀ (mul_pos (by linarith) hq)).mpr (by simpa using huq)
  refine ⟨u,(q^p/(u*q))^2,hu,huq.trans hqp1,hratio,rfl,by nlinarith,?_⟩
  intro c hc
  refine ⟨Real.rpow_pos_of_pos (by linarith) _,?_⟩
  exact Real.rpow_lt_one_of_one_lt_of_neg hu (neg_neg_of_pos hc)

lemma source_mesh_scale_cancel {p r δ : ℝ} (hr : 0 < r) (_hδ : 0 < δ) (n : ℕ) :
    r^(-p)*(δ^(-p)*r^p/(n+1:ℝ)^2) = δ^(-p)/(n+1:ℝ)^2 := by
  have he : r^(-p)*r^p = 1 := by rw [←Real.rpow_add hr,neg_add_cancel,Real.rpow_zero]
  calc
    _ = δ^(-p)*(r^(-p)*r^p)/(n+1:ℝ)^2 := by ring
    _ = _ := by rw [he,mul_one]

lemma source_mesh_radius_bound {q u L r δ : ℝ} (hq : 0 < q) (hu : 0 < u)
    (huq : u*q ≤ 1) (hL : 0 < L) (hr : 0 < r) (hrδ : r ≤ δ) (n : ℕ) :
    (L*u^n)*(r*q^n) ≤ L*δ := by
  have hh : (u*q)^n ≤ 1 := pow_le_one₀ (mul_nonneg hu.le hq.le) huq
  calc
    _ = (L*r)*(u*q)^n := by rw [mul_pow]; ring
    _ ≤ (L*r)*1 := mul_le_mul_of_nonneg_left hh (mul_nonneg hL.le hr.le)
    _ ≤ L*δ := by rw [mul_one]; exact mul_le_mul_of_nonneg_left hrδ hL.le

lemma source_mesh_alpha {c u L : ℝ} (hL : 0 < L) (hu : 0 < u) (n : ℕ) :
    (L*u^n)^(-c) = L^(-c)*(u^(-c))^n := by
  rw [Real.mul_rpow hL.le (pow_nonneg hu.le _),Real.rpow_pow_comm hu.le]

lemma source_mesh_failure_exponent {p q u L r δ K : ℝ}
    (hp1 : p < 1) (hq : 0 < q) (hu : 0 < u) (hL : 0 < L)
    (hr : 0 < r) (hrδ : r ≤ δ) (_hK : 0 < K) (n : ℕ) :
    δ^(-2:ℝ)/(K^2*L^2)*((q^p/(u*q))^2)^n/(n+1:ℝ)^4 ≤
    (δ^(-p)*(r*q^n)^p/(n+1:ℝ)^2)^2/(K^2*((L*u^n)*(r*q^n))^2) := by
  have hδ : 0 < δ := hr.trans_le hrδ
  have hn : 0 < (n+1:ℝ) := by positivity
  have hR : 0 < (L*u^n)*(r*q^n) := by positivity
  have hrq : 0 < r*q^n := by positivity
  have hid : (δ^(-p)*(r*q^n)^p/(n+1:ℝ)^2)/((L*u^n)*(r*q^n)) =
      (δ^(-p)*r^(p-1))/L*(q^p/(u*q))^n/(n+1:ℝ)^2 := by
    rw [Real.mul_rpow hr.le (pow_nonneg hq.le _),←Real.rpow_pow_comm hq.le,
      Real.rpow_sub hr,Real.rpow_one,div_pow,mul_pow]
    field_simp
  have hant := Real.rpow_le_rpow_of_nonpos hr hrδ (by linarith : p-1 ≤ 0)
  have hc : δ⁻¹ ≤ δ^(-p)*r^(p-1) := by
    calc
      δ⁻¹ = δ^(-p)*δ^(p-1) := by rw [←Real.rpow_add hδ]; ring_nf; rw [Real.rpow_neg_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left hant (Real.rpow_nonneg hδ.le _)
  have ratio : δ⁻¹/L*(q^p/(u*q))^n/(n+1:ℝ)^2 ≤
      (δ^(-p)*(r*q^n)^p/(n+1:ℝ)^2)/((L*u^n)*(r*q^n)) := by
    rw [hid]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hc hL.le) (by positivity)) (by positivity)
  have hleft : 0 ≤ δ⁻¹/L*(q^p/(u*q))^n/(n+1:ℝ)^2 := by positivity
  have hsq : (δ⁻¹/L*(q^p/(u*q))^n/(n+1:ℝ)^2)^2 ≤
      ((δ^(-p)*(r*q^n)^p/(n+1:ℝ)^2)/((L*u^n)*(r*q^n)))^2 := by nlinarith
  calc
    _ = (δ⁻¹/L*(q^p/(u*q))^n/(n+1:ℝ)^2)^2/K^2 := by
      rw [Real.rpow_neg hδ.le,Real.rpow_two]
      simp only [div_pow,mul_pow,inv_pow,←pow_mul]
      ring
    _ ≤ ((δ^(-p)*(r*q^n)^p/(n+1:ℝ)^2)/((L*u^n)*(r*q^n)))^2/K^2 :=
      div_le_div_of_nonneg_right hsq (sq_nonneg K)
    _ = _ := by rw [div_pow]; ring

end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section

lemma source_mesh_choose_large {c A : ℝ} (hc : 0 < c) :
    ∃ L : ℝ, 1 < L ∧ A*L^(-c) ≤ 1/2 := by
  have ht : Tendsto (fun L : ℝ => A*L^(-c)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop hc).const_mul A
  have hh := ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2))
  obtain ⟨N,hN⟩ := eventually_atTop.mp hh
  refine ⟨max N 2,lt_of_lt_of_le (by norm_num) (le_max_right _ _),(hN _ (le_max_left _ _)).le⟩

lemma source_mesh_select_start {q rf δ : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hf : 0 < rf) (hfδ : rf ≤ δ) :
    ∃ r : ℝ, ∃ n : ℕ, 0 < r ∧ q*δ ≤ r ∧ r ≤ δ ∧ rf = r*q^n := by
  have hδ : 0 < δ := hf.trans_le hfδ
  obtain ⟨n,hn1,hn2⟩ := exists_nat_pow_near_of_lt_one (div_pos hf hδ)
    ((div_le_one₀ hδ).mpr hfδ) hq hq1
  have hqn : 0 < q^n := pow_pos hq _
  refine ⟨rf/q^n,n,div_pos hf hqn,?_,?_,?_⟩
  · apply (le_div_iff₀ hqn).mpr
    have hh := (lt_div_iff₀ hδ).mp hn1
    rw [pow_succ] at hh
    nlinarith
  · apply (div_le_iff₀ hqn).mpr
    have hh := (div_le_iff₀ hδ).mp hn2
    nlinarith
  · symm; exact div_mul_cancel₀ _ hqn.ne'

lemma source_mesh_height {z c : ℂ} {η r : ℝ} (hc : 1+η ≤ c.im)
    (hz : z ∈ ball c 1) (hr : r < η) : r < z.im := by
  have hdist : abs (z.im-c.im) ≤ dist z c := by
    simpa only [dist_eq_norm,Complex.sub_im] using Complex.abs_im_le_norm (z-c)
  have hz' : dist z c < 1 := hz
  have hh := neg_abs_le (z.im-c.im)
  linarith

lemma source_mesh_count_bound
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (D : Set ℂ) (hD : MeasurableSet D) (hfin : volume D ≠ ∞)
    (p r : ℝ) (hr : 0 < r) (hy : ∀ z ∈ D, r ≤ z.im) (ω : a.samples) :
    0 ≤ r^(-p)*(∫ z in D, if sourceCollarStart D (γ ω) z r = ⊤ then (0:ℝ) else 1) ∧
    r^(-p)*(∫ z in D, if sourceCollarStart D (γ ω) z r = ⊤ then (0:ℝ) else 1) ≤
      (volume D).toReal*r^(-p) := by
  let : IsFiniteMeasure (volume.restrict D) := ⟨by simpa only [Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr hfin⟩
  have hi : IntegrableOn (fun z => if sourceCollarStart D (γ ω) z r = ⊤ then (0:ℝ) else 1) D := by
    apply source_mesh_bounded_integrable (K := 1)
    · have hm : Measurable (fun p : ℂ × a.samples => if sourceCollarStart D (γ p.2) p.1 r = ⊤ then (0:ℝ) else 1) :=
        Measurable.ite (measurableSet_eq_fun (source_collarStart_joint a D hD r hy) measurable_const) measurable_const measurable_const
      exact hm.comp (measurable_id.prodMk measurable_const)
    · intro z; split_ifs <;> norm_num
  have hb : (∫ z in D, if sourceCollarStart D (γ ω) z r = ⊤ then (0:ℝ) else 1) ≤ (volume D).toReal := by
    calc
      _ ≤ ∫ _z in D, (1:ℝ) := integral_mono hi (integrable_const _) (fun z => by split_ifs <;> norm_num)
      _ = _ := by simp only [integral_const,Measure.restrict_apply_univ,smul_eq_mul,mul_one,measureReal_def]
  refine ⟨mul_nonneg (Real.rpow_nonneg hr.le _) (integral_nonneg (fun z => by split_ifs <;> norm_num)),?_⟩
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hr.le (-p))

end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
lemma source_mesh_grid_exponent {p q u L r δ K : ℝ}
    (hp1 : p < 1) (hq : 0 < q) (hu : 0 < u) (hL : 0 < L)
    (hr : 0 < r) (hrδ : r ≤ δ) (hK : 0 < K) (n : ℕ) :
    -(1/512:ℝ)*(δ^(-p)*(r*q^n)^p/(n+1:ℝ)^2)^2/(K^2*((L*u^n)*(r*q^n))^2) ≤
      -(1/(512*K^2*L^2))*δ^(-2:ℝ)*(((q^p/(u*q))^2)^n/(n+1:ℝ)^4) := by
  have hh := source_mesh_failure_exponent hp1 hq hu hL hr hrδ hK n
  calc
    _ = -(1/512:ℝ)*((δ^(-p)*(r*q^n)^p/(n+1:ℝ)^2)^2/(K^2*((L*u^n)*(r*q^n))^2)) := by ring
    _ ≤ -(1/512:ℝ)*(δ^(-2:ℝ)/(K^2*L^2)*((q^p/(u*q))^2)^n/(n+1:ℝ)^4) :=
      mul_le_mul_of_nonpos_left hh (by norm_num)
    _ = _ := by ring

lemma source_mesh_grid_error {p q r δ E : ℝ} (hq : 0 < q) (hr : 0 < r) (hδ : 0 < δ) (n : ℕ) :
    E*(r*q^n)^(-p)*(δ^(-p)*(r*q^n)^p/(n+1:ℝ)^2) = E*δ^(-p)/(n+1:ℝ)^2 := by
  rw [mul_assoc,source_mesh_scale_cancel (mul_pos hr (pow_pos hq _)) hδ]
  ring

lemma source_mesh_grid_coefficient {c u L Cbad q p : ℝ} (hL : 0 < L) (hu : 0 < u) (n : ℕ) :
    Cbad*(L*u^n)^(-c)*q^(-p) = (Cbad*L^(-c)*q^(-p))*(u^(-c))^n := by
  rw [source_mesh_alpha hL hu]; ring

lemma source_mesh_grid_radius_le {q r δ : ℝ} (hq : 0 < q) (hq1 : q < 1) (hr : 0 < r)
    (hrδ : r ≤ δ) (n : ℕ) : r*q^n ≤ δ :=
  (mul_le_mul_of_nonneg_left (pow_le_one₀ hq.le hq1.le) hr.le).trans (by simpa using hrδ)

lemma source_mesh_initial_scale {p q r δ : ℝ} (hp : 0 < p) (hq : 0 < q) (hδ : 0 < δ)
    (hr : q*δ ≤ r) : r^(-p) ≤ q^(-p)*δ^(-p) := by
  rw [←Real.mul_rpow hq.le hδ.le]
  exact Real.rpow_le_rpow_of_nonpos (mul_pos hq hδ) hr (neg_nonpos.mpr hp.le)

lemma source_mesh_ball_volume (c : ℂ) : volume (ball c 1) = volume (ball (0:ℂ) 1) := by
  rw [Complex.volume_ball,Complex.volume_ball]
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
structure SourceMeshParameters (κ : ℝ) where
  C : ℝ
  Cbad : ℝ
  c : ℝ
  q : ℝ
  u : ℝ
  L : ℝ
  hC : 0 < C
  hCb : 0 < Cbad
  hc : 0 < c
  hq : 0 < q
  hq1 : q < 1
  hu : 1 < u
  huq : u*q < 1
  hratio : 1 < q^codimension κ/(u*q)
  hL : 1 < L
  halpha : Cbad*L^(-c)*q^(-codimension κ) ≤ 1/2
  means :
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
    ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ)
      (z : ℂ) (ε r L : ℝ), 0 < ε → ε ≤ q*r → r < z.im → 1 < L →
    ∃ hσ : IsStoppingTime a.filtration (fun ω : a.samples => liveSpatialHitTime (γ ω) z r),
      let μ := P.comap (Subtype.val : a.samples → Ω)
      let W := fun v (ω : a.samples) => spatialGreenWeight κ
        (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z v
      let H := fun ω : a.samples => sourceSpatialWindowH (γ ω) z r ε (L*r)
      let B := fun ω : a.samples => sourceSpatialWindowB (γ ω) z r ε (L*r)
      μ[H | hσ.measurableSpace] ≤ᵐ[μ] (fun ω => C*ε^codimension κ*W r ω) ∧
      μ[(fun ω => r^codimension κ*W ε ω*H ω) | hσ.measurableSpace] ≤ᵐ[μ]
        (fun ω => r^codimension κ*W r ω) ∧
      μ[B | hσ.measurableSpace] ≤ᵐ[μ]
        (fun ω => Cbad*L^(-c)*(if liveSpatialHitTime (γ ω) z r = ⊤ then 0 else 1))

lemma source_mesh_parameters (κ : ℝ) (hκ : 4 < κ) (hκ8 : κ < 8) :
    Nonempty (SourceMeshParameters κ) := by
  obtain ⟨C,Cbad,c,q,hC,hCb,hc,hq,hq1,hmean⟩ := sourceSpatialWindowMeans_proved κ hκ hκ8
  have hp : 0 < codimension κ := by dsimp [codimension,dimension]; linarith
  have hp1 : codimension κ < 1 := by dsimp [codimension,dimension]; linarith
  obtain ⟨u,β,hu,huq,hratio,hβdef,hβ,htheta⟩ := source_mesh_power_growth hp hp1 hq hq1
  obtain ⟨L,hL,hlarge⟩ := source_mesh_choose_large (A := Cbad*q^(-codimension κ)) hc
  refine ⟨⟨C,Cbad,c,q,u,L,hC,hCb,hc,hq,hq1,hu,huq,hratio,hL,?_,hmean⟩⟩
  calc
    Cbad*L^(-c)*q^(-codimension κ) = (Cbad*q^(-codimension κ))*L^(-c) := by ring
    _ ≤ 1/2 := hlarge

lemma source_mesh_choose_delta (η L : ℝ) (hη : 0 < η) (hL : 0 < L) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < η/2 ∧ δ₀ ≤ 1 ∧ 3*L*δ₀ ≤ 1 := by
  let δ₀ := min (min (η/4) (1/2)) (1/(6*L))
  have hpos : 0 < δ₀ := by dsimp [δ₀]; positivity
  refine ⟨δ₀,hpos,?_,?_,?_⟩
  · have := (min_le_left (min (η/4) (1/2)) (1/(6*L))).trans (min_le_left _ _)
    change δ₀ ≤ η/4 at this
    linarith
  · exact ((min_le_left _ _).trans (min_le_right _ _)).trans (by norm_num)
  · have hh : δ₀ ≤ 1/(6*L) := min_le_right _ _
    have hh' := (le_div_iff₀ (by positivity : 0 < 6*L)).mp hh
    nlinarith
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable

lemma source_mesh_grid_step
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 4 < κ) (hκ8 : κ < 8) (m : SourceMeshParameters κ)
    (D : Set ℂ) (hD : MeasurableSet D) (c₀ : ℂ) (hDc : D ⊆ ball c₀ 1)
    (r δ : ℝ) (hr : 0 < r) (hrδ : r ≤ δ) (hR : 3*m.L*δ ≤ 1)
    (hy : ∀ z ∈ D, δ < z.im) (n : ℕ)
    (E : Set a.samples) (hE : MeasurableSet E)
    (hEs : ∀ z, MeasurableSet[(source_collarStart_stopping a D (r*m.q^n)
      (fun z hz => (source_mesh_grid_radius_le m.hq m.hq1 hr hrδ n).trans (hy z hz).le) z).measurableSpace] E) :
    ∃ F : Set a.samples, MeasurableSet F ∧
      ((P.comap Subtype.val).restrict E) F ≤ ENNReal.ofReal
        (3*(P.comap Subtype.val).real E*Real.exp (-(1/(512*(m.q^(-codimension κ))^2*m.L^2))*
          δ^(-2:ℝ)*(((m.q^codimension κ/(m.u*m.q))^2)^n/(n+1:ℝ)^4))) ∧
      ∀ ω ∉ F,
      spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (r*m.q^(n+1)) D ≤
        spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (r*m.q^n) D+
        ((m.Cbad*m.L^(-m.c)*m.q^(-codimension κ))*(m.u^(-m.c))^n)*sourceMeshCount (codimension κ) D (γ ω) (r*m.q^n)+
        (2*m.q^(-codimension κ))*δ^(-codimension κ)/(n+1:ℝ)^2 ∧
      sourceMeshCount (codimension κ) D (γ ω) (r*m.q^(n+1)) ≤
        m.C*spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (r*m.q^n) D+
        ((m.Cbad*m.L^(-m.c)*m.q^(-codimension κ))*(m.u^(-m.c))^n)*sourceMeshCount (codimension κ) D (γ ω) (r*m.q^n)+
        (2*m.q^(-codimension κ))*δ^(-codimension κ)/(n+1:ℝ)^2 := by
  have hp1 : codimension κ < 1 := by dsimp [codimension,dimension]; linarith
  have hk : 0 < κ := by linarith
  have hδ : 0 < δ := hr.trans_le hrδ
  have hL : 0 < m.L := lt_trans zero_lt_one m.hL
  have hu : 0 < m.u := lt_trans zero_lt_one m.hu
  have hrn : 0 < r*m.q^n := mul_pos hr (pow_pos m.hq _)
  have hy' (z : ℂ) (hz : z ∈ D) : r*m.q^n < z.im :=
    (source_mesh_grid_radius_le m.hq m.hq1 hr hrδ n).trans_lt (hy z hz)
  have hLn : 1 < m.L*m.u^n := m.hL.trans_le
    (by simpa using mul_le_mul_of_nonneg_left (one_le_pow₀ m.hu.le) hL.le)
  have hRn : 3*((m.L*m.u^n)*(r*m.q^n)) ≤ 1 :=
    (mul_le_mul_of_nonneg_left (source_mesh_radius_bound m.hq hu m.huq.le hL hr hrδ n) (by norm_num)).trans (by simpa only [mul_assoc] using hR)
  obtain ⟨F,hFm,hFt,hFg⟩ := source_mesh_step a hk hκ8 D hD c₀ hDc m.q (r*m.q^n) (m.L*m.u^n)
    m.C m.Cbad m.c (δ^(-codimension κ)*(r*m.q^n)^codimension κ/(n+1:ℝ)^2)
    m.hq m.hq1 hrn hLn hRn m.hC.le m.hCb.le (by positivity) (fun z hz => (hy' z hz).le)
    (fun z hz => by
      obtain ⟨hs,hH,hV,hB⟩ := m.means Ω ‹MeasurableSpace Ω› P inferInstance γ a z
        (m.q*(r*m.q^n)) (r*m.q^n) (m.L*m.u^n) (mul_pos m.hq hrn) le_rfl (hy' z hz) hLn
      exact ⟨hH,hV,hB⟩) E hE hEs
  refine ⟨F,hFm,hFt.trans ?_,?_⟩
  · apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    exact source_mesh_grid_exponent hp1 m.hq hu hL hr hrδ (Real.rpow_pos_of_pos m.hq _) n
  · intro ω hω
    have hh := hFg ω hω
    have hrnext : m.q*(r*m.q^n) = r*m.q^(n+1) := by rw [pow_succ]; ring
    rwa [hrnext,source_mesh_grid_coefficient hL hu,
      source_mesh_grid_error m.hq hr hδ] at hh
end
end SLEExactGauge
end

end OAI
