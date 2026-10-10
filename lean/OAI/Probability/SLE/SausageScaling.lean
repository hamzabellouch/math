import Mathlib
import OAI.Probability.SLE.TracePosCombined

namespace OAI

/-! Sausage Scaling for chordal SLE. -/

section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance SausageScaling_local1 : MeasurableSpace C(ℝ≥0,ℂ) := borel _
local instance SausageScaling_local2 : BorelSpace C(ℝ≥0,ℂ) := ⟨rfl⟩
lemma source_sausage_dilation {c : ℝ≥0} (hc : 0 < c) (η : ℝ≥0 → ℂ)
    (T δ : ℝ≥0) (ht : sourceScaleTime c δ = T) (K : Set ℂ) (e : ℝ) :
    ((fun z : ℂ => (c:ℂ)*z) '' (K ∩ sourceSausageSet η 0 T (e/(c:ℝ)))) ⊆
      ((fun z : ℂ => (c:ℂ)*z) '' K) ∩ sourceSausageSet (sourceScaleTrace c η) 0 δ e := by
  rintro _ ⟨z,hz,rfl⟩
  refine ⟨⟨z,hz.1,rfl⟩,?_⟩
  obtain ⟨u,hu,hzu⟩ := hz.2
  have hc2 : c^2 ≠ 0 := pow_ne_zero _ hc.ne'
  have htu : c^2*u ≤ δ := by
    have hh := hu.2
    rw [←ht,sourceScaleTime,le_div_iff₀ (pow_pos hc _)] at hh
    simpa only [mul_comm] using hh
  refine ⟨c^2*u,⟨bot_le,htu⟩,?_⟩
  have he : sourceScaleTime c (c^2*u) = u := by
    unfold sourceScaleTime; field_simp
  simp only [sourceScaleTrace,he,dist_eq_norm,←mul_sub,norm_mul,norm_real,Real.norm_eq_abs,abs_of_nonneg c.coe_nonneg] 
  have hh : ‖z-η u‖ < e/(c:ℝ) := by simpa only [dist_eq_norm] using hzu
  have hcR : 0 < (c:ℝ) := hc
  nlinarith [(lt_div_iff₀ hcR).mp hh]
lemma source_volume_dilation_lower {c : ℝ≥0} (hc : 0 < c) (S : Set ℂ) :
    volume S ≤ ((c⁻¹:ℝ≥0):ℝ≥0∞)^2 * volume ((fun z : ℂ => (c:ℂ)*z) '' S) := by
  have hLip : LipschitzWith c⁻¹ (fun z : ℂ => (c⁻¹:ℂ)*z) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp [dist_eq_norm,←mul_sub]
  have hh := source_volume_lipschitz_image (hLip.lipschitzOnWith (s := (fun z : ℂ => (c:ℂ)*z) '' S))
  have hi : (fun z : ℂ => (c⁻¹:ℂ)*z) '' ((fun z : ℂ => (c:ℂ)*z) '' S) = S := by
    rw [←image_comp]
    have he : (fun z : ℂ => (c⁻¹:ℂ)*((c:ℂ)*z)) = id := by
      funext z
      simp only [←mul_assoc,inv_mul_cancel₀ (by exact_mod_cast hc.ne' : (c:ℂ) ≠ 0),one_mul,id_eq]
    simp only [Function.comp_def,he,image_id]
  rwa [hi] at hh
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance SausageUniformSeed_local1 : MeasurableSpace C(ℝ≥0,ℂ) := borel _
local instance SausageUniformSeed_local2 : BorelSpace C(ℝ≥0,ℂ) := ⟨rfl⟩
lemma source_sausage_scale_mass_bound (κ : ℝ) {c : ℝ≥0} (hc : 0 < c)
    (η : ℝ≥0 → ℂ) (T δ : ℝ≥0) (ht : sourceScaleTime c δ = T)
    (K : Set ℂ) (e : ℝ) (he : 0 < e) :
    ENNReal.ofReal ((e/(c:ℝ))^(-codimension κ))*volume (K ∩ sourceSausageSet η 0 T (e/(c:ℝ))) ≤
      ENNReal.ofReal (((c:ℝ)⁻¹)^(-codimension κ)*((c:ℝ)⁻¹)^2)*
        (ENNReal.ofReal (e^(-codimension κ))*volume (((fun z : ℂ => (c:ℂ)*z) '' K) ∩
          sourceSausageSet (sourceScaleTrace c η) 0 δ e)) := by
  have hvol := (source_volume_dilation_lower hc (K ∩ sourceSausageSet η 0 T (e/(c:ℝ)))).trans (mul_le_mul' le_rfl (measure_mono (source_sausage_dilation hc η T δ ht K e)))
  have hmul : (e/(c:ℝ))^(-codimension κ) = ((c:ℝ)⁻¹)^(-codimension κ)*e^(-codimension κ) := by
    rw [show e/(c:ℝ) = (c:ℝ)⁻¹*e by ring,Real.mul_rpow (by positivity) he.le]
  have hh := mul_le_mul' (le_refl (ENNReal.ofReal ((e/(c:ℝ))^(-codimension κ)))) hvol
  apply hh.trans_eq
  rw [hmul]
  have hcI : 0 ≤ (c:ℝ)⁻¹ := inv_nonneg.mpr c.coe_nonneg
  have hcP : 0 ≤ ((c:ℝ)⁻¹)^(-codimension κ) := Real.rpow_nonneg hcI _
  rw [ENNReal.ofReal_mul hcP,ENNReal.ofReal_mul hcP,ENNReal.ofReal_pow hcI]
  simp only [ENNReal.ofReal_inv_of_pos (show 0 < (c:ℝ) from hc),ENNReal.ofReal_coe_nnreal,ENNReal.coe_inv hc.ne']
  ac_rfl
lemma RegularSLEPresentation.source_uniform_sausage_seed
    {Ω : Type} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 4 < κ) (hκ8 : κ < 8) :
    ∃ p : ℝ≥0∞, 0 < p ∧ p ≤ 1 ∧ ∀ δ : ℝ≥0, 0 < δ →
      ∃ (K : Set ℂ) (b e₀ : ℝ), IsCompact K ∧ K ⊆ upperHalfPlane ∧ 0 < b ∧ 0 < e₀ ∧
        ∀ e : ℝ, 0 < e → e < e₀ →
          p ≤ (P.comap (Subtype.val : a.samples → Ω))
            {ω | ENNReal.ofReal b ≤ ENNReal.ofReal (e^(-codimension κ))*
              volume (K ∩ sourceSausageSet (γ ω) 0 δ e)} := by
  have hk : 0 < κ := by linarith
  let z₀ : ℂ := 3*I
  have hz₀ : 2 < z₀.im := by norm_num [z₀]
  obtain ⟨T,p,b,e₀,hT,hp,hb,he₀,hseed⟩ := a.source_positive_probability_initial_sausage hκ hκ8 z₀ hz₀
  let Q := P.comap (Subtype.val : a.samples → Ω)
  have hp1 : ENNReal.ofReal p ≤ 1 := (hseed (e₀/2) (by positivity) (by linarith)).trans prob_le_one
  refine ⟨ENNReal.ofReal p,ENNReal.ofReal_pos.mpr hp,hp1,?_⟩
  intro δ hδ
  let c := NNReal.sqrt (δ/T)
  have hc : 0 < c := by dsimp [c]; exact NNReal.sqrt_pos.mpr (div_pos hδ hT)
  have hc2 : c^2 = δ/T := NNReal.sq_sqrt _
  have hcR : 0 < (c:ℝ) := hc
  have ht : sourceScaleTime c δ = T := by
    unfold sourceScaleTime
    rw [hc2]
    field_simp
  let K := (fun z : ℂ => (c:ℂ)*z) '' closedBall z₀ 1
  have hK : IsCompact K := (isCompact_closedBall z₀ 1).image (continuous_const.mul continuous_id)
  have hKH : K ⊆ upperHalfPlane := by
    rintro _ ⟨z,hz,rfl⟩
    have hz' : 0 < z.im := zero_lt_one.trans (source_unit_ball_height hz₀ hz)
    change 0 < ((c:ℂ)*z).im
    simpa only [mul_im,ofReal_re,ofReal_im,zero_mul,add_zero] using mul_pos hcR hz'
  let C := ((c:ℝ)⁻¹)^(-codimension κ)*((c:ℝ)⁻¹)^2
  have hC : 0 < C := mul_pos (Real.rpow_pos_of_pos (inv_pos.mpr hcR) _) (sq_pos_of_pos (inv_pos.mpr hcR))
  refine ⟨K,b/C,(c:ℝ)*e₀,hK,hKH,div_pos hb hC,mul_pos hcR he₀,?_⟩
  intro e he hecut
  let gp := sourceTracePath (fun ω : a.samples => γ ω) a.trace_continuous
  let sp := sourceTracePath (fun ω : a.samples => sourceScaleTrace c (γ ω)) (a.sourceScaled c hc).trace_continuous
  let A : Set C(ℝ≥0,ℂ) := {g | ENNReal.ofReal (b/C) ≤ ENNReal.ofReal (e^(-codimension κ))*volume (K ∩ sourceSausageSet g 0 δ e)}
  have hA : MeasurableSet A := measurableSet_le measurable_const
    (measurable_const.mul (source_sausage_local_volume_measurable 0 δ e K))
  have hmap := congrArg (fun μ : Measure C(ℝ≥0,ℂ) => μ A) (a.source_scale_trace_law hk hκ8 c hc)
  have hgm : Measurable gp := a.source_trace_path_measurable
  have hsm : Measurable sp := (a.sourceScaled c hc).source_trace_path_measurable
  rw [Measure.map_apply hgm hA,Measure.map_apply hsm hA] at hmap
  change ENNReal.ofReal p ≤ Q (gp ⁻¹' A)
  rw [hmap]
  have hmesh : e/(c:ℝ) < e₀ := (div_lt_iff₀ hcR).mpr (by simpa only [mul_comm] using hecut)
  apply (hseed (e/(c:ℝ)) (div_pos he hcR) hmesh).trans
  apply measure_mono
  intro ω hω
  have hh := hω.trans (source_sausage_scale_mass_bound κ hc (γ ω) T δ ht (closedBall z₀ 1) e he)
  change ENNReal.ofReal (b/C) ≤ _
  rw [ENNReal.ofReal_div_of_pos hC]
  apply (ENNReal.div_le_iff (by simpa using hC) ENNReal.ofReal_ne_top).mpr
  simpa only [C,K,sp,sourceTracePath,ContinuousMap.coe_mk,mul_comm] using hh
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
lemma source_volume_le_bilip_image {f : ℂ → ℂ} {S : Set ℂ} {L : ℝ≥0}
    (hf : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ (L:ℝ)*dist (f x) (f y)) :
    volume S ≤ (L:ℝ≥0∞)^2*volume (f '' S) := by
  have hinj : InjOn f S := by
    intro x hx y hy he
    have hh := hf x hx y hy
    rw [he,dist_self,mul_zero] at hh
    exact dist_le_zero.mp hh
  let g := Function.invFunOn f S
  have hleft : LeftInvOn g f S := hinj.leftInvOn_invFunOn
  have hLip : LipschitzOnWith L g (f '' S) := by
    apply LipschitzOnWith.of_dist_le_mul
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    rw [hleft hx,hleft hy]
    exact hf x hx y hy
  have hh := source_volume_lipschitz_image hLip
  rw [hleft.image_image] at hh
  exact hh
lemma source_chart_sausage_area {f : ℂ → ℂ} {K : Set ℂ} {r q : ℝ} {L : ℝ≥0}
    (hL : 0 < L) (_hr : 0 < r) (hq : 0 < q) (hqr : q/(L:ℝ) ≤ r)
    (hf : LipschitzOnWith L f (cthickening r K))
    (hlo : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ (L:ℝ)*dist (f x) (f y))
    (η γ : ℝ≥0 → ℂ) (s δ : ℝ≥0)
    (hid : ∀ u ∈ Icc 0 δ, η u ∈ cthickening r K → γ (s+u) = f (η u)) :
    volume (K ∩ sourceSausageSet η 0 δ (q/(L:ℝ))) ≤
      (L:ℝ≥0∞)^2*volume (sourceSausageSet γ s (s+δ) q) := by
  let S := K ∩ sourceSausageSet η 0 δ (q/(L:ℝ))
  have hin : f '' S ⊆ sourceSausageSet γ s (s+δ) q := by
    rintro _ ⟨z,hz,rfl⟩
    obtain ⟨u,hu,hzu⟩ := hz.2
    have huz : η u ∈ cthickening r K := by
      apply mem_cthickening_of_dist_le (η u) z r K hz.1
      exact (by simpa only [dist_comm] using hzu.le.trans hqr)
    have hh := hf.dist_le_mul z (self_subset_cthickening (δ := r) K hz.1) (η u) huz
    have hdist : dist (f z) (γ (s+u)) < q := by
      rw [hid u hu huz]
      apply hh.trans_lt
      exact (mul_lt_mul_of_pos_left hzu (show 0 < (L:ℝ) from hL)).trans_eq (by field_simp)
    exact ⟨s+u,⟨by simp,add_le_add le_rfl hu.2⟩,hdist⟩
  exact (source_volume_le_bilip_image (fun x hx y hy => hlo x hx.1 y hy.1)).trans
    (mul_le_mul' le_rfl (measure_mono hin))
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
lemma source_inverse_translated_chart_compact_bounds
    (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness U γ G F) (s : ℝ≥0)
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ upperHalfPlane) :
    ∃ (r : ℝ) (L : ℝ≥0), 0 < r ∧ 0 < L ∧
      cthickening r K ⊆ upperHalfPlane ∧
      LipschitzOnWith L (fun z => F s (z+(U s:ℂ))) (cthickening r K) ∧
      ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ (L:ℝ)*dist (F s (x+(U s:ℂ))) (F s (y+(U s:ℂ))) := by
  obtain ⟨r,hr,hrK⟩ := hK.exists_cthickening_subset_open isOpen_upperHalfPlane hKH
  have hKr : IsCompact (cthickening r K) := hK.cthickening
  let Z := (fun z : ℂ => z+(U s:ℂ)) '' cthickening r K
  have hZ : IsCompact Z := hKr.image (continuous_id.add_const _)
  have hZH : Z ⊆ upperHalfPlane := by
    rintro _ ⟨z,hz,rfl⟩
    simpa only [upperHalfPlane,mem_ofPred_eq,add_im,ofReal_im,add_zero] using hrK hz
  obtain ⟨L,hL,hLip,hLo⟩ := source_inverse_chart_compact_bilipschitz U γ G F hw s hZ hZH
  refine ⟨r,L,hr,hL,hrK,?_,?_⟩
  · apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [dist_add_right] using hLip.dist_le_mul (x+(U s:ℂ)) ⟨x,hx,rfl⟩ (y+(U s:ℂ)) ⟨y,hy,rfl⟩
  · intro x hx y hy
    simpa only [dist_add_right] using hLo (x+(U s:ℂ)) ⟨x,self_subset_cthickening K hx,rfl⟩
      (y+(U s:ℂ)) ⟨y,self_subset_cthickening K hy,rfl⟩
lemma source_restart_sausage_countable_bound
    (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness U γ G F) (s δ : ℝ≥0) (η : ℝ≥0 → ℂ)
    (hid : ∀ u, η u ∈ upperHalfPlane → γ (s+u) = F s (η u+(U s:ℂ)))
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ upperHalfPlane) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ q : ℝ, 0 < q → q < 1/(N:ℝ) →
      volume (K ∩ sourceSausageSet η 0 δ (q/(N:ℝ))) ≤
        (N:ℝ≥0∞)^2*volume (sourceSausageSet γ s (s+δ) q) := by
  obtain ⟨r,L,hr,hL,hrK,hLip,hLo⟩ := source_inverse_translated_chart_compact_bounds U γ G F hw s hK hKH
  obtain ⟨N,hN⟩ := exists_nat_gt (max 1 (max (L:ℝ) r⁻¹))
  have hN1 : 1 ≤ N := by exact_mod_cast (le_max_left 1 (max (L:ℝ) r⁻¹)).trans hN.le
  have hNp : 0 < (N:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN1)
  have hLN : (L:ℝ) ≤ N := (le_max_left (L:ℝ) r⁻¹).trans ((le_max_right _ _).trans hN.le)
  have hrN : 1/(N:ℝ) ≤ r := by
    have h := (le_max_right (L:ℝ) r⁻¹).trans ((le_max_right 1 _).trans hN.le)
    apply (div_le_iff₀ hNp).mpr
    have hh := (inv_le_iff_one_le_mul₀ hr).mp h
    simpa only [mul_comm] using hh
  refine ⟨N,hN1,?_⟩
  intro q hq hqN
  have hqdiv : q/(N:ℝ) ≤ r := by
    have hh : q/(N:ℝ) ≤ q := div_le_self hq.le (by exact_mod_cast hN1)
    exact hh.trans (hqN.le.trans hrN)
  exact source_chart_sausage_area (L := (N:ℝ≥0)) (by exact_mod_cast hNp) hr hq hqdiv
    (hLip.weaken (by exact_mod_cast hLN))
    (fun x hx y hy => (hLo x hx y hy).trans (mul_le_mul_of_nonneg_right hLN dist_nonneg))
    η γ s δ (fun u _ hu => hid u (hrK hu))
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance sausageScalingMeshPathMeasurableSpace : MeasurableSpace C(ℝ≥0,ℂ) := borel _
local instance sausageScalingMeshPathBorelSpace : BorelSpace C(ℝ≥0,ℂ) := ⟨rfl⟩
lemma source_sausage_mono_mesh (γ : ℝ≥0 → ℂ) (s t : ℝ≥0) {r e : ℝ} (hle : r ≤ e) :
    sourceSausageSet γ s t r ⊆ sourceSausageSet γ s t e := by
  rintro z ⟨u,hu,hz⟩
  exact ⟨u,hu,hz.trans_le hle⟩
def sourceSausageChartGood (η γ : ℝ≥0 → ℂ) (K : Set ℂ) (s δ : ℝ≥0) (N : ℕ) : Prop :=
  1 ≤ N ∧ ∀ q : ℚ, 0 < (q:ℝ) → (q:ℝ) < 1/(N:ℝ) →
    volume (K ∩ sourceSausageSet η 0 δ ((q:ℝ)/(N:ℝ))) ≤
      (N:ℝ≥0∞)^2*volume (sourceSausageSet γ s (s+δ) (q:ℝ))
lemma source_chart_good_mono (η γ : ℝ≥0 → ℂ) (K : Set ℂ) (s δ : ℝ≥0) :
    Monotone (fun N : ℕ => sourceSausageChartGood η γ K s δ N) := by
  intro M N hMN hM
  refine ⟨hM.1.trans hMN,?_⟩
  intro q hq hqN
  have hMp : 0 < (M:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM.1)
  have hMrN : (M:ℝ) ≤ N := by exact_mod_cast hMN
  have hqM : (q:ℝ) < 1/(M:ℝ) := hqN.trans_le (one_div_le_one_div_of_le hMp hMrN)
  calc
    _ ≤ volume (K ∩ sourceSausageSet η 0 δ ((q:ℝ)/(M:ℝ))) :=
      measure_mono (inter_subset_inter_right K (source_sausage_mono_mesh η 0 δ (div_le_div_of_nonneg_left hq.le hMp hMrN)))
    _ ≤ (M:ℝ≥0∞)^2*volume (sourceSausageSet γ s (s+δ) (q:ℝ)) := hM.2 q hq hqM
    _ ≤ _ := by gcongr
lemma source_chart_good_measurable {Ω : Type*} [MeasurableSpace Ω]
    (η γ : Ω → C(ℝ≥0,ℂ)) (hmη : Measurable η) (hmγ : Measurable γ)
    (K : Set ℂ) (s δ : ℝ≥0) (N : ℕ) :
    MeasurableSet {ω | sourceSausageChartGood (η ω) (γ ω) K s δ N} := by
  simp only [sourceSausageChartGood,ofPred_and,ofPred_forall]
  apply MeasurableSet.inter (by measurability)
  apply MeasurableSet.iInter; intro q
  apply MeasurableSet.iInter; intro hq
  apply MeasurableSet.iInter; intro hqN
  apply measurableSet_le
  · exact (source_sausage_local_volume_measurable 0 δ ((q:ℝ)/(N:ℝ)) K).comp hmη
  · have hmvol : Measurable (fun g : C(ℝ≥0,ℂ) => volume (sourceSausageSet g s (s+δ) (q:ℝ))) := by
      simpa only [univ_inter] using source_sausage_local_volume_measurable s (s+δ) (q:ℝ) univ
    exact measurable_const.mul (hmvol.comp hmγ)
lemma source_chart_good_real_bound (η γ : ℝ≥0 → ℂ) (K : Set ℂ) (s δ : ℝ≥0) (N : ℕ)
    (hN : sourceSausageChartGood η γ K s δ N) {e : ℝ} (he : 0 < e) (heN : e < 1/(N:ℝ)) :
    volume (K ∩ sourceSausageSet η 0 δ (e/(2*(N:ℝ)))) ≤
      (N:ℝ≥0∞)^2*volume (sourceSausageSet γ s (s+δ) e) := by
  obtain ⟨q,hq1,hq2⟩ := exists_rat_btwn (show e/2 < e by linarith)
  have hNp : 0 < (N:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN.1)
  have hmesh : e/(2*(N:ℝ)) ≤ (q:ℝ)/(N:ℝ) := by rw [←div_div]; exact div_le_div_of_nonneg_right hq1.le hNp.le
  calc
    _ ≤ volume (K ∩ sourceSausageSet η 0 δ ((q:ℝ)/(N:ℝ))) :=
      measure_mono (inter_subset_inter_right K (source_sausage_mono_mesh η 0 δ hmesh))
    _ ≤ (N:ℝ≥0∞)^2*volume (sourceSausageSet γ s (s+δ) (q:ℝ)) := hN.2 q (by linarith) (hq2.trans heN)
    _ ≤ _ := mul_le_mul' le_rfl (measure_mono (source_sausage_mono_mesh γ s (s+δ) hq2.le))
lemma source_chart_good_high_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (η γ : Ω → C(ℝ≥0,ℂ)) (hmη : Measurable η) (hmγ : Measurable γ)
    (K : Set ℂ) (s δ : ℝ≥0)
    (hfull : ∀ᵐ ω ∂P, ∃ N : ℕ, sourceSausageChartGood (η ω) (γ ω) K s δ N)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 1 ≤ N ∧ P {ω | ¬sourceSausageChartGood (η ω) (γ ω) K s δ N} < ENNReal.ofReal ε := by
  let B := fun N : ℕ => {ω | ¬sourceSausageChartGood (η ω) (γ ω) K s δ N}
  have hB : ∀ N, MeasurableSet (B N) := fun N => (source_chart_good_measurable η γ hmη hmγ K s δ N).compl
  have hanti : Antitone B := by
    intro M N hMN ω hω hM
    exact hω (source_chart_good_mono (η ω) (γ ω) K s δ hMN hM)
  have hz : P (⋂ N, B N) = 0 := by
    have hh := ae_iff.mp hfull
    simpa only [B,not_exists,ofPred_forall] using hh
  have ht := tendsto_measure_iInter_atTop (fun N => (hB N).nullMeasurableSet) hanti
    ⟨0,measure_ne_top P _⟩
  rw [hz] at ht
  have hevv : ∀ᶠ N in atTop, P (B N) < ENNReal.ofReal ε :=
    ht.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hε))
  obtain ⟨N,hN,hp⟩ := ((eventually_ge_atTop 1).and hevv).exists
  exact ⟨N,hN,hp⟩
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance sausageScalingIntervalPathMeasurableSpace : MeasurableSpace C(ℝ≥0,ℂ) := borel _
local instance sausageScalingIntervalPathBorelSpace : BorelSpace C(ℝ≥0,ℂ) := ⟨rfl⟩
lemma source_sausage_mono_interval (γ : ℝ≥0 → ℂ) (e : ℝ) {s t u v : ℝ≥0}
    (hI : Icc s t ⊆ Icc u v) : sourceSausageSet γ s t e ⊆ sourceSausageSet γ u v e := by
  rintro z ⟨w,hw,hz⟩
  exact ⟨w,hI hw,hz⟩
lemma source_sausage_mass_mono_interval (κ : ℝ) (γ : ℝ≥0 → ℂ) (e : ℝ) {s t u v : ℝ≥0}
    (hI : Icc s t ⊆ Icc u v) : sourceSausageMass κ γ s t e ≤ sourceSausageMass κ γ u v e :=
  mul_le_mul' le_rfl (measure_mono (source_sausage_mono_interval γ e hI))
lemma RegularSLEPresentation.source_sausage_mass_measurable_at
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ}
    (a : RegularSLEPresentation P κ γ) (s t : ℝ≥0) (e : ℝ) :
    @Measurable a.samples ℝ≥0∞ (a.filtration t) inferInstance (fun ω => sourceSausageMass κ (γ ω) s t e) := by
  let f : a.samples → C(ℝ≥0,ℂ) := fun ω =>
    ⟨fun u => γ ω (min u t), (a.trace_continuous ω).comp (continuous_id.min continuous_const)⟩
  have hm : @Measurable a.samples C(ℝ≥0,ℂ) (a.filtration t) (borel _) f := by
    let : MeasurableSpace a.samples := a.filtration t
    apply source_path_measurable
    intro u
    exact (a.trace_adapted (min u t)).mono (a.filtration.mono (min_le_right u t)) le_rfl
  have he (ω : a.samples) : sourceSausageSet (γ ω) s t e = sourceSausageSet (f ω) s t e := by
    ext z
    constructor
    · rintro ⟨u,hu,huz⟩
      exact ⟨u,hu,by simpa only [f,ContinuousMap.coe_mk,min_eq_left hu.2] using huz⟩
    · rintro ⟨u,hu,huz⟩
      exact ⟨u,hu,by simpa only [f,ContinuousMap.coe_mk,min_eq_left hu.2] using huz⟩
  have he' : (fun ω : a.samples => sourceSausageMass κ (γ ω) s t e) =
      (fun ω => sourceSausageMass κ (f ω) s t e) := by
    funext ω; unfold sourceSausageMass; rw [he]
  rw [he']
  exact (source_sausage_mass_measurable κ s t e).comp hm
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
lemma source_chart_good_mass_bound (κ : ℝ) (η γ : ℝ≥0 → ℂ) (K : Set ℂ)
    (s δ : ℝ≥0) (N : ℕ) (hN : sourceSausageChartGood η γ K s δ N)
    {e : ℝ} (he : 0 < e) (heN : e < 1/(N:ℝ)) :
    ENNReal.ofReal ((e/(2*(N:ℝ)))^(-codimension κ))*
      volume (K ∩ sourceSausageSet η 0 δ (e/(2*(N:ℝ)))) ≤
    ENNReal.ofReal (((2*(N:ℝ))⁻¹)^(-codimension κ)*(N:ℝ)^2)*sourceSausageMass κ γ s (s+δ) e := by
  have hvol := source_chart_good_real_bound η γ K s δ N hN he heN
  have hnp : 0 < (N:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN.1)
  have hbase : 0 ≤ (2*(N:ℝ))⁻¹ := by positivity
  have hmul : (e/(2*(N:ℝ)))^(-codimension κ) = ((2*(N:ℝ))⁻¹)^(-codimension κ)*e^(-codimension κ) := by
    rw [show e/(2*(N:ℝ)) = (2*(N:ℝ))⁻¹*e by ring,Real.mul_rpow hbase he.le]
  have hh := mul_le_mul' (le_refl (ENNReal.ofReal ((e/(2*(N:ℝ)))^(-codimension κ)))) hvol
  apply hh.trans_eq
  rw [hmul,ENNReal.ofReal_mul (Real.rpow_nonneg hbase _),
    ENNReal.ofReal_mul (Real.rpow_nonneg hbase _),ENNReal.ofReal_pow (Nat.cast_nonneg N)]
  simp only [ENNReal.ofReal_natCast,sourceSausageMass]
  ac_rfl
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance SausageConditional_local1 : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance SausageConditional_local2 : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩
local instance SausageConditional_local3 : MeasurableSpace C(ℝ≥0,ℂ) := borel _
local instance SausageConditional_local4 : BorelSpace C(ℝ≥0,ℂ) := ⟨rfl⟩
lemma RegularSLEPresentation.source_uniform_sausage_slot_bound
    {Ω : Type} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 4 < κ) (hκ8 : κ < 8) :
    ∃ p : ℝ≥0∞, 0 < p ∧ p ≤ 1 ∧ ∀ (s δ : ℝ≥0), 0 < δ →
      ∀ ε : ℝ, 0 < ε → ∃ b e₀ : ℝ, 0 < b ∧ 0 < e₀ ∧
        ∀ e : ℝ, 0 < e → e < e₀ →
        ∀ A : Set a.samples, MeasurableSet[a.filtration s] A →
          (P.comap (Subtype.val : a.samples → Ω))
            (A ∩ {ω | sourceSausageMass κ (γ ω) s (s+δ) e < ENNReal.ofReal b}) ≤
          (1-p)*(P.comap (Subtype.val : a.samples → Ω)) A + ENNReal.ofReal ε := by
  have hk : 0 < κ := by linarith
  let Q := P.comap (Subtype.val : a.samples → Ω)
  obtain ⟨p,hp,hp1,hseed⟩ := a.source_uniform_sausage_seed hκ hκ8
  refine ⟨p,hp,hp1,?_⟩
  intro s δ hδ ε hε
  obtain ⟨K,b,e₀,hK,hKH,hb,he₀,hKP⟩ := hseed δ hδ
  obtain ⟨Φ,hΦm,hΦe,hrestart⟩ := sourceStoppedTraceLaw κ hk hκ8 a.B a.brownian
    a.measurable_B a.continuous_B (fun ω : a.samples => γ ω) a.G a.F a.witness
  let τ : a.samples → ℝ≥0 := fun _ => s
  have hτ : IsStoppingTime a.filtration (fun ω => (τ ω : WithTop ℝ≥0)) := isStoppingTime_const a.filtration s
  obtain ⟨hlaw,hident⟩ := hrestart τ hτ
  let rp := sourceRestartDriverPath a.B a.continuous_B τ
  let gp := sourceTracePath (fun ω : a.samples => γ ω) a.trace_continuous
  let η := fun ω : a.samples => Φ (rp ω)
  have hrm : Measurable rp := by
    apply source_path_measurable
    intro t
    exact (a.measurable_B (s+t)).sub (a.measurable_B s)
  have hem : Measurable η := hΦm.comp hrm
  have hgm : Measurable gp := a.source_trace_path_measurable
  have hfull : ∀ᵐ ω ∂Q, ∃ N : ℕ, sourceSausageChartGood (η ω) (gp ω) K s δ N := by
    filter_upwards [hident] with ω hω
    obtain ⟨N,hN,hbound⟩ := source_restart_sausage_countable_bound
      (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (a.F ω) (a.witness ω) s δ (η ω) hω hK hKH
    exact ⟨N,hN,fun q hq hqN => hbound q hq hqN⟩
  obtain ⟨N,hN,hbad⟩ := source_chart_good_high_probability Q η gp hem hgm K s δ hfull ε hε
  have hNp : 0 < (N:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  let C := ((2*(N:ℝ))⁻¹)^(-codimension κ)*(N:ℝ)^2
  have hC : 0 < C := mul_pos (Real.rpow_pos_of_pos (by positivity) _) (sq_pos_of_pos hNp)
  refine ⟨b/C,min (1/(N:ℝ)) (2*(N:ℝ)*e₀),div_pos hb hC,lt_min (by positivity) (by positivity),?_⟩
  intro e he hecut A hA
  have hmesh : e/(2*(N:ℝ)) < e₀ := (div_lt_iff₀ (by positivity)).mpr
    (by simpa only [mul_comm] using hecut.trans_le (min_le_right _ _))
  let D : Set C(ℝ≥0,ℂ) := {g | ENNReal.ofReal b ≤ ENNReal.ofReal ((e/(2*(N:ℝ)))^(-codimension κ))*
      volume (K ∩ sourceSausageSet g 0 δ (e/(2*(N:ℝ))))}
  let E : Set a.samples := η ⁻¹' D
  let B : Set a.samples := {ω | ¬sourceSausageChartGood (η ω) (gp ω) K s δ N}
  have hD : MeasurableSet D := measurableSet_le measurable_const
    (measurable_const.mul (source_sausage_local_volume_measurable 0 δ (e/(2*(N:ℝ))) K))
  have hEm : MeasurableSet E := hD.preimage hem
  have hAm : MeasurableSet A := (a.filtration.le s) A hA
  have hAstop : MeasurableSet[hτ.measurableSpace] A := by
    change MeasurableSet[(isStoppingTime_const a.filtration s).measurableSpace] A
    rw [IsStoppingTime.measurableSpace_const]
    exact hA
  have hprob : p*Q A ≤ Q (A ∩ E) := by
    have hEq := congrArg (fun μ : Measure C(ℝ≥0,ℂ) => μ D) (hlaw A hAstop)
    rw [Measure.map_apply hem hD,Measure.smul_apply,Measure.map_apply hgm hD,
      Measure.restrict_apply (hD.preimage hem)] at hEq
    change Q (E ∩ A) = Q A*Q {ω | ENNReal.ofReal b ≤ ENNReal.ofReal ((e/(2*(N:ℝ)))^(-codimension κ))*
      volume (K ∩ sourceSausageSet (γ ω) 0 δ (e/(2*(N:ℝ))))} at hEq
    rw [inter_comm] at hEq
    rw [hEq,mul_comm p (Q A)]
    exact mul_le_mul' le_rfl (hKP (e/(2*(N:ℝ))) (by positivity) hmesh)
  have hins : A ∩ {ω | sourceSausageMass κ (γ ω) s (s+δ) e < ENNReal.ofReal (b/C)} ⊆ (A \ E) ∪ B := by
    intro ω hω
    by_cases hG : sourceSausageChartGood (η ω) (gp ω) K s δ N
    · left
      refine ⟨hω.1,?_⟩
      intro hE
      have hEE : ENNReal.ofReal b ≤ ENNReal.ofReal ((e/(2*(N:ℝ)))^(-codimension κ))*
          volume (K ∩ sourceSausageSet (η ω) 0 δ (e/(2*(N:ℝ)))) := hE
      have hmass := hEE.trans (source_chart_good_mass_bound κ (η ω) (gp ω) K s δ N hG he
        (hecut.trans_le (min_le_left _ _)))
      have hlow : ENNReal.ofReal (b/C) ≤ sourceSausageMass κ (γ ω) s (s+δ) e := by
        rw [ENNReal.ofReal_div_of_pos hC]
        apply (ENNReal.div_le_iff (by simpa using hC) ENNReal.ofReal_ne_top).mpr
        simpa only [C,gp,sourceTracePath,ContinuousMap.coe_mk,mul_comm] using hmass
      exact (not_lt_of_ge hlow) hω.2
    · exact Or.inr hG
  have hdiff : Q (A \ E) = Q A - Q (A ∩ E) := by
    have heq : A \ E = A \ (A ∩ E) := by ext ω; simp only [Set.mem_sdiff,mem_inter_iff]; tauto
    rw [heq]
    exact measure_sdiff inter_subset_left (hAm.inter hEm).nullMeasurableSet (measure_ne_top Q _)
  calc
    Q (A ∩ {ω | sourceSausageMass κ (γ ω) s (s+δ) e < ENNReal.ofReal (b/C)})
        ≤ Q ((A \ E) ∪ B) := measure_mono hins
    _ ≤ Q (A \ E) + Q B := measure_union_le _ _
    _ ≤ (Q A-p*Q A)+ENNReal.ofReal ε := by rw [hdiff]; exact add_le_add (tsub_le_tsub_left hprob _) hbad.le
    _ = (1-p)*Q A+ENNReal.ofReal ε := by
      rw [ENNReal.sub_mul (fun _ _ => measure_ne_top Q A),one_mul]
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
lemma RegularSLEPresentation.source_sausage_nslot_bound
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 4 < κ) (hκ8 : κ < 8) :
    ∃ c : ℝ≥0∞, c < 1 ∧ ∀ (s δ : ℝ≥0), 0 < δ → ∀ ν : ℝ, 0 < ν →
      ∀ n : ℕ, ∃ b e₀ : ℝ, 0 < b ∧ 0 < e₀ ∧ ∀ e : ℝ, 0 < e → e < e₀ →
        (P.comap (Subtype.val : a.samples → Ω))
          {ω | sourceSausageMass κ (γ ω) s (s+(n:ℝ≥0)*δ) e < ENNReal.ofReal b} ≤
        c^n + (n:ℝ≥0∞)*ENNReal.ofReal ν := by
  let Q := P.comap (Subtype.val : a.samples → Ω)
  obtain ⟨p,hp,hp1,hslot⟩ := a.source_uniform_sausage_slot_bound hκ hκ8
  let c : ℝ≥0∞ := 1-p
  have hc : c < 1 := ENNReal.sub_lt_self (by simp) (by simp) hp.ne'
  refine ⟨c,hc,?_⟩
  intro s δ hδ ν hν n
  induction n with
  | zero =>
    refine ⟨1,1,by norm_num,by norm_num,?_⟩
    intro e he hel
    simpa only [pow_zero,Nat.cast_zero,zero_mul,add_zero] using
      (prob_le_one (μ := Q) (s := {ω | sourceSausageMass κ (γ ω) s (s+(0:ℝ≥0)*δ) e < ENNReal.ofReal 1}))
  | succ n ih =>
    obtain ⟨b₀,e₀,hb₀,he₀,hprev⟩ := ih
    obtain ⟨b₁,e₁,hb₁,he₁,hstep⟩ := hslot (s+(n:ℝ≥0)*δ) δ hδ ν hν
    refine ⟨min b₀ b₁,min e₀ e₁,lt_min hb₀ hb₁,lt_min he₀ he₁,?_⟩
    intro e he hel
    have hend : s+((n+1:ℕ):ℝ≥0)*δ = (s+(n:ℝ≥0)*δ)+δ := by push_cast; ring
    let A : Set a.samples := {ω | sourceSausageMass κ (γ ω) s (s+(n:ℝ≥0)*δ) e < ENNReal.ofReal b₀}
    have hA : MeasurableSet[a.filtration (s+(n:ℝ≥0)*δ)] A :=
      measurableSet_lt (a.source_sausage_mass_measurable_at s _ e) measurable_const
    rw [hend]
    calc
      Q {ω | sourceSausageMass κ (γ ω) s (s+(n:ℝ≥0)*δ+δ) e < ENNReal.ofReal (min b₀ b₁)}
          ≤ Q (A ∩ {ω | sourceSausageMass κ (γ ω) (s+(n:ℝ≥0)*δ) (s+(n:ℝ≥0)*δ+δ) e < ENNReal.ofReal b₁}) := by
          apply measure_mono
          intro ω hω
          constructor
          · exact ((source_sausage_mass_mono_interval κ (γ ω) e
              (Icc_subset_Icc le_rfl (le_add_of_nonneg_right (show 0 ≤ δ from bot_le)))).trans_lt hω).trans_le
                (ENNReal.ofReal_le_ofReal (min_le_left _ _))
          · exact ((source_sausage_mass_mono_interval κ (γ ω) e
              (Icc_subset_Icc (le_add_of_nonneg_right (by positivity)) le_rfl)).trans_lt hω).trans_le
                (ENNReal.ofReal_le_ofReal (min_le_right _ _))
      _ ≤ c*Q A+ENNReal.ofReal ν := hstep e he (hel.trans_le (min_le_right _ _)) A hA
      _ ≤ c*(c^n+(n:ℝ≥0∞)*ENNReal.ofReal ν)+ENNReal.ofReal ν := by
          exact add_le_add (mul_le_mul' le_rfl (hprev e he (hel.trans_le (min_le_left _ _)))) le_rfl
      _ ≤ c^(n+1)+((n+1:ℕ):ℝ≥0∞)*ENNReal.ofReal ν := by
          rw [mul_add,pow_succ,mul_comm (c^n) c,Nat.cast_add,Nat.cast_one,add_mul,one_mul]
          rw [←add_assoc]
          exact add_le_add (add_le_add le_rfl (mul_le_of_le_one_left' hc.le)) le_rfl
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
lemma RegularSLEPresentation.source_small_sausage
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 4 < κ) (hκ8 : κ < 8) (s t : ℝ≥0) (hst : s < t) (ε : ℝ) (hε : 0 < ε) :
    ∃ b e₀ : ℝ, 0 < b ∧ 0 < e₀ ∧ ∀ e : ℝ, 0 < e → e < e₀ →
      (P.comap (Subtype.val : a.samples → Ω))
        {ω | sourceSausageMass κ (γ ω) s t e < ENNReal.ofReal b} < ENNReal.ofReal ε := by
  obtain ⟨c,hc,hsteps⟩ := a.source_sausage_nslot_bound hκ hκ8
  have hev : ∀ᶠ n : ℕ in atTop, c^n < ENNReal.ofReal (ε/4) :=
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hc).eventually
      (gt_mem_nhds (ENNReal.ofReal_pos.mpr (by positivity)))
  obtain ⟨n,hn,hcn⟩ := ((eventually_ge_atTop 1).and hev).exists
  have hn0 : 0 < (n:ℝ≥0) := by exact_mod_cast (show 0 < n by omega)
  let δ : ℝ≥0 := (t-s)/(n:ℝ≥0)
  have hδ : 0 < δ := div_pos (tsub_pos_iff_lt.mpr hst) hn0
  have hend : s+(n:ℝ≥0)*δ = t := by
    dsimp [δ]
    rw [mul_div_cancel₀ _ hn0.ne',add_tsub_cancel_of_le hst.le]
  let ν : ℝ := ε/(4*((n:ℝ)+1))
  have hν : 0 < ν := by dsimp [ν]; positivity
  obtain ⟨b,e₀,hb,he₀,hbound⟩ := hsteps s δ hδ ν hν n
  have hnν : (n:ℝ≥0∞)*ENNReal.ofReal ν ≤ ENNReal.ofReal (ε/4) := by
    rw [←ENNReal.ofReal_natCast,←ENNReal.ofReal_mul (Nat.cast_nonneg n)]
    apply ENNReal.ofReal_le_ofReal
    calc (n:ℝ)*ν ≤ ((n:ℝ)+1)*ν := mul_le_mul_of_nonneg_right (by linarith) hν.le
      _ = ε/4 := by dsimp [ν]; field_simp
  refine ⟨b,e₀,hb,he₀,?_⟩
  intro e he hel
  have hh := hbound e he hel
  rw [hend] at hh
  apply hh.trans_lt
  calc c^n+(n:ℝ≥0∞)*ENNReal.ofReal ν
      ≤ ENNReal.ofReal (ε/4)+ENNReal.ofReal (ε/4) := add_le_add hcn.le hnν
    _ = ENNReal.ofReal (ε/2) := by rw [←ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
    _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).mpr (by linarith)
theorem sourceSmallSausage_proved : SourceSmallSausageTarget := by
  intro κ hκ hκ8 Ω m P hP γ hSLE s t hst ε hε
  let : IsProbabilityMeasure P := hP
  obtain ⟨a⟩ := exists_regular_sle_presentation hSLE
  obtain ⟨b,e₀,hb,he₀,hbound⟩ := a.source_small_sausage hκ hκ8 s t hst ε hε
  refine ⟨b,e₀,hb,he₀,?_⟩
  intro e he hel
  have hh := hbound e he hel
  rw [←a.measurePreserving_val.map_eq]
  rwa [(MeasurableEmbedding.subtype_coe a.measurable_samples).map_apply] 
end
end SLEExactGauge
end

end OAI
