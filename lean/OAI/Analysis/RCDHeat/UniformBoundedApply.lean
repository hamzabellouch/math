import Mathlib
import OAI.Analysis.RCDHeat.HeatEnergy

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: UniformBoundedApply, HeatDifferentiable, HeatEVI, LipschitzCalculus, SobolevAlgebra. -/



open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
namespace RegularPointCoordinates
universe u
open Metric
section UniformBoundedApply
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι α : Type*} {l : Filter ι} {s : Set α}

 theorem tendstoUniformlyOn_bounded_apply {B : α → E →L[ℝ] F} {C : ℝ}
    (hC : 0 ≤ C) (hB : ∀ t ∈ s, ‖B t‖ ≤ C)
    {v : ι → E} {w : E} (hv : Tendsto v l (𝓝 w)) :
    TendstoUniformlyOn (fun i t => B t (v i)) (fun t => B t w) l s := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hCp : 0 < C+1 := by linarith
  filter_upwards [Metric.tendsto_nhds.mp hv (ε/(C+1)) (div_pos hε hCp)] with i hi
  intro t ht
  have hn := (B t).le_of_opNorm_le (hB t ht) (w-v i)
  simp only [map_sub, ← dist_eq_norm] at hn
  calc
    dist (B t w) (B t (v i)) ≤ C * dist w (v i) := hn
    _ ≤ (C+1) * dist (v i) w := by rw [dist_comm w]; nlinarith [(dist_nonneg : 0 ≤ dist (v i) w)]
    _ < ε := by simpa only [mul_comm] using (lt_div_iff₀ hCp).mp hi

end UniformBoundedApply

section HeatDifferentiable
variable {X : Type u} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
  [ProperSpace X] [BorelSpace X] [μ.Regular]

noncomputable def heatGeneratorAt (t : ℝ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  if ht : 0 < t then heatGenerator μ hQ t ht else 0

 theorem heatGeneratorAt_of_pos (t : ℝ) (ht : 0 < t) :
    heatGeneratorAt μ hQ t = heatGenerator μ hQ t ht := by simp only [heatGeneratorAt, dite_eq_left ht]

 theorem heatGeneratorAt_norm_le_of_ge (a : ℝ) (ha : 0 < a) (t : ℝ) (ht : a ≤ t) :
    ‖heatGeneratorAt μ hQ t‖ ≤ 2*(1+1/a) := by
  rw [heatGeneratorAt_of_pos μ hQ t (ha.trans_le ht)]
  exact (heatGenerator_norm_le μ hQ t (ha.trans_le ht)).trans
    (by have h := one_div_le_one_div_of_le ha ht; linarith)

 
 theorem heatAt_hasDerivAt (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ) :
    HasDerivAt (fun s => heatAt μ hQ s f) (-heatGeneratorAt μ hQ t f) t := by
  obtain ⟨fs, hfs, hconv⟩ := mem_closure_iff_seq_limit.mp
    (resolventLp_denseRange μ hQ 1 zero_lt_one f)
  have hC : 0 ≤ 2*(1+1/(t/2)) := by positivity
  have hbound (s : ℝ) (hs : s ∈ Ioo (t/2) (t+1)) :
      ‖heatGeneratorAt μ hQ s‖ ≤ 2*(1+1/(t/2)) :=
    heatGeneratorAt_norm_le_of_ge μ hQ (t/2) (half_pos ht) s hs.1.le
  have huni := (tendstoUniformlyOn_bounded_apply hC hbound hconv).neg
  refine hasDerivAt_of_tendstoUniformlyOn (f := fun i s => heatAt μ hQ s (fs i))
    isOpen_Ioo huni ?_ ?_ ⟨by linarith, by linarith⟩
  · apply Eventually.of_forall
    intro i s hs
    change HasDerivAt (fun s => heatAt μ hQ s (fs i)) (-heatGeneratorAt μ hQ s (fs i)) s
    obtain ⟨g, hg⟩ := hfs i
    rw [← hg, heatGeneratorAt_of_pos μ hQ s ((half_pos ht).trans hs.1), heatGenerator_core]
    exact heatAt_core_hasDerivAt μ hQ s ((half_pos ht).trans hs.1) g
  · intro s _
    exact (heatAt μ hQ s).continuous.continuousAt.tendsto.comp hconv

 theorem heatGenerator_add (s t : ℝ) (hs : 0 ≤ s) (ht : 0 < t) :
    heatGenerator μ hQ (s+t) (by linarith) = heatAt μ hQ s * heatGenerator μ hQ t ht := by
  have he : (fun f => heatGenerator μ hQ (s+t) (by linarith) f) =
      (fun f => heatAt μ hQ s (heatGenerator μ hQ t ht f)) := by
    apply (resolventLp_denseRange μ hQ 1 zero_lt_one).equalizer
      (heatGenerator μ hQ (s+t) (by linarith)).continuous
      ((heatAt μ hQ s).continuous.comp (heatGenerator μ hQ t ht).continuous)
    funext f
    simp only [Function.comp_apply]
    rw [heatGenerator_core, heatGenerator_core, heatAt_add μ hQ s t hs ht.le,
      mul_apply_eq_comp]
  exact ContinuousLinearMap.ext (congrFun he)

end HeatDifferentiable

section HeatEVI
variable {X : Type u} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

 theorem energyForm_sub_right (f g h : SobolevSpace μ hQ) :
    energyForm μ hQ f (g-h) = energyForm μ hQ f g - energyForm μ hQ f h := by
  simp only [energyForm, map_sub, inner_sub_right]
  ring

 theorem SobolevSpace.energy_sub_eq (f g : SobolevSpace μ hQ) :
    SobolevSpace.energy μ hQ (f-g) = SobolevSpace.energy μ hQ f +
      SobolevSpace.energy μ hQ g - energyForm μ hQ f g := by
  simp only [SobolevSpace.energy_eq_norms, map_sub, norm_sub_sq_real, energyForm]
  ring

variable [ProperSpace X] [BorelSpace X] [μ.Regular]

 
 theorem heatAt_dist_sq_hasDerivAt (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ)
    (g : SobolevSpace μ hQ) :
    HasDerivAt (fun s => ‖heatAt μ hQ s f - SobolevSpace.toLp μ hQ g‖^2)
      (2*(SobolevSpace.energy μ hQ g -
        SobolevSpace.energy μ hQ (heatSobolev μ hQ t ht f) -
        SobolevSpace.energy μ hQ (g-heatSobolev μ hQ t ht f))) t := by
  have h := ((heatAt_hasDerivAt μ hQ t ht f).sub_const (SobolevSpace.toLp μ hQ g)).norm_sq
  rw [heatGeneratorAt_of_pos μ hQ t ht] at h
  have hF := heatGenerator_form μ hQ t ht f (heatSobolev μ hQ t ht f-g)
  rw [energyForm_sub_right, energyForm_self, map_sub, heatSobolev_toLp] at hF
  have hE := SobolevSpace.energy_sub_eq μ hQ g (heatSobolev μ hQ t ht f)
  rw [energyForm_comm μ hQ g] at hE
  convert h using 1
  rw [inner_neg_right, real_inner_comm, ← hF]
  linarith

 theorem heatAt_evi (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ) (g : SobolevSpace μ hQ) :
    deriv (fun s => ‖heatAt μ hQ s f - SobolevSpace.toLp μ hQ g‖^2) t ≤
      2*(SobolevSpace.energy μ hQ g - SobolevSpace.energy μ hQ (heatSobolev μ hQ t ht f)) := by
  rw [(heatAt_dist_sq_hasDerivAt μ hQ t ht f g).deriv]
  linarith [SobolevSpace.energy_nonneg μ hQ (g-heatSobolev μ hQ t ht f)]

 
noncomputable def heatTail (a : ℝ) (ha : 0 < a) (f : Lp ℝ 2 μ) (t : ℝ) : SobolevSpace μ hQ :=
  heatSobolevMap μ hQ a ha (heatAt μ hQ (t-a) f)

 theorem heatTail_toLp (a : ℝ) (ha : 0 < a) (f : Lp ℝ 2 μ) (t : ℝ) (ht : a ≤ t) :
    SobolevSpace.toLp μ hQ (heatTail μ hQ a ha f t) = heatAt μ hQ t f := by
  change heatAt μ hQ a (heatAt μ hQ (t-a) f) = _
  rw [← mul_apply_eq_comp, ← heatAt_add μ hQ a (t-a) ha.le (sub_nonneg.mpr ht)]
  have he : a+(t-a)=t := by ring
  simp only [he]

 theorem heatTail_eq (a : ℝ) (ha : 0 < a) (f : Lp ℝ 2 μ) (t : ℝ) (ht : a ≤ t) :
    heatTail μ hQ a ha f t = heatSobolev μ hQ t (ha.trans_le ht) f := by
  apply Subtype.ext
  exact heatTail_toLp μ hQ a ha f t ht

 theorem heatTail_hasDerivAt (a : ℝ) (ha : 0 < a) (f : Lp ℝ 2 μ) (t : ℝ) (ht : a < t) :
    HasDerivAt (heatTail μ hQ a ha f)
      (heatSobolevMap μ hQ a ha (-heatGeneratorAt μ hQ (t-a) f)) t := by
  have h := (heatAt_hasDerivAt μ hQ (t-a) (sub_pos.mpr ht) f).scomp t ((hasDerivAt_id t).sub_const a)
  simp only [one_smul] at h
  exact (heatSobolevMap μ hQ a ha).hasFDerivAt.comp_hasDerivAt t h

 theorem heatTail_deriv_toLp (a : ℝ) (ha : 0 < a) (f : Lp ℝ 2 μ) (t : ℝ) (ht : a < t) :
    SobolevSpace.toLp μ hQ (heatSobolevMap μ hQ a ha (-heatGeneratorAt μ hQ (t-a) f)) =
      -heatGeneratorAt μ hQ t f := by
  change heatAt μ hQ a (-heatGeneratorAt μ hQ (t-a) f) = _
  rw [map_neg, heatGeneratorAt_of_pos μ hQ (t-a) (sub_pos.mpr ht),
    heatGeneratorAt_of_pos μ hQ t (ha.trans ht), ← mul_apply_eq_comp,
    ← heatGenerator_add μ hQ a (t-a) ha.le (sub_pos.mpr ht)]
  have he : a+(t-a)=t := by ring
  simp only [he]

 theorem heatAt_energy_hasDerivAt (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ) :
    HasDerivAt (fun s => (energyLp μ (heatAt μ hQ s f)).toReal)
      (-‖heatGeneratorAt μ hQ t f‖^2) t := by
  have hat : t/2 < t := by linarith
  have h := SobolevSpace.energy_hasDerivAt μ hQ
    (heatTail_hasDerivAt μ hQ (t/2) (half_pos ht) f t hat)
  have he : energyForm μ hQ (heatTail μ hQ (t/2) (half_pos ht) f t)
      (heatSobolevMap μ hQ (t/2) (half_pos ht) (-heatGeneratorAt μ hQ (t-t/2) f)) =
      -‖heatGeneratorAt μ hQ t f‖^2 := by
    rw [heatTail_eq μ hQ (t/2) (half_pos ht) f t hat.le, heatGenerator_form,
      heatTail_deriv_toLp μ hQ (t/2) (half_pos ht) f t hat,
      heatGeneratorAt_of_pos μ hQ t ht, inner_neg_right, real_inner_self_eq_norm_sq]
  rw [he] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hat] with s hs
  rw [SobolevSpace.energy, heatTail_toLp μ hQ (t/2) (half_pos ht) f s hs.le]

end HeatEVI

section LipschitzCalculus
variable {X : Type u} [MetricSpace X]

 theorem localSlope_comp_lipschitz {C : ℝ≥0} {φ : ℝ → ℝ}
    (hφ : LipschitzWith C φ) (f : X → ℝ) (x : X) :
    localSlope (φ ∘ f) x ≤ C * localSlope f x := by
  by_cases hC : C = 0
  · subst C
    have he : φ ∘ f = fun _ => φ 0 := by
      funext y
      apply dist_eq_zero.mp
      exact le_antisymm (by simpa using hφ.dist_le_mul (f y) 0) dist_nonneg
    simp only [he, localSlope_const, ENNReal.coe_zero, zero_mul, le_refl]
  · unfold localSlope
    rw [ENNReal.mul_iInf_of_ne (by exact_mod_cast hC) ENNReal.coe_ne_top]
    apply le_iInf fun r => ?_
    rw [ENNReal.mul_iInf_of_ne (by exact_mod_cast hC) ENNReal.coe_ne_top]
    apply le_iInf fun hr => ?_
    apply iInf_le_of_le r
    apply iInf_le_of_le hr
    simp_rw [ENNReal.mul_iSup]
    apply iSup_mono fun y => iSup_mono fun _ => iSup_mono fun _ => ?_
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg]
    apply ENNReal.ofReal_le_ofReal
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ dist_nonneg
    simpa only [Function.comp_apply, Real.dist_eq] using hφ.dist_le_mul (f y) (f x)

variable [MeasurableSpace X] (μ : Measure X)

 theorem slopeEnergy_comp_lipschitz {C : ℝ≥0} {φ : ℝ → ℝ}
    (hφ : LipschitzWith C φ) (f : X → ℝ) :
    slopeEnergy μ (φ ∘ f) ≤ (C : ℝ≥0∞)^2 * slopeEnergy μ f := by
  unfold slopeEnergy
  calc
    _ ≤ (2 : ℝ≥0∞)⁻¹ * ∫⁻ x, (C * localSlope f x)^2 ∂μ :=
      mul_le_mul' le_rfl (lintegral_mono fun x => pow_le_pow_left' (localSlope_comp_lipschitz hφ f x) 2)
    _ = _ := by
      simp_rw [mul_pow]
      rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.coe_ne_top)]
      ac_rfl

 theorem IsLipschitzApproximation.comp_lipschitz {C : ℝ≥0} {φ : ℝ → ℝ}
    (hφ : LipschitzWith C φ) (hφ0 : φ 0 = 0)
    {f : X → ℝ} {fs : ℕ → X → ℝ} (hfs : IsLipschitzApproximation μ f fs) :
    IsLipschitzApproximation μ (φ ∘ f) (fun i => φ ∘ fs i) := by
  constructor
  · intro i
    obtain ⟨hm, D, hD⟩ := hfs.1 i
    exact ⟨hφ.comp_memLp hφ0 hm, C*D, hφ.comp hD⟩
  · have hnorm (i : ℕ) : eLpNorm (fun x => φ (fs i x) - φ (f x)) 2 μ ≤
        (C : ℝ≥0∞) * eLpNorm (fun x => fs i x - f x) 2 μ := by
      rw [← ENNReal.ofReal_coe_nnreal]
      apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
        ((hφ.comp_memLp hφ0 (hfs.1 i).1).aestronglyMeasurable.sub
          (hφ.comp_memLp hφ0 hfs.memLp).aestronglyMeasurable)
      exact Eventually.of_forall fun x => by
        simpa only [Pi.sub_apply, Function.comp_apply, ← dist_eq_norm] using
          hφ.dist_le_mul (fs i x) (f x)
    have ht := ENNReal.Tendsto.const_mul (a := (C : ℝ≥0∞)) hfs.2 (Or.inr ENNReal.coe_ne_top)
    simp only [mul_zero] at ht
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => bot_le) hnorm

 theorem cheegerEnergy_comp_lipschitz {C : ℝ≥0} {φ : ℝ → ℝ}
    (hφ : LipschitzWith C φ) (hφ0 : φ 0 = 0) (f : X → ℝ) :
    cheegerEnergy μ (φ ∘ f) ≤ (C : ℝ≥0∞)^2 * cheegerEnergy μ f := by
  by_cases hC : C = 0
  · subst C
    have he : φ ∘ f = fun _ => 0 := by
      funext x
      have he : φ (f x) = φ 0 := dist_eq_zero.mp
        (le_antisymm (by simpa using hφ.dist_le_mul (f x) 0) dist_nonneg)
      exact he.trans hφ0
    simp only [he, cheegerEnergy_zero, ENNReal.coe_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, zero_mul, le_refl]
  · have hC0 : (C : ℝ≥0∞)^2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hC)
    have hCt : (C : ℝ≥0∞)^2 ≠ ∞ := ENNReal.pow_ne_top ENNReal.coe_ne_top
    unfold cheegerEnergy
    rw [ENNReal.mul_iInf_of_ne hC0 hCt]
    refine le_iInf fun fs => ?_
    rw [ENNReal.mul_iInf_of_ne hC0 hCt]
    refine le_iInf fun hfs => ?_
    calc
      _ ≤ liminf (fun i => slopeEnergy μ (φ ∘ fs i)) atTop :=
        cheegerEnergy_le_liminf μ (hfs.comp_lipschitz μ hφ hφ0)
      _ ≤ liminf (fun i => (C : ℝ≥0∞)^2 * slopeEnergy μ (fs i)) atTop :=
        liminf_le_liminf (Eventually.of_forall fun i => slopeEnergy_comp_lipschitz μ hφ (fs i))
      _ = _ := by rw [ENNReal.liminf_const_mul_of_ne_top hCt]; rfl

 theorem cheegerEnergy_comp_lipschitz_ne_top {C : ℝ≥0} {φ : ℝ → ℝ}
    (hφ : LipschitzWith C φ) (hφ0 : φ 0 = 0) {f : X → ℝ}
    (hf : cheegerEnergy μ f ≠ ∞) : cheegerEnergy μ (φ ∘ f) ≠ ∞ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) hf)
    (cheegerEnergy_comp_lipschitz μ hφ hφ0 f)

end LipschitzCalculus


noncomputable def clipReal (C : ℝ≥0) (x : ℝ) : ℝ := min (max x (-C)) C

 theorem clipReal_lipschitz (C : ℝ≥0) : LipschitzWith 1 (clipReal C) :=
  (LipschitzWith.id.max_const (-C)).min_const C

 theorem clipReal_eq_self (C : ℝ≥0) {x : ℝ} (hx : |x| ≤ C) : clipReal C x = x := by
  rw [clipReal, max_eq_left (abs_le.mp hx).1, min_eq_left (abs_le.mp hx).2]

 theorem clipReal_abs_le (C : ℝ≥0) (x : ℝ) : |clipReal C x| ≤ C := by
  rw [abs_le]
  exact ⟨le_min (le_max_right _ _) (by linarith [C.coe_nonneg]), min_le_right _ _⟩

 theorem clipReal_zero (C : ℝ≥0) : clipReal C 0 = 0 :=
  clipReal_eq_self C (by simp)

 theorem clipReal_sq_lipschitz (C : ℝ≥0) : LipschitzWith (2*C) (fun x => (clipReal C x)^2) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hd := (clipReal_lipschitz C).dist_le_mul x y
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hd
  have ha : |clipReal C x + clipReal C y| ≤ 2*(C:ℝ) :=
    (abs_add_le _ _).trans (by linarith [clipReal_abs_le C x, clipReal_abs_le C y])
  simp only [Real.dist_eq, NNReal.coe_mul, NNReal.coe_ofNat]
  rw [sq_sub_sq, abs_mul]
  calc
    _ ≤ (2*(C:ℝ)) * |x-y| := mul_le_mul ha hd (abs_nonneg _) (by positivity)

variable {X : Type u} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

 
noncomputable def SobolevSpace.comp {C : ℝ≥0} {φ : ℝ → ℝ}
    (hφ : LipschitzWith C φ) (hφ0 : φ 0 = 0) (f : SobolevSpace μ hQ) : SobolevSpace μ hQ :=
  ⟨hφ.compLp hφ0 (SobolevSpace.toLp μ hQ f), by
    change cheegerEnergy μ _ ≠ ∞
    rw [cheegerEnergy_congr_ae μ (hφ.coeFn_compLp hφ0 (SobolevSpace.toLp μ hQ f))]
    exact cheegerEnergy_comp_lipschitz_ne_top μ hφ hφ0 f.property⟩

 theorem SobolevSpace.comp_coe {C : ℝ≥0} {φ : ℝ → ℝ}
    (hφ : LipschitzWith C φ) (hφ0 : φ 0 = 0) (f : SobolevSpace μ hQ) :
    (SobolevSpace.toLp μ hQ (SobolevSpace.comp μ hQ hφ hφ0 f)) =ᵐ[μ]
      (φ ∘ (SobolevSpace.toLp μ hQ f)) := hφ.coeFn_compLp hφ0 _

 theorem SobolevSpace.comp_energy_le {C : ℝ≥0} {φ : ℝ → ℝ}
    (hφ : LipschitzWith C φ) (hφ0 : φ 0 = 0) (f : SobolevSpace μ hQ) :
    SobolevSpace.energy μ hQ (SobolevSpace.comp μ hQ hφ hφ0 f) ≤
      (C : ℝ)^2 * SobolevSpace.energy μ hQ f := by
  have he : energyLp μ (SobolevSpace.toLp μ hQ (SobolevSpace.comp μ hQ hφ hφ0 f)) ≤
      (C : ℝ≥0∞)^2 * energyLp μ (SobolevSpace.toLp μ hQ f) := by
    unfold energyLp
    rw [cheegerEnergy_congr_ae μ (SobolevSpace.comp_coe μ hQ hφ hφ0 f)]
    exact cheegerEnergy_comp_lipschitz μ hφ hφ0 _
  have ht := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) f.property) he
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal] at ht
  exact ht

noncomputable def SobolevSpace.square (f : SobolevSpace μ hQ) (C : ℝ≥0) : SobolevSpace μ hQ :=
  SobolevSpace.comp μ hQ (clipReal_sq_lipschitz C) (by rw [clipReal_zero]; norm_num) f

 theorem SobolevSpace.square_coe (f : SobolevSpace μ hQ) (C : ℝ≥0)
    (hf : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ f x| ≤ C) :
    SobolevSpace.toLp μ hQ (SobolevSpace.square μ hQ f C) =ᵐ[μ]
      (fun x => (SobolevSpace.toLp μ hQ f x)^2) := by
  filter_upwards [SobolevSpace.comp_coe μ hQ (clipReal_sq_lipschitz C)
    (show (clipReal C 0)^2 = 0 by rw [clipReal_zero]; norm_num) f, hf] with x hx hfx
  simpa only [SobolevSpace.square, Function.comp_apply, clipReal_eq_self C hfx] using hx

 theorem SobolevSpace.square_energy_le (f : SobolevSpace μ hQ) (C : ℝ≥0) :
    SobolevSpace.energy μ hQ (SobolevSpace.square μ hQ f C) ≤
      4*(C:ℝ)^2 * SobolevSpace.energy μ hQ f := by
  have h := SobolevSpace.comp_energy_le μ hQ (clipReal_sq_lipschitz C)
    (show (clipReal C 0)^2 = 0 by rw [clipReal_zero]; norm_num) f
  simp only [NNReal.coe_mul, NNReal.coe_ofNat] at h
  dsimp only [SobolevSpace.square]
  nlinarith [h]

 

noncomputable def SobolevSpace.product (f g : SobolevSpace μ hQ) (C D : ℝ≥0) : SobolevSpace μ hQ :=
  (1/4 : ℝ) • (SobolevSpace.square μ hQ (f+g) (C+D) -
    SobolevSpace.square μ hQ (f-g) (C+D))

 theorem SobolevSpace.product_coe (f g : SobolevSpace μ hQ) (C D : ℝ≥0)
    (hf : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ f x| ≤ C)
    (hg : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ g x| ≤ D) :
    SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ f g C D) =ᵐ[μ]
      (fun x => SobolevSpace.toLp μ hQ f x * SobolevSpace.toLp μ hQ g x) := by
  have hp : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (f+g) x| ≤ (C+D:ℝ≥0) := by
    simp only [map_add]
    filter_upwards [hf, hg, Lp.coeFn_add (SobolevSpace.toLp μ hQ f) (SobolevSpace.toLp μ hQ g)]
      with x hfx hgx hx
    rw [hx]
    exact (abs_add_le _ _).trans (add_le_add hfx hgx)
  have hm : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (f-g) x| ≤ (C+D:ℝ≥0) := by
    simp only [map_sub]
    filter_upwards [hf, hg, Lp.coeFn_sub (SobolevSpace.toLp μ hQ f) (SobolevSpace.toLp μ hQ g)]
      with x hfx hgx hx
    rw [hx]
    exact (abs_sub _ _).trans (add_le_add hfx hgx)
  simp only [SobolevSpace.product, map_smul, map_sub]
  filter_upwards [Lp.coeFn_smul (1/4:ℝ)
    (SobolevSpace.toLp μ hQ (SobolevSpace.square μ hQ (f+g) (C+D)) -
    SobolevSpace.toLp μ hQ (SobolevSpace.square μ hQ (f-g) (C+D))),
    Lp.coeFn_sub (SobolevSpace.toLp μ hQ (SobolevSpace.square μ hQ (f+g) (C+D)))
      (SobolevSpace.toLp μ hQ (SobolevSpace.square μ hQ (f-g) (C+D))),
    SobolevSpace.square_coe μ hQ (f+g) (C+D) hp,
    SobolevSpace.square_coe μ hQ (f-g) (C+D) hm,
    Lp.coeFn_add (SobolevSpace.toLp μ hQ f) (SobolevSpace.toLp μ hQ g),
    Lp.coeFn_sub (SobolevSpace.toLp μ hQ f) (SobolevSpace.toLp μ hQ g)]
    with x hsm hsub hp hm hadd hdiff
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at hsm hsub
  simp only [map_add, map_sub] at hp hm
  rw [hsm, hsub, hp, hm, hadd, hdiff]
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

end RegularPointCoordinates

end OAI
