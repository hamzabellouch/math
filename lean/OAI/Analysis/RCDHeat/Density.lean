import Mathlib
import OAI.Analysis.RCDHeat.EnergyLp

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: Density, EnergyDensity, DenseDomain, ResolventMarkov, ParameterizedResolvent. -/



open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
namespace RegularPointCoordinates
universe u
open Metric
section Density
variable {X : Type*} [MetricSpace X] [ProperSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
  [μ.Regular]

 
theorem exists_lipschitz_eLpNorm_sub_indicator_le {s : Set X} (hs : IsCompact s)
    (c : ℝ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ f : X → ℝ, (∃ C : ℝ≥0, LipschitzWith C f) ∧ HasCompactSupport f ∧
      MemLp f 2 μ ∧ eLpNorm (fun x => f x - s.indicator (fun _ => c) x) 2 μ ≤ ε := by
  obtain ⟨η, η_pos, hη⟩ :
      ∃ η : ℝ≥0, 0 < η ∧ ∀ t : Set X, μ t ≤ η → NullMeasurableSet t μ →
        eLpNorm (t.indicator fun _x => c) 2 μ ≤ ε :=
    exists_eLpNorm_indicator_le (by norm_num : (2 : ℝ≥0∞) ≠ ∞) c hε
  obtain ⟨V, hsV, hVo, _, hV⟩ :=
    hs.measurableSet.exists_isOpen_sdiff_lt (hs.measure_lt_top (μ := μ)).ne
      (ENNReal.coe_pos.mpr η_pos).ne'
  obtain ⟨δ, hδ, hδV⟩ := hs.exists_cthickening_subset_open hVo hsV
  let g : X → ℝ := fun x => (thickenedIndicator hδ s x : ℝ)
  have hgLip : LipschitzWith δ.toNNReal⁻¹ g :=
    by
      simpa only [one_mul, Function.comp_def, g] using
        NNReal.isometry_coe.lipschitzWith.comp (lipschitzWith_thickenedIndicator hδ s)
  have hg0 (x : X) : 0 ≤ g x := NNReal.coe_nonneg _
  have hg1 (x : X) : g x ≤ 1 := by
    exact_mod_cast thickenedIndicator_le_one hδ s x
  have hgs {x : X} (hx : x ∈ s) : g x = 1 := by
    simp only [g, thickenedIndicator_one hδ s hx, NNReal.coe_one]
  have hgV {x : X} (hx : x ∉ V) : g x = 0 := by
    simp only [g, thickenedIndicator_zero hδ s
      (fun h => hx (hδV (thickening_subset_cthickening δ s h))), NNReal.coe_zero]
  let f : X → ℝ := fun x => c * g x
  have hfLip : LipschitzWith (‖c‖₊ * δ.toNNReal⁻¹) f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [f, Real.dist_eq, ← mul_sub, abs_mul, NNReal.coe_mul, coe_nnnorm,
      Real.norm_eq_abs]
    calc
      _ ≤ |c| * ((δ.toNNReal⁻¹ : ℝ≥0) * dist x y) :=
        mul_le_mul_of_nonneg_left (by simpa only [Real.dist_eq] using hgLip.dist_le_mul x y)
          (abs_nonneg c)
      _ = _ := (mul_assoc _ _ _).symm
  have hfSupport : HasCompactSupport f := by
    apply HasCompactSupport.intro (hs.cthickening (r := δ))
    intro x hx
    simp only [f, g, thickenedIndicator_zero hδ s
      (fun h => hx (thickening_subset_cthickening δ s h)), NNReal.coe_zero, mul_zero]
  have hfBound (x : X) : ‖f x‖ ≤ ‖c‖ := by
    change ‖c * g x‖ ≤ ‖c‖
    rw [norm_mul, Real.norm_eq_abs (g x), abs_of_nonneg (hg0 x)]
    exact mul_le_of_le_one_right (norm_nonneg c) (hg1 x)
  refine ⟨f, ⟨_, hfLip⟩, hfSupport,
    hfLip.continuous.memLp_of_hasCompactSupport hfSupport, ?_⟩
  apply (eLpNorm_mono (g := (V \ s).indicator fun _ => c)
    (hfLip.continuous.aestronglyMeasurable.sub
      (aestronglyMeasurable_const.indicator hs.measurableSet)) ?_).trans
    (hη _ hV.le (hVo.measurableSet.diff hs.measurableSet).nullMeasurableSet)
  intro x
  simp only [Pi.sub_apply]
  by_cases hxV : x ∈ V
  · by_cases hxs : x ∈ s
    · simp [f, hgs hxs, hxs]
    · rw [indicator_of_notMem hxs, sub_zero,
        indicator_of_mem (show x ∈ V \ s from ⟨hxV, hxs⟩)]
      exact hfBound x
  · have hxs : x ∉ s := fun h => hxV (hsV h)
    simp [f, hgV hxV, hxV, hxs]

 
theorem MemLp.exists_lipschitz_hasCompactSupport_eLpNorm_sub_le
    {f : X → ℝ} (hf : MemLp f 2 μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : X → ℝ, eLpNorm (f - g) 2 μ ≤ ε ∧
      (∃ C : ℝ≥0, LipschitzWith C g) ∧ MemLp g 2 μ ∧ HasCompactSupport g := by
  apply hf.induction_dense (by norm_num : (2 : ℝ≥0∞) ≠ ∞) _ _ _ hε
  rotate_left
  · rintro f g ⟨⟨Cf, hfL⟩, hfm, hfs⟩ ⟨⟨Cg, hgL⟩, hgm, hgs⟩
    exact ⟨⟨Cf + Cg, hfL.add hgL⟩, hfm.add hgm, hfs.add hgs⟩
  intro c t ht htμ ε hε
  obtain ⟨δ, hδ, hδadd⟩ := exists_Lp_half ℝ μ 2 hε
  obtain ⟨η, hη, hηbound⟩ :=
    exists_eLpNorm_indicator_le (by norm_num : (2 : ℝ≥0∞) ≠ ∞) c hδ.ne'
  obtain ⟨s, hst, hsc, hsClosed, hμs⟩ :=
    ht.exists_isCompact_isClosed_sdiff_lt htμ.ne (ENNReal.coe_pos.mpr hη).ne'
  have h1 : eLpNorm ((s.indicator fun _ => c) - t.indicator fun _ => c) 2 μ ≤ δ := by
    rw [← eLpNorm_neg, neg_sub, ← indicator_sdiff hst]
    exact hηbound _ hμs.le (ht.diff hsClosed.measurableSet).nullMeasurableSet
  obtain ⟨g, hgL, hgs, hgm, h2⟩ :=
    exists_lipschitz_eLpNorm_sub_indicator_le μ hsc c hδ.ne'
  refine ⟨g, ?_, hgL, hgm, hgs⟩
  simpa only [Pi.add_def, Pi.sub_def, sub_add_sub_cancel] using (hδadd _ _ h2 h1).le

end Density

section EnergyDensity
variable {X : Type u} [MetricSpace X]

 theorem localSlope_eq_zero_of_notMem_tsupport {f : X → ℝ} {x : X}
    (hx : x ∉ tsupport f) : localSlope f x = 0 := by
  obtain ⟨r, hr, hrS⟩ := Metric.isOpen_iff.mp isClosed_closure.isOpen_compl x hx
  have hfx : f x = 0 := image_eq_zero_of_notMem_tsupport hx
  apply le_antisymm _ bot_le
  unfold localSlope
  refine iInf_le_of_le r (iInf_le_of_le hr ?_)
  refine iSup_le fun y => iSup_le fun hy => iSup_le fun _ => ?_
  have hfy : f y = 0 := image_eq_zero_of_notMem_tsupport
    (hrS (by simpa only [Metric.mem_ball, dist_comm] using hy))
  simp [hfx, hfy]

variable [MeasurableSpace X] (μ : Measure X)

 theorem cheegerEnergy_le_slopeEnergy {f : X → ℝ} (hf : MemLp f 2 μ)
    {C : ℝ≥0} (hL : LipschitzWith C f) : cheegerEnergy μ f ≤ slopeEnergy μ f := by
  have ha : IsLipschitzApproximation μ f (fun _ => f) := by
    refine ⟨fun _ => ⟨hf, C, hL⟩, ?_⟩
    simp
  simpa only [liminf_const] using cheegerEnergy_le_liminf μ ha

variable [BorelSpace X] [IsFiniteMeasureOnCompacts μ]

 theorem slopeEnergy_lt_top_of_lipschitz_hasCompactSupport {f : X → ℝ}
    {C : ℝ≥0} (hf : LipschitzWith C f) (hs : HasCompactSupport f) :
    slopeEnergy μ f < ∞ := by
  have hbound : (∫⁻ x, localSlope f x ^ 2 ∂μ) ≤ (C : ℝ≥0∞) ^ 2 * μ (tsupport f) := by
    calc
      _ ≤ ∫⁻ x, (tsupport f).indicator (fun _ => (C : ℝ≥0∞) ^ 2) x ∂μ := by
        apply lintegral_mono
        intro x
        by_cases hx : x ∈ tsupport f
        · simp only [Set.indicator_of_mem hx]
          exact pow_le_pow_left₀ (by positivity) (localSlope_le_of_lipschitz hf x) 2
        · simp [Set.indicator_of_notMem hx, localSlope_eq_zero_of_notMem_tsupport hx]
      _ = _ := lintegral_indicator_const isClosed_closure.measurableSet _
  apply ENNReal.mul_lt_top (by norm_num : (2 : ℝ≥0∞)⁻¹ < ∞)
  exact hbound.trans_lt (ENNReal.mul_lt_top (by finiteness) (hs.measure_lt_top (μ := μ)))

 theorem cheegerEnergy_lt_top_of_lipschitz_hasCompactSupport {f : X → ℝ}
    {C : ℝ≥0} (hf : LipschitzWith C f) (hs : HasCompactSupport f) :
    cheegerEnergy μ f < ∞ :=
  (cheegerEnergy_le_slopeEnergy μ (hf.continuous.memLp_of_hasCompactSupport hs) hf).trans_lt
    (slopeEnergy_lt_top_of_lipschitz_hasCompactSupport μ hf hs)

end EnergyDensity

section DenseDomain
variable {X : Type u} [MetricSpace X] [ProperSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.Regular]
  (hQ : QuadraticCheegerEnergy μ)

 theorem SobolevSpace.toLp_denseRange : DenseRange (SobolevSpace.toLp μ hQ) := by
  rw [Metric.denseRange_iff]
  intro f ε hε
  obtain ⟨g, hgclose, ⟨C, hgL⟩, hgm, hgs⟩ :=
    MemLp.exists_lipschitz_hasCompactSupport_eLpNorm_sub_le μ (Lp.memLp f)
      (ε := ENNReal.ofReal (ε / 2))
      (by simpa only [ne_eq, ENNReal.ofReal_eq_zero, not_le] using half_pos hε)
  let gLp := hgm.toLp g
  have hgE : energyLp μ gLp < ∞ := by
    change cheegerEnergy μ gLp < ∞
    rw [cheegerEnergy_congr_ae μ hgm.coeFn_toLp]
    exact cheegerEnergy_lt_top_of_lipschitz_hasCompactSupport μ hgL hgs
  let u : SobolevSpace μ hQ := ⟨gLp, hgE.ne⟩
  refine ⟨u, ?_⟩
  have hclose : edist f (SobolevSpace.toLp μ hQ u) ≤ ENNReal.ofReal (ε / 2) := by
    rw [Lp.edist_def]
    change eLpNorm (fun x => f x - gLp x) 2 μ ≤ _
    have hae : (fun x => f x - gLp x) =ᵐ[μ] (fun x => f x - g x) :=
      hgm.coeFn_toLp.mono fun x hx => congrArg (fun t => f x - t) hx
    exact (eLpNorm_congr_ae hae).trans_le hgclose
  rw [edist_dist] at hclose
  have : dist f (SobolevSpace.toLp μ hQ u) ≤ ε / 2 := by
    exact (ENNReal.ofReal_le_ofReal_iff (half_pos hε).le).mp hclose
  have hd := lt_of_le_of_lt this (half_lt_self hε)
  simpa only [dist_comm] using hd

 theorem IsWeakLaplacian.unique {f : SobolevSpace μ hQ} {g h : Lp ℝ 2 μ}
    (hg : IsWeakLaplacian μ hQ f g) (hh : IsWeakLaplacian μ hQ f h) : g = h := by
  have hi : ∀ φ : SobolevSpace μ hQ,
      inner ℝ g (SobolevSpace.toLp μ hQ φ) = inner ℝ h (SobolevSpace.toLp μ hQ φ) := by
    intro φ
    have h1 := hg φ
    have h2 := hh φ
    linarith
  apply ext_inner_right ℝ
  have heq : (fun v : Lp ℝ 2 μ => inner ℝ g v) = (fun v => inner ℝ h v) :=
    (SobolevSpace.toLp_denseRange μ hQ).equalizer (by fun_prop) (by fun_prop) (funext hi)
  exact fun v => congrFun heq v

end DenseDomain

section ResolventMarkov
variable {X : Type u} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

 theorem energyLp_comp_contraction_le {φ : ℝ → ℝ} (hφ : LipschitzWith 1 φ)
    (hφ0 : φ 0 = 0) (f : Lp ℝ 2 μ) :
    energyLp μ (hφ.compLp hφ0 f) ≤ energyLp μ f := by
  unfold energyLp
  rw [cheegerEnergy_congr_ae μ (hφ.coeFn_compLp hφ0 f)]
  exact cheegerEnergy_comp_contraction μ hφ hφ0 f

 
noncomputable def SobolevSpace.compContraction {φ : ℝ → ℝ} (hφ : LipschitzWith 1 φ)
    (hφ0 : φ 0 = 0) (f : SobolevSpace μ hQ) : SobolevSpace μ hQ :=
  ⟨hφ.compLp hφ0 (SobolevSpace.toLp μ hQ f),
    (lt_of_le_of_lt (energyLp_comp_contraction_le μ hφ hφ0 _) f.2.lt_top).ne⟩

 theorem SobolevSpace.compContraction_toLp {φ : ℝ → ℝ} (hφ : LipschitzWith 1 φ)
    (hφ0 : φ 0 = 0) (f : SobolevSpace μ hQ) :
    SobolevSpace.toLp μ hQ (SobolevSpace.compContraction μ hQ hφ hφ0 f) =
      hφ.compLp hφ0 (SobolevSpace.toLp μ hQ f) := rfl

 theorem SobolevSpace.energy_compContraction_le {φ : ℝ → ℝ} (hφ : LipschitzWith 1 φ)
    (hφ0 : φ 0 = 0) (f : SobolevSpace μ hQ) :
    SobolevSpace.energy μ hQ (SobolevSpace.compContraction μ hQ hφ hφ0 f) ≤
      SobolevSpace.energy μ hQ f :=
  ENNReal.toReal_mono f.2 (energyLp_comp_contraction_le μ hφ hφ0 _)

 

 theorem SobolevSpace.resolvent_contraction_fixed {φ : ℝ → ℝ} (hφ : LipschitzWith 1 φ)
    (hφ0 : φ 0 = 0) (f : Lp ℝ 2 μ)
    (hf : (fun x => φ (f x)) =ᵐ[μ] f) :
    SobolevSpace.compContraction μ hQ hφ hφ0 (SobolevSpace.resolvent μ hQ f) =
      SobolevSpace.resolvent μ hQ f := by
  let r := SobolevSpace.resolvent μ hQ f
  let v := SobolevSpace.compContraction μ hQ hφ hφ0 r
  have hfFixed : hφ.compLp hφ0 f = f :=
    Lp.ext ((hφ.coeFn_compLp hφ0 f).trans hf)
  have hnorm : ‖SobolevSpace.toLp μ hQ v - f‖ ≤
      ‖SobolevSpace.toLp μ hQ r - f‖ := by
    change ‖hφ.compLp hφ0 (SobolevSpace.toLp μ hQ r) - f‖ ≤ _
    simpa only [hfFixed, NNReal.coe_one, one_mul] using
      hφ.norm_compLp_sub_le hφ0 (SobolevSpace.toLp μ hQ r) f
  have he := SobolevSpace.energy_compContraction_le μ hQ hφ hφ0 r
  have hv := SobolevSpace.resolvent_variational_identity μ hQ f v
  have hsq : ‖SobolevSpace.toLp μ hQ v - f‖ ^ 2 ≤
      ‖SobolevSpace.toLp μ hQ r - f‖ ^ 2 :=
    sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr hnorm
  have hzero : ‖v - r‖ ^ 2 = 0 := by
    change _ = _ + _ + ‖v - r‖ ^ 2 at hv
    have he' : SobolevSpace.energy μ hQ v ≤ SobolevSpace.energy μ hQ r := he
    nlinarith [sq_nonneg ‖v - r‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hzero))

 theorem SobolevSpace.resolvent_nonneg (f : Lp ℝ 2 μ) (hf : ∀ᵐ x ∂μ, 0 ≤ f x) :
    ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ (SobolevSpace.resolvent μ hQ f) x := by
  have hφ := Lp.lipschitzWith_pos_part
  have hφ0 : max (0 : ℝ) 0 = 0 := max_self _
  have hfix : (fun x => max (f x) 0) =ᵐ[μ] f :=
    hf.mono fun _ hx => max_eq_left hx
  have heq := congrArg (SobolevSpace.toLp μ hQ)
    (SobolevSpace.resolvent_contraction_fixed μ hQ hφ hφ0 f hfix)
  rw [SobolevSpace.compContraction_toLp] at heq
  have hae := hφ.coeFn_compLp hφ0
    (SobolevSpace.toLp μ hQ (SobolevSpace.resolvent μ hQ f))
  rw [heq] at hae
  exact hae.mono fun _ hx => by rw [hx]; exact le_max_right _ _

 theorem SobolevSpace.resolvent_le_const {c : ℝ} (hc : 0 ≤ c)
    (f : Lp ℝ 2 μ) (hf : ∀ᵐ x ∂μ, f x ≤ c) :
    ∀ᵐ x ∂μ, SobolevSpace.toLp μ hQ (SobolevSpace.resolvent μ hQ f) x ≤ c := by
  have hφ : LipschitzWith 1 (fun x : ℝ => min x c) := LipschitzWith.id.min_const c
  have hφ0 : min (0 : ℝ) c = 0 := min_eq_left hc
  have hfix : (fun x => min (f x) c) =ᵐ[μ] f := hf.mono fun _ hx => min_eq_left hx
  have heq := congrArg (SobolevSpace.toLp μ hQ)
    (SobolevSpace.resolvent_contraction_fixed μ hQ hφ hφ0 f hfix)
  rw [SobolevSpace.compContraction_toLp] at heq
  have hae := hφ.coeFn_compLp hφ0
    (SobolevSpace.toLp μ hQ (SobolevSpace.resolvent μ hQ f))
  rw [heq] at hae
  exact hae.mono fun _ hx => by rw [hx]; exact min_le_right _ _

end ResolventMarkov

variable {X : Type u} [MetricSpace X] [MeasurableSpace X] (μ : Measure X)
variable (hQ : QuadraticCheegerEnergy μ)

 
noncomputable def SobolevSpace.resolventForm (t : ℝ) :
    SobolevSpace μ hQ →L[ℝ] SobolevSpace μ hQ →L[ℝ] ℝ :=
  (innerSL ℝ).comp (t • ContinuousLinearMap.id ℝ (SobolevSpace μ hQ) +
    (1 - t) • (SobolevSpace.toLpCLM μ hQ).adjoint.comp (SobolevSpace.toLpCLM μ hQ))

 theorem SobolevSpace.resolventForm_apply (t : ℝ) (v w : SobolevSpace μ hQ) :
    SobolevSpace.resolventForm μ hQ t v w =
      inner ℝ (SobolevSpace.toLp μ hQ v) (SobolevSpace.toLp μ hQ w) +
        t * energyForm μ hQ v w := by
  simp only [SobolevSpace.resolventForm, ContinuousLinearMap.comp_apply,
    add_apply, smul_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply, inner_add_left, real_inner_smul_left,
    ContinuousLinearMap.adjoint_inner_left, SobolevSpace.toLpCLM,
    LinearMap.mkContinuous_apply, energyForm]
  ring

 theorem SobolevSpace.resolventForm_self (t : ℝ) (v : SobolevSpace μ hQ) :
    SobolevSpace.resolventForm μ hQ t v v =
      ‖SobolevSpace.toLp μ hQ v‖ ^ 2 + 2 * t * SobolevSpace.energy μ hQ v := by
  rw [SobolevSpace.resolventForm_apply, energyForm_self, real_inner_self_eq_norm_sq]
  ring

 theorem SobolevSpace.resolventForm_coercive {t : ℝ} (ht : 0 < t) :
    IsCoercive (SobolevSpace.resolventForm μ hQ t) := by
  refine ⟨min 1 t, lt_min zero_lt_one ht, fun v => ?_⟩
  rw [SobolevSpace.resolventForm_self]
  have hn := SobolevSpace.norm_sq μ hQ v
  unfold SobolevSpace.normSq at hn
  have h1 : min 1 t * ‖SobolevSpace.toLp μ hQ v‖ ^ 2 ≤
      ‖SobolevSpace.toLp μ hQ v‖ ^ 2 := by
    simpa using mul_le_mul_of_nonneg_right (min_le_left (1 : ℝ) t)
      (sq_nonneg ‖SobolevSpace.toLp μ hQ v‖)
  have h2 := mul_le_mul_of_nonneg_right (min_le_right (1 : ℝ) t)
    (SobolevSpace.energy_nonneg μ hQ v)
  calc
    min 1 t * ‖v‖ * ‖v‖ = min 1 t * ‖v‖ ^ 2 := by ring
    _ = min 1 t * ‖SobolevSpace.toLp μ hQ v‖ ^ 2 +
      2 * (min 1 t * SobolevSpace.energy μ hQ v) := by rw [hn]; ring
    _ ≤ ‖SobolevSpace.toLp μ hQ v‖ ^ 2 + 2 * t * SobolevSpace.energy μ hQ v := by
      linarith

 
noncomputable def SobolevSpace.resolventAt (t : ℝ) (ht : 0 < t) :
    Lp ℝ 2 μ →L[ℝ] SobolevSpace μ hQ :=
  (SobolevSpace.resolventForm_coercive μ hQ ht).continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp
    (SobolevSpace.resolvent μ hQ)

 theorem SobolevSpace.resolventAt_equation (t : ℝ) (ht : 0 < t)
    (f : Lp ℝ 2 μ) (φ : SobolevSpace μ hQ) :
    inner ℝ (SobolevSpace.toLp μ hQ (SobolevSpace.resolventAt μ hQ t ht f))
        (SobolevSpace.toLp μ hQ φ) +
      t * energyForm μ hQ (SobolevSpace.resolventAt μ hQ t ht f) φ =
        inner ℝ f (SobolevSpace.toLp μ hQ φ) := by
  rw [← SobolevSpace.resolventForm_apply]
  rw [← IsCoercive.continuousLinearEquivOfBilin_apply
    (SobolevSpace.resolventForm_coercive μ hQ ht)]
  simp only [SobolevSpace.resolventAt, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply,
    SobolevSpace.resolvent_inner]

 theorem SobolevSpace.resolventAt_unique {t : ℝ} (ht : 0 < t) {f : Lp ℝ 2 μ}
    {v : SobolevSpace μ hQ}
    (hv : ∀ φ : SobolevSpace μ hQ,
      inner ℝ (SobolevSpace.toLp μ hQ v) (SobolevSpace.toLp μ hQ φ) +
        t * energyForm μ hQ v φ = inner ℝ f (SobolevSpace.toLp μ hQ φ)) :
    v = SobolevSpace.resolventAt μ hQ t ht f := by
  apply (SobolevSpace.resolventForm_coercive μ hQ ht).continuousLinearEquivOfBilin.injective
  apply ext_inner_right ℝ
  intro φ
  rw [IsCoercive.continuousLinearEquivOfBilin_apply,
    IsCoercive.continuousLinearEquivOfBilin_apply, SobolevSpace.resolventForm_apply,
    SobolevSpace.resolventForm_apply, hv, SobolevSpace.resolventAt_equation]

 theorem SobolevSpace.resolventAt_weak_laplacian (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ) :
    IsWeakLaplacian μ hQ (SobolevSpace.resolventAt μ hQ t ht f)
      (t⁻¹ • (SobolevSpace.toLp μ hQ (SobolevSpace.resolventAt μ hQ t ht f) - f)) := by
  intro φ
  have h := SobolevSpace.resolventAt_equation μ hQ t ht f φ
  rw [real_inner_smul_left, inner_sub_left]
  apply (mul_left_cancel₀ ht.ne')
  field_simp
  linarith

 theorem SobolevSpace.resolventAt_variational_identity (t : ℝ) (ht : 0 < t)
    (f : Lp ℝ 2 μ) (v : SobolevSpace μ hQ) :
    ‖SobolevSpace.toLp μ hQ v - f‖ ^ 2 + 2 * t * SobolevSpace.energy μ hQ v =
      ‖SobolevSpace.toLp μ hQ (SobolevSpace.resolventAt μ hQ t ht f) - f‖ ^ 2 +
        2 * t * SobolevSpace.energy μ hQ (SobolevSpace.resolventAt μ hQ t ht f) +
        SobolevSpace.resolventForm μ hQ t
          (v - SobolevSpace.resolventAt μ hQ t ht f)
          (v - SobolevSpace.resolventAt μ hQ t ht f) := by
  let r := SobolevSpace.resolventAt μ hQ t ht f
  have hv := SobolevSpace.norm_sq μ hQ v
  have hr := SobolevSpace.norm_sq μ hQ r
  have hd := SobolevSpace.norm_sq μ hQ (v - r)
  have hi := SobolevSpace.resolventAt_equation μ hQ t ht f v
  have hi_self := SobolevSpace.resolventAt_equation μ hQ t ht f r
  change _ = _ + _ + SobolevSpace.resolventForm μ hQ t (v-r) (v-r)
  rw [SobolevSpace.resolventForm_self]
  simp only [SobolevSpace.normSq, map_sub, norm_sub_sq_real] at hv hr hd ⊢
  simp only [energyForm] at hi hi_self
  change inner ℝ (SobolevSpace.toLp μ hQ r) (SobolevSpace.toLp μ hQ v) +
    t * (inner ℝ r v - inner ℝ (SobolevSpace.toLp μ hQ r) (SobolevSpace.toLp μ hQ v)) = _ at hi
  change inner ℝ (SobolevSpace.toLp μ hQ r) (SobolevSpace.toLp μ hQ r) +
    t * (inner ℝ r r - inner ℝ (SobolevSpace.toLp μ hQ r) (SobolevSpace.toLp μ hQ r)) = _ at hi_self
  rw [real_inner_comm v r, real_inner_comm (SobolevSpace.toLp μ hQ v) (SobolevSpace.toLp μ hQ r),
    real_inner_comm (SobolevSpace.toLp μ hQ v) f] at hi
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    real_inner_comm (SobolevSpace.toLp μ hQ r) f] at hi_self
  have hv' := congrArg (t * ·) hv
  have hr' := congrArg (t * ·) hr
  have hd' := congrArg (t * ·) hd
  nlinarith [hv', hr', hd']

 theorem SobolevSpace.resolventAt_minimizes (t : ℝ) (ht : 0 < t)
    (f : Lp ℝ 2 μ) (v : SobolevSpace μ hQ) :
    ‖SobolevSpace.toLp μ hQ (SobolevSpace.resolventAt μ hQ t ht f) - f‖ ^ 2 +
        2 * t * SobolevSpace.energy μ hQ (SobolevSpace.resolventAt μ hQ t ht f) ≤
      ‖SobolevSpace.toLp μ hQ v - f‖ ^ 2 + 2 * t * SobolevSpace.energy μ hQ v := by
  rw [SobolevSpace.resolventAt_variational_identity μ hQ t ht f v,
    SobolevSpace.resolventForm_self]
  have h := SobolevSpace.energy_nonneg μ hQ (v - SobolevSpace.resolventAt μ hQ t ht f)
  exact le_add_of_nonneg_right (add_nonneg (sq_nonneg _)
    (mul_nonneg (mul_nonneg (by norm_num) ht.le) h))

 theorem SobolevSpace.resolventAt_norm_le (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ) :
    ‖SobolevSpace.toLp μ hQ (SobolevSpace.resolventAt μ hQ t ht f)‖ ≤ ‖f‖ := by
  let r := SobolevSpace.resolventAt μ hQ t ht f
  have h := SobolevSpace.resolventAt_equation μ hQ t ht f r
  change inner ℝ (SobolevSpace.toLp μ hQ r) (SobolevSpace.toLp μ hQ r) +
    t * energyForm μ hQ r r = _ at h
  rw [energyForm_self, real_inner_self_eq_norm_sq] at h
  have he := mul_nonneg ht.le (SobolevSpace.energy_nonneg μ hQ r)
  have hi := real_inner_le_norm f (SobolevSpace.toLp μ hQ r)
  have hn := norm_nonneg (SobolevSpace.toLp μ hQ r)
  change ‖SobolevSpace.toLp μ hQ r‖ ≤ _
  have hs : ‖SobolevSpace.toLp μ hQ r‖ ^ 2 ≤ ‖f‖ * ‖SobolevSpace.toLp μ hQ r‖ := by
    nlinarith only [h, hi, he]
  by_cases hz : ‖SobolevSpace.toLp μ hQ r‖ = 0
  · rw [hz]; exact norm_nonneg _
  · have hp := lt_of_le_of_ne hn (Ne.symm hz)
    exact le_of_mul_le_mul_right (by simpa only [pow_two] using hs) hp

end RegularPointCoordinates

end OAI
