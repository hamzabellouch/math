import Mathlib
import OAI.Analysis.RCDHeat.UniformBoundedApply

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: HeatH1, HeatFormDerivative, HeatJensen, CarrePositive, StrongEnergyDensity. -/



open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
namespace RegularPointCoordinates
universe u
open Metric
section HeatH1
variable {X : Type u} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
  [ProperSpace X] [BorelSpace X] [μ.Regular]

 theorem heatAt_of_nonpos (t : ℝ) (ht : t ≤ 0) : heatAt μ hQ t = 1 := by
  simp only [heatAt, max_eq_right ht, heatFlow_zero]

 
noncomputable def heatH1 (t : ℝ) (f : SobolevSpace μ hQ) : SobolevSpace μ hQ :=
  if ht : 0 < t then heatSobolev μ hQ t ht (SobolevSpace.toLp μ hQ f) else f

 theorem heatH1_toLp (t : ℝ) (f : SobolevSpace μ hQ) :
    SobolevSpace.toLp μ hQ (heatH1 μ hQ t f) = heatAt μ hQ t (SobolevSpace.toLp μ hQ f) := by
  by_cases ht : 0 < t
  · simp only [heatH1, dite_eq_left ht, heatSobolev_toLp]
  · simp only [heatH1, dite_eq_right ht, heatAt_of_nonpos μ hQ t (le_of_not_gt ht), one_apply_eq_self]

 theorem heatH1_energy_le (t : ℝ) (f : SobolevSpace μ hQ) :
    SobolevSpace.energy μ hQ (heatH1 μ hQ t f) ≤ SobolevSpace.energy μ hQ f := by
  unfold heatH1
  split_ifs with ht
  · exact heatSobolev_energy_le μ hQ t ht f
  · exact le_rfl

 theorem heatH1_norm_le (t : ℝ) (f : SobolevSpace μ hQ) : ‖heatH1 μ hQ t f‖ ≤ ‖f‖ := by
  have hn := (heatAt μ hQ t).le_of_opNorm_le (heatAt_norm_le μ hQ t) (SobolevSpace.toLp μ hQ f)
  simp only [one_mul] at hn
  have hE := heatH1_energy_le μ hQ t f
  have h1 := SobolevSpace.norm_sq μ hQ (heatH1 μ hQ t f)
  have h2 := SobolevSpace.norm_sq μ hQ f
  simp only [SobolevSpace.normSq, heatH1_toLp] at h1 h2
  nlinarith [norm_nonneg (heatAt μ hQ t (SobolevSpace.toLp μ hQ f)),
    norm_nonneg (heatH1 μ hQ t f), norm_nonneg f, sq_nonneg (‖f‖-‖heatH1 μ hQ t f‖),
    sq_nonneg (‖heatAt μ hQ t (SobolevSpace.toLp μ hQ f)‖ - ‖SobolevSpace.toLp μ hQ f‖)]

noncomputable def heatH1Map (t : ℝ) : SobolevSpace μ hQ →L[ℝ] SobolevSpace μ hQ :=
  LinearMap.mkContinuous
    { toFun := heatH1 μ hQ t
      map_add' := fun f g => by
        apply Subtype.ext
        change SobolevSpace.toLp μ hQ (heatH1 μ hQ t (f+g)) =
          SobolevSpace.toLp μ hQ (heatH1 μ hQ t f + heatH1 μ hQ t g)
        simp only [heatH1_toLp, map_add]
      map_smul' := fun c f => by
        apply Subtype.ext
        change SobolevSpace.toLp μ hQ (heatH1 μ hQ t (c • f)) =
          SobolevSpace.toLp μ hQ (c • heatH1 μ hQ t f)
        simp only [heatH1_toLp, map_smul] }
    1 (fun f => by
      change ‖heatH1 μ hQ t f‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using heatH1_norm_le μ hQ t f)

 theorem heatH1Map_norm_le (t : ℝ) : ‖heatH1Map μ hQ t‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun f => by
    change ‖heatH1 μ hQ t f‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using heatH1_norm_le μ hQ t f)

 theorem heatH1_core (t : ℝ) (f : Lp ℝ 2 μ) :
    heatH1 μ hQ t (SobolevSpace.resolventAt μ hQ 1 zero_lt_one f) = heatCore μ hQ t f := by
  apply Subtype.ext
  change SobolevSpace.toLp μ hQ _ = SobolevSpace.toLp μ hQ _
  rw [heatH1_toLp, heatCore_toLp]
  rfl

 theorem heatH1_continuous (f : SobolevSpace μ hQ) : Continuous (fun t => heatH1 μ hQ t f) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply tendsto_contraction_of_denseRange
    ((SobolevSpace.resolventAt_one_denseRange μ hQ).comp (SobolevSpace.toLp_denseRange μ hQ)
      (SobolevSpace.resolventAt μ hQ 1 zero_lt_one).continuous)
    (A := heatH1Map μ hQ) (B := heatH1Map μ hQ t)
    (heatH1Map_norm_le μ hQ) (heatH1Map_norm_le μ hQ t)
  intro g
  change Tendsto (fun s => heatH1 μ hQ s
    (SobolevSpace.resolventAt μ hQ 1 zero_lt_one (SobolevSpace.toLp μ hQ g))) (𝓝 t)
    (𝓝 (heatH1 μ hQ t (SobolevSpace.resolventAt μ hQ 1 zero_lt_one (SobolevSpace.toLp μ hQ g))))
  simp only [heatH1_core]
  exact (heatCore_continuous μ hQ _).continuousAt

 theorem heatH1_zero (f : SobolevSpace μ hQ) : heatH1 μ hQ 0 f = f := by
  simp only [heatH1, lt_self_iff_false, ↓reduceDIte]

 theorem heatH1_add (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (f : SobolevSpace μ hQ) :
    heatH1 μ hQ (s+t) f = heatH1 μ hQ s (heatH1 μ hQ t f) := by
  apply Subtype.ext
  change SobolevSpace.toLp μ hQ _ = SobolevSpace.toLp μ hQ _
  simp only [heatH1_toLp, heatAt_add μ hQ s t hs ht, mul_apply_eq_comp]

end HeatH1

section HeatFormDerivative
variable {X : Type u} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

 theorem energyForm_continuous : Continuous (fun fg : SobolevSpace μ hQ × SobolevSpace μ hQ =>
    energyForm μ hQ fg.1 fg.2) := by
  simp only [energyForm]
  exact (continuous_fst.inner continuous_snd).sub
    (((SobolevSpace.toLpCLM μ hQ).continuous.comp continuous_fst).inner
    ((SobolevSpace.toLpCLM μ hQ).continuous.comp continuous_snd))

variable [ProperSpace X] [BorelSpace X] [μ.Regular]

 theorem heatAt_inner_hasDerivAt (t : ℝ) (ht : 0 < t) (f g : SobolevSpace μ hQ) :
    HasDerivAt (fun s => inner ℝ (heatAt μ hQ s (SobolevSpace.toLp μ hQ f))
      (SobolevSpace.toLp μ hQ g)) (-energyForm μ hQ (heatH1 μ hQ t f) g) t := by
  have h := (heatAt_hasDerivAt μ hQ t ht (SobolevSpace.toLp μ hQ f)).inner ℝ
    (hasDerivAt_const t (SobolevSpace.toLp μ hQ g))
  simpa only [heatGeneratorAt_of_pos μ hQ t ht, inner_neg_left,
    heatH1, dite_eq_left ht, heatGenerator_form, inner_zero_right, zero_add] using h

 
 theorem heatAt_inner_hasDerivWithinAt_zero (f g : SobolevSpace μ hQ) :
    HasDerivWithinAt (fun s => inner ℝ (heatAt μ hQ s (SobolevSpace.toLp μ hQ f))
      (SobolevSpace.toLp μ hQ g)) (-energyForm μ hQ f g) (Ici 0) 0 := by
  apply hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioi 0)
  · intro t ht
    exact (heatAt_inner_hasDerivAt μ hQ t ht f g).differentiableAt.differentiableWithinAt
  · exact (((heatAt_continuous μ hQ _).inner continuous_const).continuousAt).continuousWithinAt
  · exact self_mem_nhdsWithin
  · have hc : Continuous (fun t => -energyForm μ hQ (heatH1 μ hQ t f) g) :=
      ((energyForm_continuous μ hQ).comp ((heatH1_continuous μ hQ f).prodMk
        continuous_const)).neg
    have hl : Tendsto (fun t => -energyForm μ hQ (heatH1 μ hQ t f) g)
        (𝓝[>] 0) (𝓝 (-energyForm μ hQ f g)) := by
      have hh := hc.tendsto (0 : ℝ)
      rw [heatH1_zero] at hh
      exact hh.mono_left nhdsWithin_le_nhds
    apply hl.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (heatAt_inner_hasDerivAt μ hQ t ht f g).deriv.symm

 theorem heatAt_form_limit (f g : SobolevSpace μ hQ) :
    Tendsto (fun t : ℝ => (inner ℝ (heatAt μ hQ t (SobolevSpace.toLp μ hQ f))
      (SobolevSpace.toLp μ hQ g) - inner ℝ (SobolevSpace.toLp μ hQ f)
      (SobolevSpace.toLp μ hQ g)) / t) (𝓝[>] 0) (𝓝 (-energyForm μ hQ f g)) := by
  have h := (heatAt_inner_hasDerivWithinAt_zero μ hQ f g).Ioi_of_Ici
  have ht := (hasDerivWithinAt_iff_tendsto_slope' (s := Ioi (0:ℝ)) (lt_irrefl (0:ℝ))).mp h
  simpa only [slope_fun_def_field, heatAt_zero, one_apply_eq_self, sub_zero] using ht

end HeatFormDerivative

section HeatJensen
variable {X : Type u} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
  [ProperSpace X] [BorelSpace X] [μ.Regular]

 theorem heatAt_nonneg (t : ℝ) (f : Lp ℝ 2 μ) (hf : 0 ≤ f) : 0 ≤ heatAt μ hQ t f :=
  heatFlow_nonneg μ hQ _ _ f hf

 theorem heatAt_le_const (t : ℝ) {c : ℝ} (hc : 0 ≤ c) (f : Lp ℝ 2 μ)
    (hf : ∀ᵐ x ∂μ, f x ≤ c) : ∀ᵐ x ∂μ, heatAt μ hQ t f x ≤ c :=
  heatFlow_le_const μ hQ _ _ hc f hf

 theorem heatAt_abs_le_const (t : ℝ) (C : ℝ≥0) (f : Lp ℝ 2 μ)
    (hf : ∀ᵐ x ∂μ, |f x| ≤ C) : ∀ᵐ x ∂μ, |heatAt μ hQ t f x| ≤ C := by
  have hp := heatAt_le_const μ hQ t C.coe_nonneg f (hf.mono fun _ h => (abs_le.mp h).2)
  have hm : ∀ᵐ x ∂μ, (-f) x ≤ C := by
    filter_upwards [hf, Lp.coeFn_neg f] with x hx hneg
    rw [hneg]
    exact neg_le.mp (abs_le.mp hx).1
  have h := heatAt_le_const μ hQ t C.coe_nonneg (-f) hm
  rw [map_neg] at h
  filter_upwards [hp, h, Lp.coeFn_neg (heatAt μ hQ t f)] with x hp hm heq
  rw [heq, Pi.neg_apply] at hm
  exact abs_le.mpr ⟨by linarith, hp⟩

 

 theorem heatAt_jensen_square (t : ℝ) (f : SobolevSpace μ hQ) (C : ℝ≥0)
    (hf : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ f x| ≤ C) :
    ∀ᵐ x ∂μ, (heatAt μ hQ t (SobolevSpace.toLp μ hQ f) x)^2 ≤
      heatAt μ hQ t (SobolevSpace.toLp μ hQ (SobolevSpace.square μ hQ f C)) x := by
  let fL := SobolevSpace.toLp μ hQ f
  let fS := SobolevSpace.toLp μ hQ (SobolevSpace.square μ hQ f C)
  have hq (q : ℚ) : ∀ᵐ x ∂μ, 2*(q:ℝ)*(heatAt μ hQ t fL x) - heatAt μ hQ t fS x ≤ (q:ℝ)^2 := by
    have hsrc : ∀ᵐ x ∂μ, ((2*(q:ℝ)) • fL - fS) x ≤ (q:ℝ)^2 := by
      filter_upwards [Lp.coeFn_sub ((2*(q:ℝ)) • fL) fS, Lp.coeFn_smul (2*(q:ℝ)) fL,
        SobolevSpace.square_coe μ hQ f C hf] with x hsub hsm hs
      change fS x = (fL x)^2 at hs
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hsub hsm
      rw [hsub, hsm, hs]
      nlinarith [sq_nonneg ((q:ℝ)-fL x)]
    have hout := heatAt_le_const μ hQ t (c := (q:ℝ)^2) (sq_nonneg (q:ℝ)) ((2*(q:ℝ)) • fL - fS) hsrc
    simp only [map_sub, map_smul] at hout
    filter_upwards [hout, Lp.coeFn_sub ((2*(q:ℝ)) • heatAt μ hQ t fL) (heatAt μ hQ t fS),
      Lp.coeFn_smul (2*(q:ℝ)) (heatAt μ hQ t fL)] with x hx hsub hsm
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hsub hsm
    simpa only [hsub, hsm] using hx
  have hforall : ∀ᵐ x ∂μ, ∀ q : ℚ, 2*(q:ℝ)*heatAt μ hQ t fL x - heatAt μ hQ t fS x ≤ (q:ℝ)^2 :=
    ae_all_iff.mpr hq
  filter_upwards [hforall] with x hx
  have hall (c : ℝ) : 2*c*heatAt μ hQ t fL x - heatAt μ hQ t fS x ≤ c^2 := by
    refine (Rat.denseRange_cast (𝕜 := ℝ)).induction_on c ?_ hx
    exact isClosed_le (by fun_prop) (by fun_prop)
  have h := hall (heatAt μ hQ t fL x)
  nlinarith

 theorem heatAt_square_increment_nonneg (t : ℝ) (f : SobolevSpace μ hQ) (C : ℝ≥0)
    (hf : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ f x| ≤ C) :
    ∀ᵐ x ∂μ, 0 ≤ heatAt μ hQ t (SobolevSpace.toLp μ hQ (SobolevSpace.square μ hQ f C)) x -
      2 * SobolevSpace.toLp μ hQ f x * heatAt μ hQ t (SobolevSpace.toLp μ hQ f) x +
      (SobolevSpace.toLp μ hQ f x)^2 := by
  filter_upwards [heatAt_jensen_square μ hQ t f C hf] with x hx
  nlinarith [sq_nonneg (heatAt μ hQ t (SobolevSpace.toLp μ hQ f) x - SobolevSpace.toLp μ hQ f x)]

end HeatJensen

section CarrePositive
variable {X : Type u} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

 omit [MetricSpace X] in
 theorem lp_inner_nonneg (f g : Lp ℝ 2 μ)
    (hf : ∀ᵐ x ∂μ, 0 ≤ f x) (hg : ∀ᵐ x ∂μ, 0 ≤ g x) : 0 ≤ inner ℝ f g := by
  rw [L2.inner_def]
  apply integral_nonneg_of_ae
  filter_upwards [hf, hg] with x hfx hgx
  rw [Real.inner_apply]
  exact mul_nonneg hfx hgx

 theorem SobolevSpace.inner_product_swap (f g h : SobolevSpace μ hQ) (C D E : ℝ≥0)
    (hf : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ f x| ≤ C)
    (hg : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ g x| ≤ D)
    (hh : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ h x| ≤ E) :
    inner ℝ (SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ f g C D))
      (SobolevSpace.toLp μ hQ h) = inner ℝ (SobolevSpace.toLp μ hQ g)
      (SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ f h C E)) := by
  simp only [L2.inner_def, Real.inner_apply]
  apply integral_congr_ae
  filter_upwards [SobolevSpace.product_coe μ hQ f g C D hf hg,
    SobolevSpace.product_coe μ hQ f h C E hf hh] with x hfg hfh
  rw [hfg, hfh]
  ring

 theorem SobolevSpace.inner_square_product (f g : SobolevSpace μ hQ) (C D : ℝ≥0)
    (hf : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ f x| ≤ C)
    (hg : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ g x| ≤ D) :
    inner ℝ (SobolevSpace.toLp μ hQ (SobolevSpace.square μ hQ f C))
      (SobolevSpace.toLp μ hQ g) = inner ℝ (SobolevSpace.toLp μ hQ f)
      (SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ f g C D)) := by
  simp only [L2.inner_def, Real.inner_apply]
  apply integral_congr_ae
  filter_upwards [SobolevSpace.square_coe μ hQ f C hf,
    SobolevSpace.product_coe μ hQ f g C D hf hg] with x hsq hprod
  rw [hsq, hprod]
  ring

 

noncomputable def carrePair (f φ : SobolevSpace μ hQ) (C D : ℝ≥0) : ℝ :=
  energyForm μ hQ f (SobolevSpace.product μ hQ f φ C D) -
    (1/2:ℝ) * energyForm μ hQ (SobolevSpace.square μ hQ f C) φ

variable [ProperSpace X] [BorelSpace X] [μ.Regular]

 theorem heatH1_abs_le_const (t : ℝ) (f : SobolevSpace μ hQ) (C : ℝ≥0)
    (hf : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ f x| ≤ C) :
    ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (heatH1 μ hQ t f) x| ≤ C := by
  rw [heatH1_toLp]
  exact heatAt_abs_le_const μ hQ t C _ hf

 theorem heatAt_carre_increment_nonneg (t : ℝ) (f φ : SobolevSpace μ hQ) (C D : ℝ≥0)
    (hf : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ f x| ≤ C)
    (hφ : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ φ x| ≤ D)
    (hφ0 : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ φ x) :
    0 ≤ inner ℝ (heatAt μ hQ t (SobolevSpace.toLp μ hQ (SobolevSpace.square μ hQ f C)))
        (SobolevSpace.toLp μ hQ φ) -
      2 * inner ℝ (heatAt μ hQ t (SobolevSpace.toLp μ hQ f))
        (SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ f φ C D)) +
      inner ℝ (SobolevSpace.toLp μ hQ (SobolevSpace.square μ hQ f C))
        (SobolevSpace.toLp μ hQ φ) := by
  let q : SobolevSpace μ hQ := heatH1 μ hQ t (SobolevSpace.square μ hQ f C) -
    (2:ℝ) • SobolevSpace.product μ hQ f (heatH1 μ hQ t f) C C + SobolevSpace.square μ hQ f C
  have hq : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ q x := by
    dsimp only [q]
    simp only [map_add, map_sub, map_smul]
    filter_upwards [Lp.coeFn_add
      (SobolevSpace.toLp μ hQ (heatH1 μ hQ t (SobolevSpace.square μ hQ f C)) -
        (2:ℝ) • SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ f (heatH1 μ hQ t f) C C))
      (SobolevSpace.toLp μ hQ (SobolevSpace.square μ hQ f C)),
      Lp.coeFn_sub (SobolevSpace.toLp μ hQ (heatH1 μ hQ t (SobolevSpace.square μ hQ f C)))
        ((2:ℝ) • SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ f (heatH1 μ hQ t f) C C)),
      Lp.coeFn_smul (2:ℝ) (SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ f (heatH1 μ hQ t f) C C)),
      SobolevSpace.product_coe μ hQ f (heatH1 μ hQ t f) C C hf
        (heatH1_abs_le_const μ hQ t f C hf), SobolevSpace.square_coe μ hQ f C hf,
      heatAt_square_increment_nonneg μ hQ t f C hf] with x hadd hsub hsm hprod hsq hnon
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, heatH1_toLp] at *
    rw [hadd, hsub, hsm, hprod, hsq]
    nlinarith [hnon]
  have hi := lp_inner_nonneg μ (SobolevSpace.toLp μ hQ q) (SobolevSpace.toLp μ hQ φ) hq hφ0
  dsimp only [q] at hi
  simp only [map_add, map_sub, map_smul, inner_add_left, inner_sub_left, real_inner_smul_left] at hi
  rw [SobolevSpace.inner_product_swap μ hQ f (heatH1 μ hQ t f) φ C C D hf
    (heatH1_abs_le_const μ hQ t f C hf) hφ] at hi
  simpa only [heatH1_toLp] using hi

 

 theorem carrePair_nonneg (f φ : SobolevSpace μ hQ) (C D : ℝ≥0)
    (hf : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ f x| ≤ C)
    (hφ : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ φ x| ≤ D)
    (hφ0 : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ φ x) :
    0 ≤ carrePair μ hQ f φ C D := by
  have hl := (heatAt_form_limit μ hQ (SobolevSpace.square μ hQ f C) φ).sub
    ((heatAt_form_limit μ hQ f (SobolevSpace.product μ hQ f φ C D)).const_mul 2)
  have hpos : 0 ≤ -energyForm μ hQ (SobolevSpace.square μ hQ f C) φ -
      2 * (-energyForm μ hQ f (SobolevSpace.product μ hQ f φ C D)) := by
    apply ge_of_tendsto hl
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hi := heatAt_carre_increment_nonneg μ hQ t f φ C D hf hφ hφ0
    have he := SobolevSpace.inner_square_product μ hQ f φ C D hf hφ
    have hn := div_nonneg hi ht.le
    rw [he] at hn ⊢
    convert hn using 1
    ring
  dsimp only [carrePair]
  linarith

end CarrePositive

variable {X : Type u} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

 

theorem SobolevSpace.eventually_energy_gt {f : SobolevSpace μ hQ}
    {fs : ℕ → SobolevSpace μ hQ}
    (hc : Tendsto (fun i => SobolevSpace.toLp μ hQ (fs i)) atTop
      (𝓝 (SobolevSpace.toLp μ hQ f))) {a : ℝ}
    (ha : a < SobolevSpace.energy μ hQ f) :
    ∀ᶠ i in atTop, a < SobolevSpace.energy μ hQ (fs i) := by
  by_cases ha0 : 0 ≤ a
  · have hlt : ENNReal.ofReal a < energyLp μ (SobolevSpace.toLp μ hQ f) :=
      (ENNReal.ofReal_lt_iff_lt_toReal ha0 f.property).mpr ha
    have hev := eventually_lt_of_lt_liminf
      (hlt.trans_le (energyLp_le_liminf μ hc)) (by isBoundedDefault)
    exact hev.mono fun i hi =>
      (ENNReal.ofReal_lt_iff_lt_toReal ha0 (fs i).property).mp hi
  · exact Eventually.of_forall fun i => (lt_of_not_ge ha0).trans_le
      (SobolevSpace.energy_nonneg μ hQ (fs i))

 

theorem SobolevSpace.tendsto_of_toLp_tendsto_energy_le {f : SobolevSpace μ hQ}
    {fs : ℕ → SobolevSpace μ hQ}
    (hc : Tendsto (fun i => SobolevSpace.toLp μ hQ (fs i)) atTop
      (𝓝 (SobolevSpace.toLp μ hQ f)))
    (he : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop,
      SobolevSpace.energy μ hQ (fs i) ≤ SobolevSpace.energy μ hQ f + ε) :
    Tendsto fs atTop (𝓝 f) := by
  have hm : Tendsto (fun i => SobolevSpace.toLp μ hQ ((1 / 2 : ℝ) • (fs i + f)))
      atTop (𝓝 (SobolevSpace.toLp μ hQ f)) := by
    have h := (hc.add (tendsto_const_nhds (x := SobolevSpace.toLp μ hQ f))).const_smul (1 / 2 : ℝ)
    convert h using 1
    · ext i; simp
    · norm_num [smul_add, ← add_smul]
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hεs : 0 < ε ^ 2 / 32 := by positivity
  have hem := SobolevSpace.eventually_energy_gt μ hQ hm
    (a := SobolevSpace.energy μ hQ f - ε ^ 2 / 32) (by linarith)
  have hn : ∀ᶠ i in atTop,
      ‖SobolevSpace.toLp μ hQ (fs i - f)‖ < ε / 2 := by
    have h := (hc.sub (tendsto_const_nhds (x := SobolevSpace.toLp μ hQ f))).norm
    simp only [sub_self, norm_zero] at h
    simpa only [map_sub] using h.eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [hem, he (ε ^ 2 / 32) hεs, hn] with i hi hie hin
  have hp := SobolevSpace.energy_parallelogram μ hQ (fs i) f
  rw [SobolevSpace.energy_smul] at hi
  have hediff : SobolevSpace.energy μ hQ (fs i - f) < 6 * (ε ^ 2 / 32) := by
    nlinarith
  have hnorm := SobolevSpace.norm_sq μ hQ (fs i - f)
  unfold SobolevSpace.normSq at hnorm
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (fs i - f),
    norm_nonneg (SobolevSpace.toLp μ hQ (fs i - f))]

 

theorem SobolevSpace.exists_strong_lipschitz_recovery (f : SobolevSpace μ hQ) :
    ∃ (fs : ℕ → SobolevSpace μ hQ) (gs : ℕ → X → ℝ),
      Tendsto fs atTop (𝓝 f) ∧
      ∀ i, (∃ C : ℝ≥0, LipschitzWith C (gs i)) ∧
        SobolevSpace.toLp μ hQ (fs i) =ᵐ[μ] gs i ∧
        slopeEnergy μ (gs i) <
          ENNReal.ofReal (SobolevSpace.energy μ hQ f + (1 / 2 : ℝ) ^ i) := by
  let δ : ℕ → ℝ := fun i => (1 / 2 : ℝ) ^ i
  have hδ : ∀ i, 0 < δ i := fun i => pow_pos (by norm_num) i
  have hδt : Tendsto δ atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hf : ∀ i, energyLp μ (SobolevSpace.toLp μ hQ f) <
      ENNReal.ofReal (SobolevSpace.energy μ hQ f + δ i) := by
    intro i
    apply (ENNReal.lt_ofReal_iff_toReal_lt
      (show energyLp μ (SobolevSpace.toLp μ hQ f) ≠ ∞ from f.property)).mpr
    change SobolevSpace.energy μ hQ f < SobolevSpace.energy μ hQ f + δ i
    linarith [hδ i]
  choose gs hm hl hd he using fun i =>
    exists_lipschitzApproximation_of_energy_lt μ (hf i)
      (ENNReal.ofReal_pos.mpr (hδ i))
  have hfin (i : ℕ) : energyLp μ ((hm i).toLp (gs i)) ≠ ∞ := by
    change cheegerEnergy μ ((hm i).toLp (gs i)) ≠ ∞
    rw [cheegerEnergy_congr_ae μ (hm i).coeFn_toLp]
    obtain ⟨C, hC⟩ := hl i
    exact ((cheegerEnergy_le_slopeEnergy μ (hm i) hC).trans_lt
      ((he i).trans_le le_top)).ne
  let fs : ℕ → SobolevSpace μ hQ := fun i => ⟨(hm i).toLp (gs i), hfin i⟩
  have hfae (i : ℕ) : SobolevSpace.toLp μ hQ (fs i) =ᵐ[μ] gs i :=
    (hm i).coeFn_toLp
  have hdist (i : ℕ) : dist (SobolevSpace.toLp μ hQ (fs i))
      (SobolevSpace.toLp μ hQ f) < δ i := by
    have hed : edist (SobolevSpace.toLp μ hQ (fs i))
        (SobolevSpace.toLp μ hQ f) < ENNReal.ofReal (δ i) := by
      rw [Lp.edist_def]
      change eLpNorm (fun x => SobolevSpace.toLp μ hQ (fs i) x -
        SobolevSpace.toLp μ hQ f x) 2 μ < _
      rw [eLpNorm_congr_ae ((hfae i).mono fun x hx =>
        congrArg (fun z => z - SobolevSpace.toLp μ hQ f x) hx)]
      exact hd i
    rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff (hδ i)] at hed
    exact hed
  have hLp : Tendsto (fun i => SobolevSpace.toLp μ hQ (fs i)) atTop
      (𝓝 (SobolevSpace.toLp μ hQ f)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hδt.eventually (gt_mem_nhds hε)] with i hi
    exact (hdist i).trans hi
  have hEn (i : ℕ) : SobolevSpace.energy μ hQ (fs i) ≤
      SobolevSpace.energy μ hQ f + δ i := by
    apply ENNReal.toReal_le_of_le_ofReal
      (add_nonneg (SobolevSpace.energy_nonneg μ hQ f) (hδ i).le)
    change cheegerEnergy μ (SobolevSpace.toLp μ hQ (fs i)) ≤ _
    rw [cheegerEnergy_congr_ae μ (hfae i)]
    obtain ⟨C, hC⟩ := hl i
    exact (cheegerEnergy_le_slopeEnergy μ (hm i) hC).trans (he i).le
  refine ⟨fs, gs, SobolevSpace.tendsto_of_toLp_tendsto_energy_le μ hQ hLp ?_,
    fun i => ⟨hl i, hfae i, he i⟩⟩
  intro ε hε
  filter_upwards [hδt.eventually (gt_mem_nhds hε)] with i hi
  linarith [hEn i]

end RegularPointCoordinates

end OAI
