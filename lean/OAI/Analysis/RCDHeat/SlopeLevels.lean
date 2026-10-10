import Mathlib
import OAI.Analysis.RCDHeat.RelaxedChain

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: SlopeLevels, StrongLocality, ScalarInverse, ChainEquality, ExactChain. -/



open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
namespace RegularPointCoordinates
universe u
open Metric
open Metric
section SlopeLevels
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X)

 theorem slopeFlatten_tendsto {εs : ℕ → ℝ} (hε : Tendsto εs atTop (𝓝 0)) (a : ℝ) :
    Tendsto (fun i => slopeFlatten (εs i) a) atTop (𝓝 a) := by
  have h := (slopeFlattenFactor_tendsto hε a).mul_const a
  simp_rw [← slopeFlatten_eq_factor] at h
  convert h using 1
  split_ifs with ha <;> simp [ha]

 
 theorem IsRelaxedSlope.cut_level {f G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ f G) (c : ℝ) :
    ∃ H : Lp ℝ 2 μ, IsRelaxedSlope μ f H ∧
      ∀ᵐ x ∂μ, H x = if f x = c then 0 else G x := by
  let ε (i : ℕ) : ℝ := (1 / 2 : ℝ) ^ i
  have hε (i : ℕ) : 0 < ε i := pow_pos (by norm_num) i
  have heps : Tendsto ε atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  let φs (i : ℕ) (a : ℝ) := slopeFlatten (ε i) (a-c) - slopeFlatten (ε i) (-c)
  let ψs (i : ℕ) (a : ℝ) := slopeFlattenDeriv (ε i) (a-c)
  have hφs (i : ℕ) : LipschitzWith 3 (φs i) := by
    have h := ((slopeFlatten_lipschitz (hε i)).comp
      (LipschitzWith.id.sub (LipschitzWith.const c))).sub
        (LipschitzWith.const (slopeFlatten (ε i) (-c)))
    convert h using 1 <;> first | rfl | simp only [add_zero, mul_one]
  have hφz (i : ℕ) : φs i 0 = 0 := by simp [φs]
  have hψs (i : ℕ) : Continuous (ψs i) :=
    (slopeFlattenDeriv_continuous (hε i)).comp (continuous_id.sub continuous_const)
  have hds (i : ℕ) (a : ℝ) : HasDerivAt (φs i) (ψs i a) a := by
    have h := ((slopeFlatten_deriv (hε i) (a-c)).comp a
      ((hasDerivAt_id a).sub_const c)).sub_const (slopeFlatten (ε i) (-c))
    convert h using 1 <;> first | rfl | simp [ψs, mul_one]
  have hdb (i : ℕ) (a : ℝ) : |ψs i a| ≤ (3 : ℝ≥0) := by
    rw [abs_of_nonneg (slopeFlattenDeriv_nonneg (hε i) (a-c))]
    exact slopeFlattenDeriv_le (hε i) (a-c)
  let η (x : X) : ℝ := if f x = c then 0 else 1
  have hη : Measurable η := measurable_const.ite
    ((Lp.stronglyMeasurable f).measurable (measurableSet_singleton c)) measurable_const
  have hηb (x : X) : |η x| ≤ (3 : ℝ≥0) := by dsimp [η]; split_ifs <;> norm_num
  let θ := boundedMultiplier μ η hη 3 hηb
  let H := lpMultiplier μ θ G
  have hH : ∀ᵐ x ∂μ, H x = if f x = c then 0 else G x := by
    filter_upwards [lpMultiplier_coe μ θ G, boundedMultiplier_coe μ η hη 3 hηb] with x hx ht
    change lpMultiplier μ θ G x = _
    rw [hx, show θ x = η x from ht]
    dsimp [η]; split_ifs <;> simp
  refine ⟨H, ?_, hH⟩
  let us (i : ℕ) := (hφs i).compLp (hφz i) f
  let ηs (i : ℕ) (x : X) : ℝ := |ψs i (f x)|
  have hs (i : ℕ) : Measurable (ηs i) :=
    ((hψs i).measurable.comp (Lp.stronglyMeasurable f).measurable).abs
  have hsb (i : ℕ) (x : X) : |ηs i x| ≤ (3 : ℝ≥0) := by
    simpa only [ηs, abs_abs] using hdb i (f x)
  let Gs (i : ℕ) := lpMultiplier μ (boundedMultiplier μ (ηs i) (hs i) 3 (hsb i)) G
  have hrel (i : ℕ) : IsRelaxedSlope μ (us i) (Gs i) :=
    hG.comp_C1 μ (hφs i) (hφz i) (hψs i) (hds i) 3 (hdb i)
  have hGt : Tendsto Gs atTop (𝓝 H) := by
    apply lpMultiplier_tendsto_of_ae μ G ηs η hs hη 3 hsb hηb
    apply Eventually.of_forall
    intro x
    have ht := (slopeFlattenDeriv_tendsto heps (f x-c)).abs
    convert ht using 1
    dsimp [η]
    by_cases hfx : f x = c
    · simp only [hfx, sub_self, ite_true, abs_zero]
    · simp only [hfx, sub_ne_zero.mpr hfx, ite_false, abs_one]
  have hut : Tendsto us atTop (𝓝 f) := by
    have hi : LipschitzWith 3 (id : ℝ → ℝ) := LipschitzWith.id.weaken (by norm_num)
    have ht := compLp_tendsto_of_pointwise μ hφs hi hφz (rfl : id (0 : ℝ) = 0)
      (fun a => by
        have hp := (slopeFlatten_tendsto heps (a-c)).sub (slopeFlatten_tendsto heps (-c))
        convert hp using 1; first | rfl | simp [id, sub_neg_eq_add, sub_add_cancel]) f
    have he : hi.compLp rfl f = f := by
      apply Lp.ext
      exact hi.coeFn_compLp rfl f
    rwa [he] at ht
  exact IsRelaxedSlope.of_tendsto μ hrel hut hGt

variable [ProperSpace X] (hQ : QuadraticCheegerEnergy μ)

 theorem SobolevSpace.minimalSlope_zero_on_level (f : SobolevSpace μ hQ) (c : ℝ) :
    ∀ᵐ x ∂μ, SobolevSpace.toLp μ hQ f x = c → SobolevSpace.minimalSlope μ hQ f x = 0 := by
  obtain ⟨H, hH, hHa⟩ := (SobolevSpace.minimalSlope_isRelaxed μ hQ f).cut_level μ c
  have hle := (Lp.coeFn_le _ _).mpr (SobolevSpace.minimalSlope_le μ hQ f hH)
  have hnon := Lp.coeFn_nonneg _ |>.mpr (SobolevSpace.minimalSlope_nonneg μ hQ f)
  filter_upwards [hle, hnon, hHa] with x hx hn he
  intro hz
  rw [hz, ite_eq_left rfl] at he
  exact le_antisymm (he ▸ hx) hn

end SlopeLevels

section StrongLocality
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

 theorem SobolevSpace.minimalSlope_smul_nonneg (f : SobolevSpace μ hQ) {c : ℝ} (hc : 0 ≤ c) :
    SobolevSpace.minimalSlope μ hQ (c • f) = c • SobolevSpace.minimalSlope μ hQ f := by
  apply IsRelaxedSlope.unique_minimizer μ (SobolevSpace.minimalSlope_isRelaxed μ hQ (c • f))
  · simpa only [map_smul] using (SobolevSpace.minimalSlope_isRelaxed μ hQ f).const_mul μ hc
  · exact SobolevSpace.minimalSlope_norm_sq μ hQ (c • f)
  · rw [norm_smul, mul_pow, SobolevSpace.minimalSlope_norm_sq]
    change ‖c‖ ^ 2 * (2 * SobolevSpace.energy μ hQ f) = 2 * SobolevSpace.energy μ hQ (c • f)
    rw [SobolevSpace.energy_smul, Real.norm_eq_abs, sq_abs]
    ring

 theorem SobolevSpace.minimalSlope_smul (f : SobolevSpace μ hQ) (c : ℝ) :
    SobolevSpace.minimalSlope μ hQ (c • f) = |c| • SobolevSpace.minimalSlope μ hQ f := by
  rcases le_total 0 c with hc | hc
  · rw [abs_of_nonneg hc, SobolevSpace.minimalSlope_smul_nonneg μ hQ f hc]
  · rw [abs_of_nonpos hc, ← neg_neg (c • f), ← neg_smul, SobolevSpace.minimalSlope_neg,
      SobolevSpace.minimalSlope_smul_nonneg μ hQ f (neg_nonneg.mpr hc)]

variable [ProperSpace X]

 theorem energyForm_le_slope_inner (f g : SobolevSpace μ hQ) :
    energyForm μ hQ f g ≤ inner ℝ (SobolevSpace.minimalSlope μ hQ f)
      (SobolevSpace.minimalSlope μ hQ g) := by
  have hn : ‖SobolevSpace.minimalSlope μ hQ (f+g)‖ ≤
      ‖SobolevSpace.minimalSlope μ hQ f + SobolevSpace.minimalSlope μ hQ g‖ :=
    norm_le_norm_of_abs_le_abs (by
      rw [abs_of_nonneg (SobolevSpace.minimalSlope_nonneg μ hQ (f+g)),
        abs_of_nonneg (add_nonneg (SobolevSpace.minimalSlope_nonneg μ hQ f)
          (SobolevSpace.minimalSlope_nonneg μ hQ g))]
      exact SobolevSpace.minimalSlope_add_le μ hQ f g)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [norm_add_sq_real, SobolevSpace.minimalSlope_norm_sq,
    SobolevSpace.minimalSlope_norm_sq, SobolevSpace.minimalSlope_norm_sq] at hs
  have he : 2 * SobolevSpace.energy μ hQ (f+g) =
      2 * SobolevSpace.energy μ hQ f + 2 * energyForm μ hQ f g + 2 * SobolevSpace.energy μ hQ g := by
    rw [← energyForm_self, energyForm_add_left, energyForm_comm μ hQ f (f+g),
      energyForm_add_left, energyForm_comm μ hQ g (f+g), energyForm_add_left,
      energyForm_self, energyForm_self, energyForm_comm μ hQ g f]
    ring
  rw [he] at hs
  linarith

 
 theorem energyForm_abs_le_slope_inner (f g : SobolevSpace μ hQ) :
    |energyForm μ hQ f g| ≤ inner ℝ (SobolevSpace.minimalSlope μ hQ f)
      (SobolevSpace.minimalSlope μ hQ g) := by
  apply abs_le'.mpr
  refine ⟨energyForm_le_slope_inner μ hQ f g, ?_⟩
  have h := energyForm_le_slope_inner μ hQ (-f) g
  rw [SobolevSpace.minimalSlope_neg] at h
  simpa only [energyForm, map_neg, inner_neg_left, neg_sub_neg, neg_sub] using h

 

 theorem energyForm_strongly_local (f g : SobolevSpace μ hQ) (c : ℝ)
    (hfg : ∀ᵐ x ∂μ, SobolevSpace.toLp μ hQ g x ≠ 0 → SobolevSpace.toLp μ hQ f x = c) :
    energyForm μ hQ f g = 0 := by
  have hi : inner ℝ (SobolevSpace.minimalSlope μ hQ f) (SobolevSpace.minimalSlope μ hQ g) = 0 := by
    rw [L2.inner_def]
    apply integral_eq_zero_of_ae
    filter_upwards [hfg, SobolevSpace.minimalSlope_zero_on_level μ hQ f c,
      SobolevSpace.minimalSlope_zero_on_zero μ hQ g] with x hx hf hg
    rw [Real.inner_apply]
    by_cases hz : SobolevSpace.toLp μ hQ g x = 0
    · simp only [hg hz, mul_zero, Pi.zero_apply]
    · simp only [hf (hx hz), zero_mul, Pi.zero_apply]
  have h := energyForm_abs_le_slope_inner μ hQ f g
  rw [hi] at h
  exact abs_nonpos_iff.mp h

end StrongLocality

section ScalarInverse

 

 theorem scalar_small_perturbation_inverse {η κ : ℝ → ℝ}
    (hη : LipschitzWith (1/2) η) (hη0 : η 0 = 0)
    (hκ : Continuous κ) (hd : ∀ a, HasDerivAt η (κ a) a)
    (hκb : ∀ a, |κ a| ≤ 1/2) :
    ∃ θ χ : ℝ → ℝ, LipschitzWith 2 θ ∧ θ 0 = 0 ∧ Continuous χ ∧
      (∀ a, HasDerivAt θ (χ a) a) ∧ (∀ a, |χ a| ≤ 2) ∧
      Function.LeftInverse θ (fun a => a + η a) := by
  have hc (b : ℝ) : ContractingWith (1/2) (fun a => b - η a) := by
    refine ⟨by norm_num, ?_⟩
    have hh := (LipschitzWith.const b).sub hη
    convert hh using 1
    first | rfl | norm_num
  let θ (b : ℝ) := (hc b).fixedPoint (fun a => b - η a)
  have hr (b : ℝ) : θ b + η (θ b) = b := by
    have h := (hc b).fixedPoint_isFixedPt
    change b - η (θ b) = θ b at h
    linarith
  have hθ : LipschitzWith 2 θ := by
    apply LipschitzWith.of_dist_le_mul
    intro b c
    have hh : |θ b-θ c| ≤ |b-c| + |η (θ b)-η (θ c)| := by
      have he : θ b-θ c = (b-c) - (η (θ b)-η (θ c)) := by linarith [hr b, hr c]
      rw [he]
      exact abs_sub _ _
    have hl := hη.dist_le_mul (θ b) (θ c)
    simp only [Real.dist_eq, NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_one] at hl ⊢
    linarith
  have hleft : Function.LeftInverse θ (fun a => a+η a) := by
    intro a
    have h : Function.IsFixedPt (fun b => a+η a-η b) a := by dsimp [Function.IsFixedPt]; ring
    exact ((hc (a+η a)).fixedPoint_unique h).symm
  have hθ0 : θ 0 = 0 := by simpa only [hη0, zero_add] using hleft 0
  have hpos (a : ℝ) : 0 < 1 + κ a := by
    have h := (abs_le.mp (hκb a)).1
    linarith
  let χ (a : ℝ) := (1 + κ (θ a))⁻¹
  have hχ : Continuous χ := (continuous_const.add (hκ.comp hθ.continuous)).inv₀
    (fun a => (hpos (θ a)).ne')
  refine ⟨θ, χ, hθ, hθ0, hχ, ?_, ?_, hleft⟩
  · intro a
    have hf : HasDerivAt (fun a => a+η a) (1+κ (θ a)) (θ a) :=
      (hasDerivAt_id (θ a)).add (hd (θ a))
    exact hf.of_local_left_inverse hθ.continuous.continuousAt (hpos (θ a)).ne'
      (Eventually.of_forall hr)
  · intro a
    dsimp [χ]
    rw [abs_of_pos (inv_pos.mpr (hpos (θ a)))]
    apply (inv_le_iff_one_le_mul₀ (hpos (θ a))).mpr
    have h := (abs_le.mp (hκb (θ a))).1
    linarith

end ScalarInverse

section ChainEquality
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

 theorem SobolevSpace.minimalSlope_comp_C1_le (f : SobolevSpace μ hQ)
    {φ ψ : ℝ → ℝ} {C : ℝ≥0} (hφ : LipschitzWith C φ) (hφ0 : φ 0 = 0)
    (hψ : Continuous ψ) (hd : ∀ a, HasDerivAt φ (ψ a) a)
    (B : ℝ≥0) (hB : ∀ a, |ψ a| ≤ B) :
    ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ (SobolevSpace.comp μ hQ hφ hφ0 f) x ≤
      |ψ (SobolevSpace.toLp μ hQ f x)| * SobolevSpace.minimalSlope μ hQ f x := by
  let η (x : X) := |ψ (SobolevSpace.toLp μ hQ f x)|
  have hη : Measurable η :=
    (hψ.measurable.comp (Lp.stronglyMeasurable (SobolevSpace.toLp μ hQ f)).measurable).abs
  have hηb (x : X) : |η x| ≤ B := by simpa only [η, abs_abs] using hB (SobolevSpace.toLp μ hQ f x)
  let θ := boundedMultiplier μ η hη B hηb
  have hs : SobolevSpace.minimalSlope μ hQ (SobolevSpace.comp μ hQ hφ hφ0 f) ≤
      lpMultiplier μ θ (SobolevSpace.minimalSlope μ hQ f) :=
    SobolevSpace.minimalSlope_le μ hQ _
      ((SobolevSpace.minimalSlope_isRelaxed μ hQ f).comp_C1 μ hφ hφ0 hψ hd B hB)
  filter_upwards [(Lp.coeFn_le _ _).mpr hs,
    lpMultiplier_coe μ θ (SobolevSpace.minimalSlope μ hQ f),
    boundedMultiplier_coe μ η hη B hηb] with x hx hm hc
  rw [hm, show θ x = η x from hc] at hx
  exact hx

omit [BorelSpace X] [ProperSpace X] in
 theorem SobolevSpace.comp_comp_eq (f : SobolevSpace μ hQ)
    {φ θ : ℝ → ℝ} {C D : ℝ≥0} (hφ : LipschitzWith C φ) (hφ0 : φ 0 = 0)
    (hθ : LipschitzWith D θ) (hθ0 : θ 0 = 0) (hleft : Function.LeftInverse θ φ) :
    SobolevSpace.comp μ hQ hθ hθ0 (SobolevSpace.comp μ hQ hφ hφ0 f) = f := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [SobolevSpace.comp_coe μ hQ hθ hθ0 (SobolevSpace.comp μ hQ hφ hφ0 f),
    SobolevSpace.comp_coe μ hQ hφ hφ0 f] with x hh hp
  change SobolevSpace.toLp μ hQ (SobolevSpace.comp μ hQ hθ hθ0 _ ) x = _
  simp only [Function.comp_apply, hp] at hh
  exact hh.trans (hleft _)

 
 theorem SobolevSpace.minimalSlope_comp_C1_inverse (f : SobolevSpace μ hQ)
    {φ ψ θ χ : ℝ → ℝ} {C D : ℝ≥0}
    (hφ : LipschitzWith C φ) (hφ0 : φ 0 = 0) (hψ : Continuous ψ)
    (hd : ∀ a, HasDerivAt φ (ψ a) a) (B : ℝ≥0) (hB : ∀ a, |ψ a| ≤ B)
    (hθ : LipschitzWith D θ) (hθ0 : θ 0 = 0) (hχ : Continuous χ)
    (he : ∀ a, HasDerivAt θ (χ a) a) (E : ℝ≥0) (hE : ∀ a, |χ a| ≤ E)
    (hleft : Function.LeftInverse θ φ) :
    ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ (SobolevSpace.comp μ hQ hφ hφ0 f) x =
      |ψ (SobolevSpace.toLp μ hQ f x)| * SobolevSpace.minimalSlope μ hQ f x := by
  have hid (a : ℝ) : χ (φ a) * ψ a = 1 := by
    have h := (he (φ a)).comp a (hd a)
    have ht : (θ ∘ φ) = id := funext hleft
    rw [ht] at h
    exact h.unique (hasDerivAt_id a)
  have ha := SobolevSpace.minimalSlope_comp_C1_le μ hQ f hφ hφ0 hψ hd B hB
  have hb := SobolevSpace.minimalSlope_comp_C1_le μ hQ
    (SobolevSpace.comp μ hQ hφ hφ0 f) hθ hθ0 hχ he E hE
  rw [SobolevSpace.comp_comp_eq μ hQ f hφ hφ0 hθ hθ0 hleft] at hb
  filter_upwards [ha, hb, SobolevSpace.comp_coe μ hQ hφ hφ0 f] with x ha hb hc
  apply le_antisymm ha
  have hprod : |ψ (SobolevSpace.toLp μ hQ f x)| * |χ (φ (SobolevSpace.toLp μ hQ f x))| = 1 := by
    rw [← abs_mul, mul_comm, hid, abs_one]
  have h := mul_le_mul_of_nonneg_left hb (abs_nonneg (ψ (SobolevSpace.toLp μ hQ f x)))
  simp only [hc, Function.comp_apply] at h
  rwa [← mul_assoc, hprod, one_mul] at h

end ChainEquality

variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

 theorem SobolevSpace.chain_signed_lower (f : SobolevSpace μ hQ)
    {φ ψ : ℝ → ℝ} {C : ℝ≥0} (hφ : LipschitzWith C φ) (hφ0 : φ 0 = 0)
    (hψ : Continuous ψ) (hd : ∀ a, HasDerivAt φ (ψ a) a)
    (B : ℝ≥0) (hB : ∀ a, |ψ a| ≤ B)
    (t : ℝ) (htC : |t| * C ≤ 1/2) (htB : |t| * B ≤ 1/2) :
    ∀ᵐ x ∂μ, t * ψ (SobolevSpace.toLp μ hQ f x) * SobolevSpace.minimalSlope μ hQ f x ≤
      |t| * SobolevSpace.minimalSlope μ hQ (SobolevSpace.comp μ hQ hφ hφ0 f) x := by
  let η : ℝ → ℝ := fun a => t * φ a
  let κ : ℝ → ℝ := fun a => t * ψ a
  have hη : LipschitzWith (1/2) η := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    simp only [η, Real.dist_eq, ← mul_sub, abs_mul, NNReal.coe_div, NNReal.coe_one,
      NNReal.coe_ofNat]
    calc
      |t| * |φ a - φ b| ≤ |t| * ((C : ℝ) * |a-b|) :=
        mul_le_mul_of_nonneg_left (hφ.dist_le_mul a b) (abs_nonneg t)
      _ ≤ 1/2 * |a-b| := by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right htC (abs_nonneg _)
  have hη0 : η 0 = 0 := by simp [η, hφ0]
  have hκ : Continuous κ := hψ.const_mul t
  have hκd (a : ℝ) : HasDerivAt η (κ a) a := (hd a).const_mul t
  have hκb (a : ℝ) : |κ a| ≤ 1/2 := by
    dsimp [κ]
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (hB a) (abs_nonneg t)).trans htB
  obtain ⟨θ, χ, hθ, hθ0, hχ, hχd, hχb, hleft⟩ :=
    scalar_small_perturbation_inverse hη hη0 hκ hκd hκb
  let F : ℝ → ℝ := fun a => a + η a
  have hF : LipschitzWith (3/2) F := by
    convert LipschitzWith.id.add hη using 1 <;> first | rfl | norm_num
  have hF0 : F 0 = 0 := by simp [F, hη0]
  have hD : Continuous (fun a => 1+κ a) := continuous_const.add hκ
  have hFd (a : ℝ) : HasDerivAt F (1+κ a) a := (hasDerivAt_id a).add (hκd a)
  have hDb (a : ℝ) : |1+κ a| ≤ (3/2 : ℝ≥0) := by
    have h := abs_add_le 1 (κ a)
    norm_num only [abs_one, NNReal.coe_div, NNReal.coe_ofNat] at h ⊢
    linarith [hκb a]
  have hFp (a : ℝ) : 0 < 1+κ a := by have h := (abs_le.mp (hκb a)).1; linarith
  have hchain := SobolevSpace.minimalSlope_comp_C1_inverse μ hQ f hF hF0 hD hFd
    (3/2) hDb hθ hθ0 hχ hχd 2 (by simpa using hχb) hleft
  let g := SobolevSpace.comp μ hQ hφ hφ0 f
  have hcomp : SobolevSpace.comp μ hQ hF hF0 f = f+t • g := by
    apply Subtype.ext
    apply Lp.ext
    have hadd := Lp.coeFn_add (SobolevSpace.toLp μ hQ f)
      (t • SobolevSpace.toLp μ hQ g)
    have hsmul := Lp.coeFn_smul t (SobolevSpace.toLp μ hQ g)
    filter_upwards [SobolevSpace.comp_coe μ hQ hF hF0 f,
      SobolevSpace.comp_coe μ hQ hφ hφ0 f, hadd, hsmul] with x hf hg ha hs
    change SobolevSpace.toLp μ hQ (SobolevSpace.comp μ hQ hF hF0 f) x = _
    rw [hf]
    change _ = (SobolevSpace.toLp μ hQ f + t • SobolevSpace.toLp μ hQ g) x
    rw [ha, Pi.add_apply, hs, Pi.smul_apply, smul_eq_mul]
    exact congrArg (fun a => SobolevSpace.toLp μ hQ f x + t * a) hg.symm
  rw [hcomp] at hchain
  have htri := SobolevSpace.minimalSlope_add_le μ hQ f (t • g)
  rw [SobolevSpace.minimalSlope_smul] at htri
  filter_upwards [hchain, (Lp.coeFn_le _ _).mpr htri,
    Lp.coeFn_add (SobolevSpace.minimalSlope μ hQ f) (|t| • SobolevSpace.minimalSlope μ hQ g),
    Lp.coeFn_smul |t| (SobolevSpace.minimalSlope μ hQ g)] with x hc ht ha hs
  rw [hc, abs_of_pos (hFp _), ha, Pi.add_apply, hs, Pi.smul_apply, smul_eq_mul] at ht
  dsimp [κ] at ht
  nlinarith

 

 theorem SobolevSpace.minimalSlope_comp_C1 (f : SobolevSpace μ hQ)
    {φ ψ : ℝ → ℝ} {C : ℝ≥0} (hφ : LipschitzWith C φ) (hφ0 : φ 0 = 0)
    (hψ : Continuous ψ) (hd : ∀ a, HasDerivAt φ (ψ a) a)
    (B : ℝ≥0) (hB : ∀ a, |ψ a| ≤ B) :
    ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ (SobolevSpace.comp μ hQ hφ hφ0 f) x =
      |ψ (SobolevSpace.toLp μ hQ f x)| * SobolevSpace.minimalSlope μ hQ f x := by
  let t : ℝ := (4*((C : ℝ)+(B : ℝ)+1))⁻¹
  have hden : 0 < 4*((C : ℝ)+(B : ℝ)+1) := by positivity
  have ht : 0 < t := inv_pos.mpr hden
  have htC : |t| * C ≤ 1/2 := by
    rw [abs_of_pos ht]
    dsimp [t]
    rw [inv_mul_eq_div, div_le_iff₀ hden]
    linarith [B.coe_nonneg, C.coe_nonneg]
  have htB : |t| * B ≤ 1/2 := by
    rw [abs_of_pos ht]
    dsimp [t]
    rw [inv_mul_eq_div, div_le_iff₀ hden]
    linarith [B.coe_nonneg, C.coe_nonneg]
  have hp := SobolevSpace.chain_signed_lower μ hQ f hφ hφ0 hψ hd B hB t htC htB
  have hn := SobolevSpace.chain_signed_lower μ hQ f hφ hφ0 hψ hd B hB (-t)
    (by simpa only [abs_neg] using htC) (by simpa only [abs_neg] using htB)
  have hu := SobolevSpace.minimalSlope_comp_C1_le μ hQ f hφ hφ0 hψ hd B hB
  filter_upwards [hp, hn, hu] with x hp hn hu
  apply le_antisymm hu
  rw [abs_of_pos ht] at hp
  rw [abs_neg, abs_of_pos ht] at hn
  by_cases h : 0 ≤ ψ (SobolevSpace.toLp μ hQ f x)
  · rw [abs_of_nonneg h]
    nlinarith
  · rw [abs_of_neg (lt_of_not_ge h)]
    nlinarith

end RegularPointCoordinates

end OAI
