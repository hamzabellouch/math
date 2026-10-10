import Mathlib
import OAI.Analysis.RCDHeat.HeatH1
import OAI.Analysis.RCDHeat.SlopeMeasurability

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: RelaxedSlope, RelaxedSlopeClosure, LpMultiplier, PointwiseGluing, RelaxedGluing. -/



open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
namespace RegularPointCoordinates
universe u
open Metric
section RelaxedSlope
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] (μ : Measure X)

 

def IsRelaxedSlope (f G : Lp ℝ 2 μ) : Prop :=
  ∃ (us : ℕ → Lp ℝ 2 μ) (gs : ℕ → X → ℝ) (Gs : ℕ → Lp ℝ 2 μ),
    (∀ i, ∃ C : ℝ≥0, LipschitzWith C (gs i)) ∧
    (∀ i, ⇑(us i) =ᵐ[μ] gs i) ∧
    (∀ i, IsSlopeMajorant μ (gs i) (Gs i)) ∧
    Tendsto us atTop (𝓝 f) ∧ Tendsto Gs atTop (𝓝 G)

 theorem IsRelaxedSlope.nonneg {f G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ f G) :
    0 ≤ G := by
  obtain ⟨us, gs, Gs, _, _, hm, _, hc⟩ := hG
  exact (isClosed_Ici (a := (0 : Lp ℝ 2 μ))).mem_of_tendsto hc
    (Eventually.of_forall fun i => (Lp.coeFn_nonneg _).mp
      ((hm i).mono fun x hx => hx.1))

 theorem IsRelaxedSlope.energy_le {f G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ f G) :
    energyLp μ f ≤ ENNReal.ofReal (‖G‖ ^ 2 / 2) := by
  obtain ⟨us, gs, Gs, hl, ha, hm, hu, hG⟩ := hG
  have hnorm : Tendsto (fun i => ENNReal.ofReal (‖Gs i‖ ^ 2 / 2)) atTop
      (𝓝 (ENNReal.ofReal (‖G‖ ^ 2 / 2))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((hG.norm.pow 2).div_const 2)
  calc
    energyLp μ f ≤ liminf (fun i => energyLp μ (us i)) atTop := energyLp_le_liminf μ hu
    _ ≤ liminf (fun i => ENNReal.ofReal (‖Gs i‖ ^ 2 / 2)) atTop := by
      exact liminf_le_liminf (Eventually.of_forall fun i => by
        obtain ⟨C, hC⟩ := hl i
        exact energyLp_le_of_lipschitz_majorant μ hC (ha i) (hm i))
    _ = _ := hnorm.liminf_eq

 theorem IsRelaxedSlope.add {f g G H : Lp ℝ 2 μ}
    (hG : IsRelaxedSlope μ f G) (hH : IsRelaxedSlope μ g H) :
    IsRelaxedSlope μ (f + g) (G + H) := by
  obtain ⟨us, gs, Gs, hl, ha, hm, hu, hG⟩ := hG
  obtain ⟨vs, hs, Hs, hk, hb, hn, hv, hH⟩ := hH
  refine ⟨fun i => us i + vs i, fun i x => gs i x + hs i x,
    fun i => Gs i + Hs i, ?_, ?_, fun i => (hm i).add μ (hn i), hu.add hv, hG.add hH⟩
  · intro i
    obtain ⟨C, hC⟩ := hl i
    obtain ⟨D, hD⟩ := hk i
    exact ⟨C+D, hC.add hD⟩
  · intro i
    filter_upwards [Lp.coeFn_add (us i) (vs i), ha i, hb i] with x hx hu hv
    simpa only [Pi.add_apply, hu, hv] using hx

 theorem IsRelaxedSlope.const_mul {f G : Lp ℝ 2 μ}
    (hG : IsRelaxedSlope μ f G) {c : ℝ} (hc : 0 ≤ c) :
    IsRelaxedSlope μ (c • f) (c • G) := by
  obtain ⟨us, gs, Gs, hl, ha, hm, hu, hG⟩ := hG
  refine ⟨fun i => c • us i, fun i x => c * gs i x, fun i => c • Gs i,
    ?_, ?_, fun i => (hm i).const_mul μ hc, hu.const_smul c, hG.const_smul c⟩
  · intro i
    obtain ⟨C, hC⟩ := hl i
    exact ⟨‖c‖₊ * C, lipschitzWith_const_mul_real hC c⟩
  · intro i
    filter_upwards [Lp.coeFn_smul c (us i), ha i] with x hx hu
    simpa only [Pi.smul_apply, smul_eq_mul, hu] using hx

 theorem IsRelaxedSlope.unique_minimizer {f G H : Lp ℝ 2 μ}
    (hG : IsRelaxedSlope μ f G) (hH : IsRelaxedSlope μ f H)
    (hnG : ‖G‖ ^ 2 = 2 * (energyLp μ f).toReal)
    (hnH : ‖H‖ ^ 2 = 2 * (energyLp μ f).toReal) : G = H := by
  have hm := (hG.add μ hH).const_mul μ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hff : (1 / 2 : ℝ) • (f + f) = f := by module
  rw [hff] at hm
  have he := ENNReal.toReal_le_of_le_ofReal (by positivity)
    (IsRelaxedSlope.energy_le μ hm)
  have hnm : ‖(1 / 2 : ℝ) • (G + H)‖ ^ 2 = (1 / 4 : ℝ) * ‖G + H‖ ^ 2 := by
    rw [norm_smul]
    norm_num [mul_pow]
  have hp := parallelogram_law_with_norm ℝ G H
  have hd : ‖G - H‖ = 0 := by nlinarith [norm_nonneg (G - H)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hd)

variable [BorelSpace X] (hQ : QuadraticCheegerEnergy μ)

 

theorem SobolevSpace.exists_minimalRelaxedSlope (f : SobolevSpace μ hQ) :
    ∃ G : Lp ℝ 2 μ, IsRelaxedSlope μ (SobolevSpace.toLp μ hQ f) G ∧
      ‖G‖ ^ 2 = 2 * SobolevSpace.energy μ hQ f := by
  obtain ⟨fs, gs, hc, hl⟩ := SobolevSpace.exists_strong_lipschitz_recovery μ hQ f
  choose Cs hCs using fun i => (hl i).1
  have hfin (i : ℕ) : slopeEnergy μ (gs i) ≠ ∞ :=
    ((hl i).2.2.trans_le le_top).ne
  let Gs : ℕ → Lp ℝ 2 μ := fun i => lipschitzSlopeLp μ (hCs i) (hfin i)
  have hmaj (i : ℕ) : IsSlopeMajorant μ (gs i) (Gs i) := by
    filter_upwards [lipschitzSlopeLp_nonneg μ (hCs i) (hfin i),
      lipschitzSlopeLp_enorm μ (hCs i) (hfin i)] with x hx he
    refine ⟨hx, ?_⟩
    rw [← he, Real.enorm_of_nonneg hx]
  have hn (i : ℕ) : ‖Gs i‖ ^ 2 ≤ 2 * (SobolevSpace.energy μ hQ f + (1 / 2 : ℝ) ^ i) := by
    have h := (hl i).2.2
    rw [lipschitzSlopeLp_energy μ (hCs i) (hfin i)] at h
    have hpos : 0 < SobolevSpace.energy μ hQ f + (1 / 2 : ℝ) ^ i :=
      add_pos_of_nonneg_of_pos (SobolevSpace.energy_nonneg μ hQ f) (pow_pos (by norm_num) i)
    have hh := (ENNReal.ofReal_lt_ofReal_iff hpos).mp h
    change ‖Gs i‖ ^ 2 / 2 < _ at hh
    linarith
  have hδ : Tendsto (fun i : ℕ => (1 / 2 : ℝ) ^ i) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hLp := (SobolevSpace.toLpCLM μ hQ).continuous.continuousAt.tendsto.comp hc
  have hC : CauchySeq Gs := by
    apply slopeMajorants_cauchy_of_recovery μ (SobolevSpace.toLp μ hQ f) f.property
      (fun i => SobolevSpace.toLp μ hQ (fs i)) gs Gs
      (fun i => ⟨Cs i, hCs i⟩) (fun i => (hl i).2.1) hmaj hLp
    intro ε hε
    filter_upwards [hδ.eventually (gt_mem_nhds hε)] with i hi
    change ‖Gs i‖ ^ 2 ≤ 2 * (SobolevSpace.energy μ hQ f + ε)
    linarith [hn i]
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete hC
  have hrel : IsRelaxedSlope μ (SobolevSpace.toLp μ hQ f) G :=
    ⟨fun i => SobolevSpace.toLp μ hQ (fs i), gs, Gs, fun i => ⟨Cs i, hCs i⟩,
      fun i => (hl i).2.1, hmaj, hLp, hG⟩
  refine ⟨G, hrel, le_antisymm ?_ ?_⟩
  · have hlim := ((tendsto_const_nhds (x := SobolevSpace.energy μ hQ f)).add hδ).const_mul 2
    simp only [add_zero] at hlim
    exact le_of_tendsto_of_tendsto (hG.norm.pow 2) hlim (Eventually.of_forall hn)
  · have h := ENNReal.toReal_le_of_le_ofReal (by positivity) (hrel.energy_le μ)
    change SobolevSpace.energy μ hQ f ≤ ‖G‖ ^ 2 / 2 at h
    linarith

noncomputable def SobolevSpace.minimalSlope (f : SobolevSpace μ hQ) : Lp ℝ 2 μ :=
  Classical.choose (SobolevSpace.exists_minimalRelaxedSlope μ hQ f)

 theorem SobolevSpace.minimalSlope_isRelaxed (f : SobolevSpace μ hQ) :
    IsRelaxedSlope μ (SobolevSpace.toLp μ hQ f) (SobolevSpace.minimalSlope μ hQ f) :=
  (Classical.choose_spec (SobolevSpace.exists_minimalRelaxedSlope μ hQ f)).1

 theorem SobolevSpace.minimalSlope_norm_sq (f : SobolevSpace μ hQ) :
    ‖SobolevSpace.minimalSlope μ hQ f‖ ^ 2 = 2 * SobolevSpace.energy μ hQ f :=
  (Classical.choose_spec (SobolevSpace.exists_minimalRelaxedSlope μ hQ f)).2

end RelaxedSlope

section RelaxedSlopeClosure
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] (μ : Measure X)

 theorem IsRelaxedSlope.mono {f G H : Lp ℝ 2 μ}
    (hG : IsRelaxedSlope μ f G) (hGH : G ≤ H) : IsRelaxedSlope μ f H := by
  obtain ⟨us, gs, Gs, hl, ha, hm, hu, hG⟩ := hG
  refine ⟨us, gs, fun i => Gs i + (H - G), hl, ha, ?_, hu, ?_⟩
  · intro i
    filter_upwards [hm i, Lp.coeFn_add (Gs i) (H - G), Lp.coeFn_sub H G,
      (Lp.coeFn_le G H).mpr hGH] with x hx hadd hsub hle
    simp only [Pi.add_apply, Pi.sub_apply] at hadd hsub
    rw [hadd, hsub]
    exact ⟨by linarith [hx.1], hx.2.trans (ENNReal.ofReal_le_ofReal (by linarith))⟩
  · convert hG.add_const (H - G) using 1; abel_nf

 

 theorem IsRelaxedSlope.of_tendsto {fs Gs : ℕ → Lp ℝ 2 μ} {f G : Lp ℝ 2 μ}
    (h : ∀ i, IsRelaxedSlope μ (fs i) (Gs i))
    (hf : Tendsto fs atTop (𝓝 f)) (hG : Tendsto Gs atTop (𝓝 G)) :
    IsRelaxedSlope μ f G := by
  choose us gs Hs hl ha hm huu hHH using h
  have hchoose (i : ℕ) : ∃ j : ℕ,
      dist (us i j) (fs i) < (1 / 2 : ℝ)^i ∧
      dist (Hs i j) (Gs i) < (1 / 2 : ℝ)^i := by
    exact ((Metric.tendsto_nhds.mp (huu i) _ (pow_pos (by norm_num) i)).and
      (Metric.tendsto_nhds.mp (hHH i) _ (pow_pos (by norm_num) i))).exists
  choose j hj using hchoose
  have hδ : Tendsto (fun i : ℕ => (1 / 2 : ℝ)^i) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  refine ⟨fun i => us i (j i), fun i => gs i (j i), fun i => Hs i (j i),
    fun i => hl i (j i), fun i => ha i (j i), fun i => hm i (j i), ?_, ?_⟩
  · apply hf.congr_dist
    simp_rw [dist_comm (fs _) (us _ _)]
    exact squeeze_zero (fun _ => dist_nonneg) (fun i => (hj i).1.le) hδ
  · apply hG.congr_dist
    simp_rw [dist_comm (Gs _) (Hs _ _)]
    exact squeeze_zero (fun _ => dist_nonneg) (fun i => (hj i).2.le) hδ

 theorem relaxedSlope_isClosed : IsClosed {z : Lp ℝ 2 μ × Lp ℝ 2 μ |
    IsRelaxedSlope μ z.1 z.2} := by
  apply IsSeqClosed.isClosed
  intro zs z hz hc
  exact IsRelaxedSlope.of_tendsto μ hz (continuous_fst.tendsto z |>.comp hc)
    (continuous_snd.tendsto z |>.comp hc)

end RelaxedSlopeClosure

section LpMultiplier
variable {X : Type u} [MeasurableSpace X] (μ : Measure X)

 
noncomputable def lpMultiplier (θ : Lp ℝ ∞ μ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun f => θ • f
      map_add' := fun f g => Lp.add_smul θ f g
      map_smul' := fun c f => (Lp.smul_comm c θ f).symm }
    ‖θ‖ (fun f => Lp.norm_smul_le θ f)

 theorem lpMultiplier_coe (θ : Lp ℝ ∞ μ) (f : Lp ℝ 2 μ) :
    ⇑(lpMultiplier μ θ f) =ᵐ[μ] fun x => θ x * f x := by
  exact Lp.coeFn_lpSMul θ f

 theorem lpMultiplier_congr {θ η : Lp ℝ ∞ μ} {f g : Lp ℝ 2 μ}
    (h : ∀ᵐ x ∂μ, θ x * f x = η x * g x) :
    lpMultiplier μ θ f = lpMultiplier μ η g := by
  apply Lp.ext
  filter_upwards [lpMultiplier_coe μ θ f, lpMultiplier_coe μ η g, h] with x hx hy hh
  exact hx.trans (hh.trans hy.symm)

omit μ [MeasurableSpace X] in
 theorem real_lipschitz_abs : LipschitzWith 1 (abs : ℝ → ℝ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using abs_abs_sub_abs_le x y

noncomputable def lpAbs : Lp ℝ 2 μ → Lp ℝ 2 μ :=
  real_lipschitz_abs.compLp (abs_zero : |(0 : ℝ)| = 0)

 theorem lpAbs_coe (f : Lp ℝ 2 μ) :
    ⇑(lpAbs μ f) =ᵐ[μ] fun x => |f x| :=
  real_lipschitz_abs.coeFn_compLp abs_zero f

 theorem lpAbs_continuous : Continuous (lpAbs μ) :=
  real_lipschitz_abs.continuous_compLp abs_zero

 theorem lpAbs_zero : lpAbs μ 0 = 0 :=
  real_lipschitz_abs.compLp_zero abs_zero

end LpMultiplier

section PointwiseGluing
variable {X : Type u} [MetricSpace X]

 theorem localSlope_sub_const (f : X → ℝ) (c : ℝ) (x : X) :
    localSlope (fun y => f y - c) x = localSlope f x := by
  simp only [localSlope, sub_sub_sub_cancel_right]

 

 theorem localSlope_convex_glue {θ g h : X → ℝ} {C D E : ℝ≥0}
    (hθ : LipschitzWith C θ) (hg : LipschitzWith D g) (hh : LipschitzWith E h)
    (x : X) (hθ0 : 0 ≤ θ x) (hθ1 : θ x ≤ 1) :
    localSlope (fun y => θ y * g y + (1 - θ y) * h y) x ≤
      ENNReal.ofReal (θ x) * localSlope g x +
      ENNReal.ofReal (1 - θ x) * localSlope h x +
      ENNReal.ofReal |g x - h x| * C := by
  have hid : (fun y => θ y * g y + (1 - θ y) * h y) =
      (fun y => (θ x * g y + (1 - θ x) * h y) +
        (θ y - θ x) * (g y - h y)) := by funext y; ring
  rw [hid]
  apply (localSlope_add_le _ _ x).trans
  apply add_le_add
  · apply (localSlope_add_le _ _ x).trans
    simp only [localSlope_const_mul, abs_of_nonneg hθ0,
      abs_of_nonneg (sub_nonneg.mpr hθ1), le_refl]
  · have hfin : localSlope (fun y => g y - h y) x ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.coe_ne_top (localSlope_le_of_lipschitz (hg.sub hh) x)
    have he := localSlope_mul_le
      (hθ.continuous.continuousAt.sub_const (θ x)) hfin
    simp only [sub_self, abs_zero, ENNReal.ofReal_zero, zero_mul, zero_add,
      localSlope_sub_const] at he
    exact he.trans (mul_le_mul' le_rfl (localSlope_le_of_lipschitz hθ x))

 

 theorem lipschitzWith_mul_of_support_bound {θ g : X → ℝ} {C D A B : ℝ≥0}
    (hθ : LipschitzWith C θ) (hg : LipschitzWith D g)
    (hA : ∀ x, |θ x| ≤ A) (hB : ∀ x, θ x ≠ 0 → |g x| ≤ B) :
    LipschitzWith (A * D + B * C) (fun x => θ x * g x) := by
  suffices h : ∀ x y, θ x ≠ 0 →
      |θ x * g x - θ y * g y| ≤ ((A * D + B * C : ℝ≥0) : ℝ) * dist x y by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq]
    by_cases hx : θ x = 0
    · by_cases hy : θ y = 0
      · simp only [hx, hy, zero_mul, sub_self, abs_zero]
        positivity
      · simpa only [abs_sub_comm, dist_comm] using h y x hy
    · exact h x y hx
  intro x y hx
  have hid : θ x * g x - θ y * g y =
      θ y * (g x - g y) + g x * (θ x - θ y) := by ring
  rw [hid]
  calc
    _ ≤ |θ y| * |g x - g y| + |g x| * |θ x - θ y| := by
      simpa only [abs_mul] using abs_add_le (θ y * (g x - g y)) (g x * (θ x - θ y))
    _ ≤ (A : ℝ) * ((D : ℝ) * dist x y) + (B : ℝ) * ((C : ℝ) * dist x y) := by
      apply add_le_add
      · exact mul_le_mul (hA y) (by simpa only [Real.dist_eq] using hg.dist_le_mul x y)
          (abs_nonneg _) A.coe_nonneg
      · exact mul_le_mul (hB x hx) (by simpa only [Real.dist_eq] using hθ.dist_le_mul x y)
          (abs_nonneg _) B.coe_nonneg
    _ = _ := by simp only [NNReal.coe_add, NNReal.coe_mul]; ring

end PointwiseGluing

section RelaxedGluing
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X)

omit [MeasurableSpace X] [BorelSpace X] in
 theorem lipschitz_mul_compact_cutoff {θ g : X → ℝ} {C D : ℝ≥0}
    (hθ : LipschitzWith C θ) (hg : LipschitzWith D g)
    (hs : HasCompactSupport θ) (hbound : ∀ x, |θ x| ≤ 1) :
    ∃ L : ℝ≥0, LipschitzWith L (fun x => θ x * g x) := by
  obtain ⟨B, hB⟩ := hs.exists_bound_of_continuousOn hg.continuous.continuousOn
  let B' : ℝ≥0 := ⟨max B 0, le_max_right _ _⟩
  refine ⟨1 * D + B' * C, lipschitzWith_mul_of_support_bound hθ hg hbound ?_⟩
  intro x hx
  have hb := hB x (subset_tsupport θ hx)
  have hb' : |g x| ≤ B := by simpa only [Real.norm_eq_abs] using hb
  exact hb'.trans (le_max_left B 0)

omit [BorelSpace X] in
 

 theorem IsRelaxedSlope.cutoff_blend {f G H : Lp ℝ 2 μ}
    (hG : IsRelaxedSlope μ f G) (hH : IsRelaxedSlope μ f H)
    {θ : X → ℝ} {C : ℝ≥0} (hθ : LipschitzWith C θ)
    (hs : HasCompactSupport θ) (hb : ∀ x, 0 ≤ θ x ∧ θ x ≤ 1)
    (θlp : Lp ℝ ∞ μ) (hθlp : ⇑θlp =ᵐ[μ] θ) :
    IsRelaxedSlope μ f (lpMultiplier μ θlp (G - H) + H) := by
  obtain ⟨us, gs, Gs, hl, ha, hm, hu, hc⟩ := hG
  obtain ⟨vs, hs', Hs, hk, hb', hn, hv, hd⟩ := hH
  let ws : ℕ → Lp ℝ 2 μ := fun i => lpMultiplier μ θlp (us i - vs i) + vs i
  let ks : ℕ → X → ℝ := fun i x => θ x * gs i x + (1 - θ x) * hs' i x
  let Ws : ℕ → Lp ℝ 2 μ := fun i =>
    lpMultiplier μ θlp (Gs i - Hs i) + Hs i + (C : ℝ) • lpAbs μ (us i - vs i)
  have hla (i : ℕ) : ∃ L : ℝ≥0, LipschitzWith L (ks i) := by
    obtain ⟨D, hD⟩ := hl i
    obtain ⟨E, hE⟩ := hk i
    obtain ⟨L, hL⟩ := lipschitz_mul_compact_cutoff hθ (hD.sub hE) hs
      (fun x => by rw [abs_of_nonneg (hb x).1]; exact (hb x).2)
    refine ⟨L + E, ?_⟩
    convert! hL.add hE using 1
    funext x
    dsimp [ks]
    ring
  have hae (i : ℕ) : ⇑(ws i) =ᵐ[μ] ks i := by
    filter_upwards [Lp.coeFn_add (lpMultiplier μ θlp (us i - vs i)) (vs i),
      lpMultiplier_coe μ θlp (us i - vs i), Lp.coeFn_sub (us i) (vs i),
      ha i, hb' i, hθlp] with x hadd hmul hsub hu' hv' hθ'
    change (lpMultiplier μ θlp (us i - vs i) + vs i) x = _
    simp only [Pi.add_apply, Pi.sub_apply] at hadd hsub
    rw [hadd, hmul, hsub, hu', hv', hθ']
    dsimp [ks]
    ring
  have hmaj (i : ℕ) : IsSlopeMajorant μ (ks i) (Ws i) := by
    obtain ⟨D, hD⟩ := hl i
    obtain ⟨E, hE⟩ := hk i
    filter_upwards [Lp.coeFn_add (lpMultiplier μ θlp (Gs i - Hs i) + Hs i)
        ((C : ℝ) • lpAbs μ (us i - vs i)),
      Lp.coeFn_add (lpMultiplier μ θlp (Gs i - Hs i)) (Hs i),
      lpMultiplier_coe μ θlp (Gs i - Hs i), Lp.coeFn_sub (Gs i) (Hs i),
      Lp.coeFn_smul (C : ℝ) (lpAbs μ (us i - vs i)), lpAbs_coe μ (us i - vs i),
      Lp.coeFn_sub (us i) (vs i), hm i, hn i, ha i, hb' i, hθlp]
      with x hadd hadd' hmul hsub hsm habs huv hG' hH' hu' hv' hθ'
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at *
    change 0 ≤ (lpMultiplier μ θlp (Gs i - Hs i) + Hs i +
      (C : ℝ) • lpAbs μ (us i - vs i)) x ∧ _
    rw [hadd, hadd', hmul, hsub, hsm, habs, huv, hu', hv', hθ']
    have heq : θ x * (Gs i x - Hs i x) + Hs i x + (C : ℝ) * |gs i x - hs' i x| =
        θ x * Gs i x + (1 - θ x) * Hs i x + |gs i x - hs' i x| * C := by ring
    rw [heq]
    have h0 : 0 ≤ θ x * Gs i x := mul_nonneg (hb x).1 hG'.1
    have h1 : 0 ≤ (1 - θ x) * Hs i x := mul_nonneg (sub_nonneg.mpr (hb x).2) hH'.1
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ENNReal.ofReal (θ x) * localSlope (gs i) x +
          ENNReal.ofReal (1 - θ x) * localSlope (hs' i) x +
          ENNReal.ofReal |gs i x - hs' i x| * C :=
        localSlope_convex_glue hθ hD hE x (hb x).1 (hb x).2
      _ ≤ ENNReal.ofReal (θ x) * ENNReal.ofReal (Gs i x) +
          ENNReal.ofReal (1 - θ x) * ENNReal.ofReal (Hs i x) +
          ENNReal.ofReal |gs i x - hs' i x| * C := by gcongr; exacts [hG'.2, hH'.2]
      _ = _ := by
        rw [ENNReal.ofReal_add (add_nonneg h0 h1) (by positivity),
          ENNReal.ofReal_add h0 h1, ENNReal.ofReal_mul (hb x).1,
          ENNReal.ofReal_mul (sub_nonneg.mpr (hb x).2),
          ENNReal.ofReal_mul (abs_nonneg _), ENNReal.ofReal_coe_nnreal]
  refine ⟨ws, ks, Ws, hla, hae, hmaj, ?_, ?_⟩
  · have hlim := ((lpMultiplier μ θlp).continuous.continuousAt.tendsto.comp (hu.sub hv)).add hv
    simpa only [ws, Function.comp_def, sub_self, map_zero, zero_add] using hlim
  · have hzero := ((lpAbs_continuous μ).continuousAt.tendsto.comp (hu.sub hv)).const_smul (C : ℝ)
    simp only [sub_self, lpAbs_zero, smul_zero] at hzero
    have hlim := (((lpMultiplier μ θlp).continuous.continuousAt.tendsto.comp (hc.sub hd)).add hd).add hzero
    simpa only [Ws, Function.comp_def, add_zero] using hlim

end RelaxedGluing

open Metric
end RegularPointCoordinates

end OAI
