import Mathlib
import OAI.Analysis.RCDHeat.WeightedCutoff

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: RelaxedChain, Flatten, SlopeLocality, CompConvergence, SlopeEquality. -/



open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
namespace RegularPointCoordinates
universe u
open Metric
open Metric
section RelaxedChain
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X)

 

 theorem IsRelaxedSlope.comp_C1 {f G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ f G)
    {φ ψ : ℝ → ℝ} {C : ℝ≥0} (hφ : LipschitzWith C φ) (hφ0 : φ 0 = 0)
    (hψ : Continuous ψ) (hd : ∀ a, HasDerivAt φ (ψ a) a)
    (B : ℝ≥0) (hB : ∀ a, |ψ a| ≤ B) :
    IsRelaxedSlope μ (hφ.compLp hφ0 f)
      (lpMultiplier μ (boundedMultiplier μ (fun x => |ψ (f x)|)
        (hψ.measurable.comp (Lp.stronglyMeasurable f).measurable).abs B
        (fun x => by simpa only [abs_abs] using hB (f x))) G) := by
  obtain ⟨us, gs, Gs, hl, ha, hm, hu, hc⟩ := hG
  obtain ⟨ns, hns, hnsae⟩ := (tendstoInMeasure_of_tendsto_Lp hu).exists_seq_tendsto_ae
  choose Cs hCs using hl
  let ηs (i : ℕ) (x : X) := |ψ (gs (ns i) x)|
  let η (x : X) := |ψ (f x)|
  have hs (i : ℕ) : Measurable (ηs i) :=
    (hψ.measurable.comp (hCs (ns i)).continuous.measurable).abs
  have hη : Measurable η := (hψ.measurable.comp (Lp.stronglyMeasurable f).measurable).abs
  have hb (i : ℕ) (x : X) : |ηs i x| ≤ B := by
    simpa only [ηs, abs_abs] using hB (gs (ns i) x)
  have hbη (x : X) : |η x| ≤ B := by simpa only [η, abs_abs] using hB (f x)
  let θs (i : ℕ) := boundedMultiplier μ (ηs i) (hs i) B (hb i)
  have hηlim : ∀ᵐ x ∂μ, Tendsto (fun i => ηs i x) atTop (𝓝 (η x)) := by
    filter_upwards [hnsae, ae_all_iff.mpr ha] with x hx he
    have hgs : Tendsto (fun i => gs (ns i) x) atTop (𝓝 (f x)) := by
      simpa only [he] using hx
    exact (hψ.continuousAt.tendsto.comp hgs).abs
  refine ⟨fun i => hφ.compLp hφ0 (us (ns i)), fun i => φ ∘ gs (ns i),
    fun i => lpMultiplier μ (θs i) (Gs (ns i)), ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨C * Cs (ns i), hφ.comp (hCs (ns i))⟩
  · intro i
    filter_upwards [hφ.coeFn_compLp hφ0 (us (ns i)), ha (ns i)] with x hx he
    simpa only [Function.comp_apply, he] using hx
  · intro i
    filter_upwards [lpMultiplier_coe μ (θs i) (Gs (ns i)),
      boundedMultiplier_coe μ (ηs i) (hs i) B (hb i), hm (ns i)] with x hx he hg
    change 0 ≤ lpMultiplier μ (θs i) (Gs (ns i)) x ∧ _
    rw [hx, show θs i x = |ψ (gs (ns i) x)| from he]
    refine ⟨mul_nonneg (abs_nonneg _) hg.1, ?_⟩
    calc
      _ ≤ ENNReal.ofReal |ψ (gs (ns i) x)| * localSlope (gs (ns i)) x :=
        localSlope_comp_hasDerivAt (hd _) (hCs (ns i)).continuous.continuousAt
          (ne_top_of_le_ne_top ENNReal.coe_ne_top (localSlope_le_of_lipschitz (hCs (ns i)) x))
      _ ≤ ENNReal.ofReal |ψ (gs (ns i) x)| * ENNReal.ofReal (Gs (ns i) x) :=
        mul_le_mul' le_rfl hg.2
      _ = _ := (ENNReal.ofReal_mul (abs_nonneg _)).symm
  · exact (hφ.continuous_compLp hφ0).continuousAt.tendsto.comp (hu.comp hns.tendsto_atTop)
  · exact lpMultiplier_tendsto_of_ae_of_tendsto μ (hc.comp hns.tendsto_atTop)
      ηs η hs hη B hb hbη hηlim

end RelaxedChain

section Flatten

 
noncomputable def slopeFlatten (ε a : ℝ) : ℝ := a ^ 3 / (a ^ 2 + ε ^ 2)
noncomputable def slopeFlattenDeriv (ε a : ℝ) : ℝ :=
  (a ^ 4 + 3 * a ^ 2 * ε ^ 2) / (a ^ 2 + ε ^ 2) ^ 2
noncomputable def slopeFlattenFactor (ε a : ℝ) : ℝ := a ^ 2 / (a ^ 2 + ε ^ 2)

 theorem slopeFlatten_den_pos {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    0 < a ^ 2 + ε ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg a) (sq_pos_of_pos hε)

 theorem slopeFlatten_deriv {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    HasDerivAt (slopeFlatten ε) (slopeFlattenDeriv ε a) a := by
  have h := ((hasDerivAt_id a).pow 3).div
    (((hasDerivAt_id a).pow 2).add_const (ε ^ 2)) (ne_of_gt (slopeFlatten_den_pos hε a))
  convert h using 1 <;> first | rfl | (dsimp [slopeFlatten, slopeFlattenDeriv]; ring)

 theorem slopeFlattenDeriv_continuous {ε : ℝ} (hε : 0 < ε) :
    Continuous (slopeFlattenDeriv ε) := by
  unfold slopeFlattenDeriv
  fun_prop (disch := intro a; exact pow_ne_zero 2 (ne_of_gt (slopeFlatten_den_pos hε a)))

 theorem slopeFlattenDeriv_nonneg {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    0 ≤ slopeFlattenDeriv ε a := by
  unfold slopeFlattenDeriv
  positivity

 theorem slopeFlattenDeriv_le {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    slopeFlattenDeriv ε a ≤ 3 := by
  unfold slopeFlattenDeriv
  rw [div_le_iff₀ (sq_pos_of_pos (slopeFlatten_den_pos hε a))]
  nlinarith [sq_nonneg (a ^ 2), sq_nonneg (ε ^ 2), mul_nonneg (sq_nonneg a) (sq_nonneg ε)]

 theorem slopeFlatten_lipschitz {ε : ℝ} (hε : 0 < ε) :
    LipschitzWith 3 (slopeFlatten ε) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun a => (slopeFlatten_deriv hε a).differentiableAt)
  intro a
  change |deriv (slopeFlatten ε) a| ≤ (3 : ℝ)
  rw [(slopeFlatten_deriv hε a).deriv, abs_of_nonneg (slopeFlattenDeriv_nonneg hε a)]
  exact slopeFlattenDeriv_le hε a

 theorem slopeFlatten_zero (ε : ℝ) : slopeFlatten ε 0 = 0 := by simp [slopeFlatten]
 theorem slopeFlattenDeriv_zero (ε : ℝ) : slopeFlattenDeriv ε 0 = 0 := by simp [slopeFlattenDeriv]
 theorem slopeFlattenFactor_zero (ε : ℝ) : slopeFlattenFactor ε 0 = 0 := by simp [slopeFlattenFactor]

 theorem slopeFlattenFactor_bounds {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    0 ≤ slopeFlattenFactor ε a ∧ slopeFlattenFactor ε a ≤ 1 := by
  unfold slopeFlattenFactor
  exact ⟨div_nonneg (sq_nonneg _) (slopeFlatten_den_pos hε a).le,
    (div_le_one (slopeFlatten_den_pos hε a)).mpr (le_add_of_nonneg_right (sq_nonneg ε))⟩

 theorem slopeFlattenFactor_continuous {ε : ℝ} (hε : 0 < ε) :
    Continuous (slopeFlattenFactor ε) := by
  unfold slopeFlattenFactor
  exact (continuous_id.pow 2).div ((continuous_id.pow 2).add continuous_const)
    (fun a => ne_of_gt (slopeFlatten_den_pos hε a))

 theorem slopeFlatten_eq_factor (ε a : ℝ) :
    slopeFlatten ε a = slopeFlattenFactor ε a * a := by
  unfold slopeFlatten slopeFlattenFactor
  ring

 theorem slopeFlattenFactor_tendsto {εs : ℕ → ℝ} (hε : Tendsto εs atTop (𝓝 0)) (a : ℝ) :
    Tendsto (fun i => slopeFlattenFactor (εs i) a) atTop (𝓝 (if a = 0 then 0 else 1)) := by
  by_cases ha : a = 0
  · simp only [ha, slopeFlattenFactor_zero, ite_true]
    exact tendsto_const_nhds
  · simp only [ha, ite_false, slopeFlattenFactor]
    have hden : Tendsto (fun i => a ^ 2 + εs i ^ 2) atTop (𝓝 (a ^ 2)) := by
      simpa using tendsto_const_nhds.add (hε.pow 2)
    have ht := (tendsto_const_nhds (x := a ^ 2)).div hden (pow_ne_zero 2 ha)
    change Tendsto (fun i => a ^ 2 / (a ^ 2 + εs i ^ 2)) atTop (𝓝 (a ^ 2 / a ^ 2)) at ht
    rwa [div_self (pow_ne_zero 2 ha)] at ht

 theorem slopeFlattenDeriv_tendsto {εs : ℕ → ℝ} (hε : Tendsto εs atTop (𝓝 0)) (a : ℝ) :
    Tendsto (fun i => slopeFlattenDeriv (εs i) a) atTop (𝓝 (if a = 0 then 0 else 1)) := by
  by_cases ha : a = 0
  · simp only [ha, slopeFlattenDeriv_zero, ite_true]
    exact tendsto_const_nhds
  · simp only [ha, ite_false, slopeFlattenDeriv]
    have hnum : Tendsto (fun i => a ^ 4 + 3 * a ^ 2 * εs i ^ 2) atTop (𝓝 (a ^ 4)) := by
      simpa using tendsto_const_nhds.add ((hε.pow 2).const_mul (3 * a ^ 2))
    have hden : Tendsto (fun i => (a ^ 2 + εs i ^ 2) ^ 2) atTop (𝓝 (a ^ 4)) := by
      convert (tendsto_const_nhds.add (hε.pow 2)).pow 2 using 1
      simp [← pow_mul]
    have ht := hnum.div hden (pow_ne_zero 4 ha)
    change Tendsto (fun i => (a ^ 4 + 3 * a ^ 2 * εs i ^ 2) / (a ^ 2 + εs i ^ 2) ^ 2)
      atTop (𝓝 (a ^ 4 / a ^ 4)) at ht
    rwa [div_self (pow_ne_zero 4 ha)] at ht

end Flatten

section SlopeLocality
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X)

 theorem IsRelaxedSlope.cut_zero {f G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ f G) :
    ∃ H : Lp ℝ 2 μ, IsRelaxedSlope μ f H ∧
      ∀ᵐ x ∂μ, H x = if f x = 0 then 0 else G x := by
  let ε (i : ℕ) : ℝ := (1 / 2 : ℝ) ^ i
  have hε (i : ℕ) : 0 < ε i := pow_pos (by norm_num) i
  have heps : Tendsto ε atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  let η (x : X) : ℝ := if f x = 0 then 0 else 1
  have hη : Measurable η := measurable_const.ite
    ((Lp.stronglyMeasurable f).measurable (measurableSet_singleton 0)) measurable_const
  have hηb (x : X) : |η x| ≤ (3 : ℝ≥0) := by dsimp [η]; split_ifs <;> norm_num
  let θ := boundedMultiplier μ η hη 3 hηb
  let H := lpMultiplier μ θ G
  have hH : ∀ᵐ x ∂μ, H x = if f x = 0 then 0 else G x := by
    filter_upwards [lpMultiplier_coe μ θ G, boundedMultiplier_coe μ η hη 3 hηb] with x hx ht
    change lpMultiplier μ θ G x = _
    rw [hx, show θ x = η x from ht]
    dsimp [η]; split_ifs <;> simp
  refine ⟨H, ?_, hH⟩
  let us (i : ℕ) := (slopeFlatten_lipschitz (hε i)).compLp (slopeFlatten_zero _) f
  let ηs (i : ℕ) (x : X) : ℝ := |slopeFlattenDeriv (ε i) (f x)|
  have hs (i : ℕ) : Measurable (ηs i) :=
    ((slopeFlattenDeriv_continuous (hε i)).measurable.comp (Lp.stronglyMeasurable f).measurable).abs
  have hsb (i : ℕ) (x : X) : |ηs i x| ≤ (3 : ℝ≥0) := by
    simp only [ηs, abs_of_nonneg (slopeFlattenDeriv_nonneg (hε i) (f x))]
    exact slopeFlattenDeriv_le (hε i) (f x)
  let Gs (i : ℕ) := lpMultiplier μ (boundedMultiplier μ (ηs i) (hs i) 3 (hsb i)) G
  have hrel (i : ℕ) : IsRelaxedSlope μ (us i) (Gs i) :=
    hG.comp_C1 μ (slopeFlatten_lipschitz (hε i)) (slopeFlatten_zero _)
      (slopeFlattenDeriv_continuous (hε i)) (slopeFlatten_deriv (hε i)) 3
      (fun a => by
        rw [abs_of_nonneg (slopeFlattenDeriv_nonneg (hε i) a)]
        exact slopeFlattenDeriv_le (hε i) a)
  have hGt : Tendsto Gs atTop (𝓝 H) := by
    apply lpMultiplier_tendsto_of_ae μ G ηs η hs hη 3 hsb hηb
    apply Eventually.of_forall
    intro x
    have ht := (slopeFlattenDeriv_tendsto heps (f x)).abs
    convert ht using 1
    dsimp [η]; split_ifs <;> norm_num
  have hut : Tendsto us atTop (𝓝 f) := by
    let qs (i : ℕ) (x : X) := slopeFlattenFactor (ε i) (f x)
    have hqs (i : ℕ) : Measurable (qs i) :=
      (slopeFlattenFactor_continuous (hε i)).measurable.comp (Lp.stronglyMeasurable f).measurable
    have hqb (i : ℕ) (x : X) : |qs i x| ≤ (3 : ℝ≥0) := by
      rw [abs_of_nonneg (slopeFlattenFactor_bounds (hε i) (f x)).1]
      exact (slopeFlattenFactor_bounds (hε i) (f x)).2.trans (by norm_num)
    have hid (i : ℕ) : us i = lpMultiplier μ (boundedMultiplier μ (qs i) (hqs i) 3 (hqb i)) f := by
      apply Lp.ext
      filter_upwards [(slopeFlatten_lipschitz (hε i)).coeFn_compLp (slopeFlatten_zero _) f,
        lpMultiplier_coe μ (boundedMultiplier μ (qs i) (hqs i) 3 (hqb i)) f,
        boundedMultiplier_coe μ (qs i) (hqs i) 3 (hqb i)] with x hx hy hz
      change (slopeFlatten_lipschitz (hε i)).compLp (slopeFlatten_zero _) f x = _
      rw [hx, hy, hz]
      exact slopeFlatten_eq_factor _ _
    have hlimid : lpMultiplier μ θ f = f := by
      apply Lp.ext
      filter_upwards [lpMultiplier_coe μ θ f, boundedMultiplier_coe μ η hη 3 hηb] with x hx hy
      rw [hx, show θ x = η x from hy]
      dsimp [η]; split_ifs with hx0 <;> simp [hx0]
    have ht := lpMultiplier_tendsto_of_ae μ f qs η hqs hη 3 hqb hηb
      (Eventually.of_forall fun x => slopeFlattenFactor_tendsto heps (f x))
    convert ht using 1
    · exact funext hid
    · rw [hlimid]
  exact IsRelaxedSlope.of_tendsto μ hrel hut hGt

variable [ProperSpace X] (hQ : QuadraticCheegerEnergy μ)

 
 theorem SobolevSpace.minimalSlope_zero_on_zero (f : SobolevSpace μ hQ) :
    ∀ᵐ x ∂μ, SobolevSpace.toLp μ hQ f x = 0 → SobolevSpace.minimalSlope μ hQ f x = 0 := by
  obtain ⟨H, hH, hHa⟩ := (SobolevSpace.minimalSlope_isRelaxed μ hQ f).cut_zero μ
  have hle := (Lp.coeFn_le _ _).mpr (SobolevSpace.minimalSlope_le μ hQ f hH)
  have hnon := Lp.coeFn_nonneg _ |>.mpr (SobolevSpace.minimalSlope_nonneg μ hQ f)
  filter_upwards [hle, hnon, hHa] with x hx hn he
  intro hz
  rw [hz, ite_eq_left rfl] at he
  exact le_antisymm (he ▸ hx) hn

end SlopeLocality

section CompConvergence
variable {X : Type u} [MeasurableSpace X] (μ : Measure X)

 theorem lipschitz_comp_quotient_bound {φ : ℝ → ℝ} {C : ℝ≥0}
    (hφ : LipschitzWith C φ) (hφ0 : φ 0 = 0) (a : ℝ) : |φ a / a| ≤ C := by
  by_cases ha : a = 0
  · simp only [ha, div_zero, abs_zero]; exact C.coe_nonneg
  rw [abs_div, div_le_iff₀ (abs_pos.mpr ha)]
  simpa only [Real.dist_eq, hφ0, sub_zero] using hφ.dist_le_mul a 0

 

 theorem compLp_tendsto_of_pointwise {φs : ℕ → ℝ → ℝ} {φ : ℝ → ℝ} {C : ℝ≥0}
    (hs : ∀ i, LipschitzWith C (φs i)) (hφ : LipschitzWith C φ)
    (hz : ∀ i, φs i 0 = 0) (hφ0 : φ 0 = 0)
    (ht : ∀ a, Tendsto (fun i => φs i a) atTop (𝓝 (φ a))) (f : Lp ℝ 2 μ) :
    Tendsto (fun i => (hs i).compLp (hz i) f) atTop (𝓝 (hφ.compLp hφ0 f)) := by
  let ηs (i : ℕ) (x : X) := φs i (f x) / f x
  let η (x : X) := φ (f x) / f x
  have hηs (i : ℕ) : Measurable (ηs i) :=
    ((hs i).continuous.measurable.comp (Lp.stronglyMeasurable f).measurable).div
      (Lp.stronglyMeasurable f).measurable
  have hη : Measurable η :=
    (hφ.continuous.measurable.comp (Lp.stronglyMeasurable f).measurable).div
      (Lp.stronglyMeasurable f).measurable
  have hb (i : ℕ) (x : X) : |ηs i x| ≤ C := lipschitz_comp_quotient_bound (hs i) (hz i) (f x)
  have hbη (x : X) : |η x| ≤ C := lipschitz_comp_quotient_bound hφ hφ0 (f x)
  have hid (i : ℕ) : (hs i).compLp (hz i) f =
      lpMultiplier μ (boundedMultiplier μ (ηs i) (hηs i) C (hb i)) f := by
    apply Lp.ext
    filter_upwards [(hs i).coeFn_compLp (hz i) f,
      lpMultiplier_coe μ (boundedMultiplier μ (ηs i) (hηs i) C (hb i)) f,
      boundedMultiplier_coe μ (ηs i) (hηs i) C (hb i)] with x hx hy he
    rw [hx, hy, he]
    dsimp [ηs]
    by_cases hfx : f x = 0
    · simp [hfx, hz i]
    · rw [div_mul_cancel₀ _ hfx]
  have hlim : hφ.compLp hφ0 f = lpMultiplier μ (boundedMultiplier μ η hη C hbη) f := by
    apply Lp.ext
    filter_upwards [hφ.coeFn_compLp hφ0 f,
      lpMultiplier_coe μ (boundedMultiplier μ η hη C hbη) f,
      boundedMultiplier_coe μ η hη C hbη] with x hx hy he
    rw [hx, hy, he]
    dsimp [η]
    by_cases hfx : f x = 0
    · simp [hfx, hφ0]
    · rw [div_mul_cancel₀ _ hfx]
  simp_rw [hid, hlim]
  apply lpMultiplier_tendsto_of_ae μ f ηs η hηs hη C hb hbη
  exact Eventually.of_forall fun x => (ht (f x)).div_const (f x)

end CompConvergence

variable {X : Type u} [MetricSpace X] [MeasurableSpace X] (μ : Measure X)

 theorem IsRelaxedSlope.neg {f G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ f G) :
    IsRelaxedSlope μ (-f) G := by
  obtain ⟨us, gs, Gs, hl, ha, hm, hu, hG⟩ := hG
  refine ⟨fun i => -us i, fun i x => -gs i x, Gs, ?_, ?_, ?_, hu.neg, hG⟩
  · intro i
    obtain ⟨C, hC⟩ := hl i
    exact ⟨C, hC.neg⟩
  · intro i
    filter_upwards [Lp.coeFn_neg (us i), ha i] with x hx hy
    simpa only [Pi.neg_apply, hy] using hx
  · intro i
    filter_upwards [hm i] with x hx
    refine ⟨hx.1, ?_⟩
    have hid : localSlope (fun x => -gs i x) x = localSlope (gs i) x := by
      unfold localSlope
      simp only [neg_sub_neg, abs_sub_comm (gs i x)]
    rw [hid]
    exact hx.2

variable [BorelSpace X] (hQ : QuadraticCheegerEnergy μ)

 theorem SobolevSpace.minimalSlope_neg (f : SobolevSpace μ hQ) :
    SobolevSpace.minimalSlope μ hQ (-f) = SobolevSpace.minimalSlope μ hQ f := by
  apply IsRelaxedSlope.unique_minimizer μ (SobolevSpace.minimalSlope_isRelaxed μ hQ (-f))
  · simpa only [map_neg] using (SobolevSpace.minimalSlope_isRelaxed μ hQ f).neg μ
  · exact SobolevSpace.minimalSlope_norm_sq μ hQ (-f)
  · rw [SobolevSpace.minimalSlope_norm_sq μ hQ f]
    change 2 * SobolevSpace.energy μ hQ f = 2 * SobolevSpace.energy μ hQ (-f)
    rw [← neg_one_smul ℝ f, SobolevSpace.energy_smul]
    norm_num

variable [ProperSpace X]

 theorem SobolevSpace.minimalSlope_sub_le (f g : SobolevSpace μ hQ) :
    SobolevSpace.minimalSlope μ hQ (f-g) ≤
      SobolevSpace.minimalSlope μ hQ f + SobolevSpace.minimalSlope μ hQ g := by
  simpa only [sub_eq_add_neg, SobolevSpace.minimalSlope_neg] using
    SobolevSpace.minimalSlope_add_le μ hQ f (-g)

 
 theorem SobolevSpace.minimalSlope_eq_on_eq (f g : SobolevSpace μ hQ) :
    ∀ᵐ x ∂μ, SobolevSpace.toLp μ hQ f x = SobolevSpace.toLp μ hQ g x →
      SobolevSpace.minimalSlope μ hQ f x = SobolevSpace.minimalSlope μ hQ g x := by
  have hf := SobolevSpace.minimalSlope_add_le μ hQ (f-g) g
  rw [sub_add_cancel] at hf
  have hg := SobolevSpace.minimalSlope_add_le μ hQ (g-f) f
  rw [sub_add_cancel] at hg
  have hneg : SobolevSpace.minimalSlope μ hQ (g-f) = SobolevSpace.minimalSlope μ hQ (f-g) := by
    rw [← neg_sub f g, SobolevSpace.minimalSlope_neg]
  rw [hneg] at hg
  have hz := SobolevSpace.minimalSlope_zero_on_zero μ hQ (f-g)
  simp only [map_sub] at hz
  filter_upwards [(Lp.coeFn_le _ _).mpr hf, (Lp.coeFn_le _ _).mpr hg, hz,
    Lp.coeFn_add (SobolevSpace.minimalSlope μ hQ (f-g)) (SobolevSpace.minimalSlope μ hQ g),
    Lp.coeFn_add (SobolevSpace.minimalSlope μ hQ (f-g)) (SobolevSpace.minimalSlope μ hQ f),
    Lp.coeFn_sub (SobolevSpace.toLp μ hQ f) (SobolevSpace.toLp μ hQ g)]
    with x hx hy hz he he' hs
  intro hfg
  have hdz : SobolevSpace.minimalSlope μ hQ (f-g) x = 0 := hz (by rw [hs, Pi.sub_apply, hfg, sub_self])
  rw [he, Pi.add_apply, hdz, zero_add] at hx
  rw [he', Pi.add_apply, hdz, zero_add] at hy
  exact le_antisymm hx hy

 
 theorem SobolevSpace.minimalSlope_sub_norm_le (f g : SobolevSpace μ hQ) :
    ‖SobolevSpace.minimalSlope μ hQ f - SobolevSpace.minimalSlope μ hQ g‖ ≤
      ‖SobolevSpace.minimalSlope μ hQ (f-g)‖ := by
  apply norm_le_norm_of_abs_le_abs
  rw [abs_of_nonneg (SobolevSpace.minimalSlope_nonneg μ hQ (f-g))]
  apply abs_le'.mpr
  constructor
  · have h := SobolevSpace.minimalSlope_add_le μ hQ (f-g) g
    rw [sub_add_cancel] at h
    exact sub_le_iff_le_add.mpr h
  · rw [neg_sub]
    have h := SobolevSpace.minimalSlope_add_le μ hQ (g-f) f
    rw [sub_add_cancel, ← neg_sub f g, SobolevSpace.minimalSlope_neg] at h
    exact sub_le_iff_le_add.mpr h

end RegularPointCoordinates

end OAI
