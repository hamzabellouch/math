import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! # Multiplication by an arbitrary bounded nonnegative Lipschitz function

Compact recovery of the Sobolev factor supplies globally Lipschitz product
approximants. The multiplier need not become constant outside a compact set.
-/

open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X)

theorem IsRelaxedSlope.mul_bounded_lipschitz {f G : Lp ℝ 2 μ}
    (hG : IsRelaxedSlope μ f G) (p : X)
    {θ : X → ℝ} {C : ℝ≥0} (hθ : LipschitzWith C θ)
    (hn : ∀ x, 0≤θ x)
    (V : Lp ℝ ∞ μ) (hV : V =ᵐ[μ] θ) :
    IsRelaxedSlope μ (lpMultiplier μ V f)
      (lpMultiplier μ V G+(C:ℝ) • lpAbs μ f) := by
  obtain ⟨us,gs,Gs,hl,hs,ha,hm,hu,hc⟩ := hG.compact_recovery μ p
  let ws := fun i => lpMultiplier μ V (us i)
  let ks := fun i x => θ x*gs i x
  let Ws := fun i => lpMultiplier μ V (Gs i)+(C:ℝ) • lpAbs μ (us i)
  refine ⟨ws,ks,Ws,?_,?_,?_,?_,?_⟩
  · intro i
    obtain ⟨D,hD⟩ := hl i
    obtain ⟨A,hA⟩ := (hs i).exists_bound_of_continuous hD.continuous
    let An : ℝ≥0 := ⟨A,(norm_nonneg _).trans (hA p)⟩
    obtain ⟨L,hL⟩ := lipschitz_mul_constant_outside_compact hD hθ 0 (by simpa only [sub_zero] using hs i)
      (show ∀ x, |gs i x|≤An from hA)
    refine ⟨L,?_⟩
    convert hL using 1
    funext x
    exact mul_comm _ _
  · intro i
    filter_upwards [lpMultiplier_coe μ V (us i),ha i,hV] with x hx hy hz
    exact hx.trans (by rw [hy,hz])
  · intro i
    obtain ⟨D,hD⟩ := hl i
    filter_upwards [Lp.coeFn_add (lpMultiplier μ V (Gs i)) ((C:ℝ) • lpAbs μ (us i)),
      lpMultiplier_coe μ V (Gs i),Lp.coeFn_smul (C:ℝ) (lpAbs μ (us i)),
      lpAbs_coe μ (us i),ha i,hm i,hV] with x hadd hmul hsm habs hu hm hv
    change 0≤Ws i x ∧ localSlope (ks i) x≤ENNReal.ofReal (Ws i x)
    have he : Ws i x=θ x*Gs i x+(C:ℝ)*|gs i x| := by
      change (lpMultiplier μ V (Gs i)+(C:ℝ) • lpAbs μ (us i)) x = _
      simp only [hadd,Pi.add_apply,hmul,hsm,Pi.smul_apply,smul_eq_mul,habs,hu,hv]
    rw [he]
    refine ⟨add_nonneg (mul_nonneg (hn x) hm.1) (mul_nonneg C.coe_nonneg (abs_nonneg _)),?_⟩
    calc
      _ ≤ ENNReal.ofReal |θ x| *localSlope (gs i) x+
          ENNReal.ofReal |gs i x| *localSlope θ x :=
        localSlope_mul_le hθ.continuous.continuousAt
          (ne_top_of_le_ne_top ENNReal.coe_ne_top (localSlope_le_of_lipschitz hD x))
      _ ≤ ENNReal.ofReal (θ x)*ENNReal.ofReal (Gs i x)+
          ENNReal.ofReal |gs i x| *ENNReal.ofReal (C:ℝ) := by
        rw [abs_of_nonneg (hn x)]
        exact add_le_add (mul_le_mul' le_rfl hm.2)
          (mul_le_mul' le_rfl (by simpa using localSlope_le_of_lipschitz hθ x))
      _ = _ := by
        rw [←ENNReal.ofReal_mul (hn x),←ENNReal.ofReal_mul (abs_nonneg _),
          ←ENNReal.ofReal_add (mul_nonneg (hn x) hm.1) (mul_nonneg (abs_nonneg _) C.coe_nonneg)]
        congr 1
        ring
  · exact (lpMultiplier μ V).continuous.continuousAt.tendsto.comp hu
  · exact ((lpMultiplier μ V).continuous.continuousAt.tendsto.comp hc).add
      (((lpAbs_continuous μ).continuousAt.tendsto.comp hu).const_smul (C:ℝ))

variable (hQ : QuadraticCheegerEnergy μ)

def SobolevSpace.boundedLipschitzMul (f : SobolevSpace μ hQ) (p : X)
    {θ : X → ℝ} {C B : ℝ≥0} (hθ : LipschitzWith C θ)
    (hb : ∀ x, |θ x|≤B) (hn : ∀ x, 0≤θ x)
    : SobolevSpace μ hQ := by
  let V := boundedMultiplier μ θ hθ.continuous.measurable B hb
  have hV : V =ᵐ[μ] θ := boundedMultiplier_coe μ θ hθ.continuous.measurable B hb
  exact ⟨lpMultiplier μ V (SobolevSpace.toLp μ hQ f),
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (((SobolevSpace.minimalSlope_isRelaxed μ hQ f).mul_bounded_lipschitz μ p hθ hn V hV).energy_le μ)⟩

theorem SobolevSpace.boundedLipschitzMul_coe (f : SobolevSpace μ hQ) (p : X)
    {θ : X → ℝ} {C B : ℝ≥0} (hθ : LipschitzWith C θ)
    (hb : ∀ x, |θ x|≤B) (hn : ∀ x, 0≤θ x) :
    SobolevSpace.toLp μ hQ (f.boundedLipschitzMul μ hQ p hθ hb hn) =ᵐ[μ]
      fun x => θ x*SobolevSpace.toLp μ hQ f x := by
  change lpMultiplier μ (boundedMultiplier μ θ hθ.continuous.measurable B hb)
    (SobolevSpace.toLp μ hQ f) =ᵐ[μ] _
  filter_upwards [lpMultiplier_coe μ (boundedMultiplier μ θ hθ.continuous.measurable B hb)
    (SobolevSpace.toLp μ hQ f),boundedMultiplier_coe μ θ hθ.continuous.measurable B hb] with x hx hy
  exact hx.trans (by rw [hy])

end RegularPointCoordinates

end

end OAI
