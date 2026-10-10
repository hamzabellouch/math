import OAI.Analysis.ModularTheory.DualUnitary

namespace OAI

/-! Concrete bounded multipliers on scalar L². These are the actual spectral
cutoffs used in the modular-core weight construction. -/

noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace

namespace WeakPureInfiniteness

variable (μ : Measure ℝ)

lemma boundedScalarLp_mem (b : ℝ → ℂ) (hb : AEStronglyMeasurable b μ)
    (C : ℝ) (hC : ∀ t, ‖b t‖ ≤ C) (f : Lp ℂ 2 μ) :
    MemLp (fun t => b t * f t) 2 μ :=
  (Lp.memLp f).of_le_mul (hb.mul (Lp.aestronglyMeasurable f))
    (Eventually.of_forall fun t => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hC t) (norm_nonneg _))

def boundedScalarLpApply (b : ℝ → ℂ) (hb : AEStronglyMeasurable b μ)
    (C : ℝ) (hC : ∀ t, ‖b t‖ ≤ C) (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (boundedScalarLp_mem μ b hb C hC f).toLp (fun t => b t * f t)

lemma boundedScalarLpApply_ae (b : ℝ → ℂ) (hb : AEStronglyMeasurable b μ)
    (C : ℝ) (hC : ∀ t, ‖b t‖ ≤ C) (f : Lp ℂ 2 μ) :
    boundedScalarLpApply μ b hb C hC f =ᵐ[μ] fun t => b t * f t :=
  MemLp.coeFn_toLp _

def boundedScalarLpLinear (b : ℝ → ℂ) (hb : AEStronglyMeasurable b μ)
    (C : ℝ) (hC : ∀ t, ‖b t‖ ≤ C) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun := boundedScalarLpApply μ b hb C hC
  map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [boundedScalarLpApply_ae μ b hb C hC (f + g),
          boundedScalarLpApply_ae μ b hb C hC f,
          boundedScalarLpApply_ae μ b hb C hC g, Lp.coeFn_add f g,
          Lp.coeFn_add (boundedScalarLpApply μ b hb C hC f)
            (boundedScalarLpApply μ b hb C hC g)] with t hfg hf hg ha he
        simp only [hfg, ha, he, Pi.add_apply, hf, hg, mul_add]
  map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [boundedScalarLpApply_ae μ b hb C hC (c • f),
          boundedScalarLpApply_ae μ b hb C hC f, Lp.coeFn_smul c f,
          Lp.coeFn_smul c (boundedScalarLpApply μ b hb C hC f)] with t hcf hf ha he
        simp only [hcf, ha, he, hf, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring

def boundedScalarLp (b : ℝ → ℂ) (hb : AEStronglyMeasurable b μ)
    (C : ℝ) (hC : ∀ t, ‖b t‖ ≤ C) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous (boundedScalarLpLinear μ b hb C hC)
    C (fun f => Lp.norm_le_mul_norm_of_ae_le_mul (by
      filter_upwards [boundedScalarLpApply_ae μ b hb C hC f] with t ht
      change ‖(boundedScalarLpApply μ b hb C hC f) t‖ ≤ C * ‖f t‖
      rw [ht, norm_mul]
      exact mul_le_mul_of_nonneg_right (hC t) (norm_nonneg _)))

lemma boundedScalarLp_ae (b : ℝ → ℂ) (hb : AEStronglyMeasurable b μ)
    (C : ℝ) (hC : ∀ t, ‖b t‖ ≤ C) (f : Lp ℂ 2 μ) :
    boundedScalarLp μ b hb C hC f =ᵐ[μ] fun t => b t * f t :=
  boundedScalarLpApply_ae μ b hb C hC f

lemma boundedScalarLp_norm_le (b : ℝ → ℂ) (hb : AEStronglyMeasurable b μ)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ t, ‖b t‖ ≤ C) :
    ‖boundedScalarLp μ b hb C hC‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC0 _

def scalarLpMultiplier (b : BoundedContinuousFunction ℝ ℂ) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  boundedScalarLp μ b b.continuous.aestronglyMeasurable ‖b‖ b.norm_coe_le_norm

lemma scalarLpMultiplier_ae (b : BoundedContinuousFunction ℝ ℂ) (f : Lp ℂ 2 μ) :
    scalarLpMultiplier μ b f =ᵐ[μ] fun t => b t * f t := boundedScalarLp_ae μ _ _ _ _ _

lemma scalarLpMultiplier_mul (a b : BoundedContinuousFunction ℝ ℂ) :
    scalarLpMultiplier μ (a * b) = scalarLpMultiplier μ a * scalarLpMultiplier μ b := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [scalarLpMultiplier_ae μ (a * b) f,
    scalarLpMultiplier_ae μ a (scalarLpMultiplier μ b f),
    scalarLpMultiplier_ae μ b f] with t hab ha hb
  change (scalarLpMultiplier μ (a * b) f) t =
    (scalarLpMultiplier μ a (scalarLpMultiplier μ b f)) t
  rw [hab, ha, hb]
  exact mul_assoc _ _ _

lemma scalarLpMultiplier_one : scalarLpMultiplier μ 1 = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  change scalarLpMultiplier μ 1 f = f
  apply Lp.ext
  filter_upwards [scalarLpMultiplier_ae μ 1 f] with t ht
  simpa only [BoundedContinuousFunction.coe_one, Pi.one_apply, one_mul] using ht

lemma scalarLpMultiplier_star (a : BoundedContinuousFunction ℝ ℂ) :
    scalarLpMultiplier μ (star a) = star (scalarLpMultiplier μ a) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f g
  simp only [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [scalarLpMultiplier_ae μ (star a) f,
    scalarLpMultiplier_ae μ a g] with t hf hg
  rw [hf, hg]
  simp only [RCLike.inner_apply, BoundedContinuousFunction.coe_star, Pi.star_apply,
    map_mul, starRingEnd_apply, star_star]
  ring

/-- Multiplication by bounded continuous scalar functions on actual L². -/
def scalarLpRepresentation : BoundedContinuousFunction ℝ ℂ →⋆ₐ[ℂ]
    (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) where
  toFun := scalarLpMultiplier μ
  map_one' := scalarLpMultiplier_one μ
  map_mul' := scalarLpMultiplier_mul μ
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro f
    change scalarLpMultiplier μ 0 f = 0
    apply Lp.ext
    filter_upwards [scalarLpMultiplier_ae μ 0 f, (Lp.coeFn_zero (E := ℂ) (p := 2) (μ := μ))]
      with t ht hz
    simpa only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, zero_mul, hz] using ht
  map_add' a b := by
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    filter_upwards [scalarLpMultiplier_ae μ (a + b) f,
      scalarLpMultiplier_ae μ a f, scalarLpMultiplier_ae μ b f,
      Lp.coeFn_add (scalarLpMultiplier μ a f) (scalarLpMultiplier μ b f)] with t hab ha hb he
    change (scalarLpMultiplier μ (a + b) f) t =
      (scalarLpMultiplier μ a f + scalarLpMultiplier μ b f) t
    simp only [hab, he, Pi.add_apply, BoundedContinuousFunction.coe_add]
    rw [ha, hb]
    exact add_mul _ _ _
  commutes' c := by
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    filter_upwards [scalarLpMultiplier_ae μ (algebraMap ℂ _ c) f,
      Lp.coeFn_smul c f] with t ht hc
    change (scalarLpMultiplier μ (algebraMap ℂ _ c) f) t = (c • f) t
    rw [ht, hc]
    rfl
  map_star' := scalarLpMultiplier_star μ

@[simp] lemma scalarLpRepresentation_character (r : ℝ) :
    scalarLpRepresentation μ (BoundedRecovery.spectralCharacter r) =
      (modularDualUnitary (H := ℂ) μ r : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [scalarLpMultiplier_ae μ (BoundedRecovery.spectralCharacter r) f,
    modularDual_ae μ r f] with t hm hd
  change (scalarLpMultiplier μ (BoundedRecovery.spectralCharacter r) f) t =
    (modularDual μ r f) t
  rw [hm, hd]
  rfl

end WeakPureInfiniteness

end

end OAI
