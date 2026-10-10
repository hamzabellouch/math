import OAI.Analysis.ModularTheory.DualUnitary

namespace OAI

/-! Scalar multiplication on vector-valued L², for the regular translation
functional calculus in the modular core. -/

noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (μ : Measure ℝ)

lemma boundedVectorLp_mem (b : ℝ → ℂ) (hb : AEStronglyMeasurable b μ)
    (C : ℝ) (hC : ∀ t, ‖b t‖ ≤ C) (f : Lp H 2 μ) :
    MemLp (fun t => b t • f t) 2 μ :=
  (Lp.memLp f).of_le_mul (hb.smul (Lp.aestronglyMeasurable f))
    (Eventually.of_forall fun t => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hC t) (norm_nonneg _))

def boundedVectorLpApply (b : ℝ → ℂ) (hb : AEStronglyMeasurable b μ)
    (C : ℝ) (hC : ∀ t, ‖b t‖ ≤ C) (f : Lp H 2 μ) : Lp H 2 μ :=
  (boundedVectorLp_mem μ b hb C hC f).toLp (fun t => b t • f t)

lemma boundedVectorLpApply_ae (b : ℝ → ℂ) (hb : AEStronglyMeasurable b μ)
    (C : ℝ) (hC : ∀ t, ‖b t‖ ≤ C) (f : Lp H 2 μ) :
    boundedVectorLpApply μ b hb C hC f =ᵐ[μ] fun t => b t • f t :=
  MemLp.coeFn_toLp _

def boundedVectorLpLinear (b : ℝ → ℂ) (hb : AEStronglyMeasurable b μ)
    (C : ℝ) (hC : ∀ t, ‖b t‖ ≤ C) : Lp H 2 μ →ₗ[ℂ] Lp H 2 μ where
  toFun := boundedVectorLpApply μ b hb C hC
  map_add' f g := by
    apply Lp.ext
    filter_upwards [boundedVectorLpApply_ae μ b hb C hC (f + g),
      boundedVectorLpApply_ae μ b hb C hC f,
      boundedVectorLpApply_ae μ b hb C hC g, Lp.coeFn_add f g,
      Lp.coeFn_add (boundedVectorLpApply μ b hb C hC f)
        (boundedVectorLpApply μ b hb C hC g)] with t hfg hf hg ha he
    simp only [hfg, ha, he, Pi.add_apply, hf, hg, smul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [boundedVectorLpApply_ae μ b hb C hC (c • f),
      boundedVectorLpApply_ae μ b hb C hC f, Lp.coeFn_smul c f,
      Lp.coeFn_smul c (boundedVectorLpApply μ b hb C hC f)] with t hcf hf ha he
    simp only [hcf, ha, he, hf, Pi.smul_apply, RingHom.id_apply]
    exact smul_comm _ _ _

def boundedVectorLp (b : ℝ → ℂ) (hb : AEStronglyMeasurable b μ)
    (C : ℝ) (hC : ∀ t, ‖b t‖ ≤ C) : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  (boundedVectorLpLinear μ b hb C hC).mkContinuous C (fun f =>
    Lp.norm_le_mul_norm_of_ae_le_mul (by
      filter_upwards [boundedVectorLpApply_ae μ b hb C hC f] with t ht
      change ‖boundedVectorLpApply μ b hb C hC f t‖ ≤ C * ‖f t‖
      rw [ht, norm_smul]
      exact mul_le_mul_of_nonneg_right (hC t) (norm_nonneg _)))

lemma boundedVectorLp_ae (b : ℝ → ℂ) (hb : AEStronglyMeasurable b μ)
    (C : ℝ) (hC : ∀ t, ‖b t‖ ≤ C) (f : Lp H 2 μ) :
    boundedVectorLp μ b hb C hC f =ᵐ[μ] fun t => b t • f t :=
  boundedVectorLpApply_ae μ b hb C hC f

def vectorLpMultiplier (b : BoundedContinuousFunction ℝ ℂ) : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  boundedVectorLp μ b b.continuous.aestronglyMeasurable ‖b‖ b.norm_coe_le_norm

lemma vectorLpMultiplier_ae (b : BoundedContinuousFunction ℝ ℂ) (f : Lp H 2 μ) :
    vectorLpMultiplier μ b f =ᵐ[μ] fun t => b t • f t := boundedVectorLp_ae μ _ _ _ _ _

lemma vectorLpMultiplier_mul (a b : BoundedContinuousFunction ℝ ℂ) :
    vectorLpMultiplier (H := H) μ (a * b) = vectorLpMultiplier μ a * vectorLpMultiplier μ b := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [vectorLpMultiplier_ae μ (a * b) f,
    vectorLpMultiplier_ae μ a (vectorLpMultiplier μ b f),
    vectorLpMultiplier_ae μ b f] with t hab ha hb
  change (vectorLpMultiplier μ (a * b) f) t =
    (vectorLpMultiplier μ a (vectorLpMultiplier μ b f)) t
  rw [hab, ha, hb]
  exact mul_smul _ _ _

lemma vectorLpMultiplier_one : vectorLpMultiplier (H := H) μ 1 = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  change vectorLpMultiplier μ 1 f = f
  apply Lp.ext
  filter_upwards [vectorLpMultiplier_ae μ 1 f] with t ht
  simpa only [BoundedContinuousFunction.coe_one, Pi.one_apply, one_smul] using ht

variable [CompleteSpace H]

lemma vectorLpMultiplier_star (a : BoundedContinuousFunction ℝ ℂ) :
    vectorLpMultiplier (H := H) μ (star a) = star (vectorLpMultiplier (H := H) μ a) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f g
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [vectorLpMultiplier_ae μ (star a) f,
    vectorLpMultiplier_ae μ a g] with t hf hg
  rw [hf, hg]
  simp only [BoundedContinuousFunction.coe_star, Pi.star_apply,
    inner_smul_left, inner_smul_right, starRingEnd_apply, star_star]

/-- Bounded continuous scalar multipliers on vector-valued L². -/
def vectorLpRepresentation : BoundedContinuousFunction ℝ ℂ →⋆ₐ[ℂ]
    (Lp H 2 μ →L[ℂ] Lp H 2 μ) where
  toFun := vectorLpMultiplier μ
  map_one' := vectorLpMultiplier_one μ
  map_mul' := vectorLpMultiplier_mul μ
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro f
    change vectorLpMultiplier μ 0 f = 0
    apply Lp.ext
    filter_upwards [vectorLpMultiplier_ae μ 0 f, Lp.coeFn_zero (E := H) (p := 2) (μ := μ)]
      with t ht hz
    simpa only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, zero_smul, hz] using ht
  map_add' a b := by
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    filter_upwards [vectorLpMultiplier_ae μ (a + b) f,
      vectorLpMultiplier_ae μ a f, vectorLpMultiplier_ae μ b f,
      Lp.coeFn_add (vectorLpMultiplier μ a f) (vectorLpMultiplier μ b f)] with t hab ha hb he
    change (vectorLpMultiplier μ (a + b) f) t =
      (vectorLpMultiplier μ a f + vectorLpMultiplier μ b f) t
    simp only [hab, he, Pi.add_apply, BoundedContinuousFunction.coe_add]
    rw [ha, hb]
    exact add_smul _ _ _
  commutes' c := by
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    filter_upwards [vectorLpMultiplier_ae μ (algebraMap ℂ _ c) f,
      Lp.coeFn_smul c f] with t ht hc
    change (vectorLpMultiplier μ (algebraMap ℂ _ c) f) t = (c • f) t
    rw [ht, hc]
    rfl
  map_star' := vectorLpMultiplier_star μ

@[simp] lemma vectorLpRepresentation_character (r : ℝ) :
    vectorLpRepresentation (H := H) μ (BoundedRecovery.spectralCharacter r) =
      (modularDualUnitary (H := H) μ r : Lp H 2 μ →L[ℂ] Lp H 2 μ) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [vectorLpMultiplier_ae μ (BoundedRecovery.spectralCharacter r) f,
    modularDual_ae μ r f] with t hm hd
  change (vectorLpMultiplier μ (BoundedRecovery.spectralCharacter r) f) t =
    (modularDual μ r f) t
  rw [hm, hd]

end WeakPureInfiniteness

end

end OAI
