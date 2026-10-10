import OAI.Analysis.BoundedHochschild.CochainLimits

namespace OAI

/-!
# Pointwise weak-star compactness for bounded linear maps

This realization keeps the algebra's given predual. Norm bounded closed
families of maps can therefore be used in the right-averaging construction
without a separability hypothesis.
-/

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

variable {M X : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- A linear map viewed as a pointwise weak-star continuous-dual valued
function. No continuity of the original map for the weak-star topology is
required. -/
def weakOperatorImage (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (T : M →L[ℂ] M) :
    M → WeakDual ℂ X := fun a => StrongDual.toWeakDual (e.symm (T a))

lemma weakOperatorImage_injective (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    Function.Injective (weakOperatorImage e) := by
  intro S T h
  ext a
  apply e.symm.injective
  exact congrArg WeakDual.toStrongDual (congrFun h a)

lemma weakOperatorImage_add (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (S T : M →L[ℂ] M) :
    weakOperatorImage e (S + T) = weakOperatorImage e S + weakOperatorImage e T := by
  funext a
  change StrongDual.toWeakDual (e.symm (S a + T a)) = _
  simp only [map_add]
  rfl

lemma weakOperatorImage_real_smul (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (r : ℝ) (T : M →L[ℂ] M) : weakOperatorImage e (r • T) = r • weakOperatorImage e T := by
  funext a
  change StrongDual.toWeakDual (e.symm (r • T a)) = r • StrongDual.toWeakDual (e.symm (T a))
  have hr (b : M) : e.symm (r • b) = r • e.symm b := by
    calc
      _ = e.symm ((r : ℂ) • b) := congrArg e.symm (Complex.coe_smul r b).symm
      _ = (r : ℂ) • e.symm b := by
        rw [e.symm.map_smulₛₗ]
        rw [show (starRingEnd ℂ) (r : ℂ) = (r : ℂ) from Complex.conj_ofReal r]
      _ = r • e.symm b := Complex.coe_smul r (e.symm b)
  rw [hr]
  rfl

/-- The weak-star realization is real linear. -/
def weakOperatorImageLinear (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    (M →L[ℂ] M) →ₗ[ℝ] (M → WeakDual ℂ X) where
  toFun := weakOperatorImage e
  map_add' := weakOperatorImage_add e
  map_smul' := weakOperatorImage_real_smul e

/-- The norm ball of linear maps, expressed by closed pointwise conditions.
The conjugate scalar appears because the chosen predual identification is
conjugate linear. -/
def weakOperatorBall (C : ℝ) : Set (M → WeakDual ℂ X) :=
  {F | (∀ a b, F (a + b) = F a + F b) ∧
    (∀ (z : ℂ) a, F (z • a) = star z • F a) ∧
    ∀ a, ‖WeakDual.toStrongDual (F a)‖ ≤ C * ‖a‖}

lemma weakOperatorImage_mem (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (T : M →L[ℂ] M) {C : ℝ} (hT : ‖T‖ ≤ C) :
    weakOperatorImage e T ∈ weakOperatorBall C := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    apply DFunLike.ext
    intro x
    simp only [weakOperatorImage, map_add]
  · intro z a
    apply DFunLike.ext
    intro x
    simp only [weakOperatorImage, map_smul,
      LinearIsometryEquiv.map_smulₛₗ, starRingEnd_apply]
  · intro a
    change ‖e.symm (T a)‖ ≤ C * ‖a‖
    rw [e.symm.norm_map]
    exact (T.le_opNorm a).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg a))

lemma weakOperatorBall_realize (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {C : ℝ} (hC : 0 ≤ C) {F : M → WeakDual ℂ X}
    (hF : F ∈ weakOperatorBall C) :
    ∃ T : M →L[ℂ] M, ‖T‖ ≤ C ∧ weakOperatorImage e T = F := by
  let L : M →ₗ[ℂ] M :=
    { toFun := fun a => e (WeakDual.toStrongDual (F a))
      map_add' := fun a b => by
        rw [hF.1 a b]
        exact map_add e _ _
      map_smul' := fun z a => by
        rw [hF.2.1 z a]
        change e (star z • WeakDual.toStrongDual (F a)) = _
        simp only [LinearIsometryEquiv.map_smulₛₗ, starRingEnd_apply, star_star,
          RingHom.id_apply] }
  have hb (a : M) : ‖L a‖ ≤ C * ‖a‖ := by
    change ‖e (WeakDual.toStrongDual (F a))‖ ≤ _
    rw [e.norm_map]
    exact hF.2.2 a
  refine ⟨L.mkContinuous C hb, L.mkContinuous_norm_le hC hb, ?_⟩
  funext a
  change StrongDual.toWeakDual (e.symm (e (WeakDual.toStrongDual (F a)))) = F a
  rw [e.symm_apply_apply]
  rfl

lemma weakOperatorBall_isClosed (C : ℝ) :
    IsClosed (weakOperatorBall (M := M) (X := X) C) := by
  have hadd : IsClosed {F : M → WeakDual ℂ X | ∀ a b, F (a + b) = F a + F b} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_eq (continuous_apply (a + b)) ((continuous_apply a).add (continuous_apply b))
  have hsmul : IsClosed {F : M → WeakDual ℂ X |
      ∀ (z : ℂ) a, F (z • a) = star z • F a} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun z => isClosed_iInter fun a =>
      isClosed_eq (continuous_apply (z • a)) ((continuous_apply a).const_smul (star z))
  have hbound : IsClosed {F : M → WeakDual ℂ X |
      ∀ a, ‖WeakDual.toStrongDual (F a)‖ ≤ C * ‖a‖} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro a
    have h := (WeakDual.isClosed_closedBall (0 : StrongDual ℂ X) (C * ‖a‖)).preimage
      (continuous_apply a : Continuous (fun F : M → WeakDual ℂ X => F a))
    convert h using 1
    ext F
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
  exact hadd.inter (hsmul.inter hbound)

theorem weakOperatorBall_isCompact (C : ℝ) :
    IsCompact (weakOperatorBall (M := M) (X := X) C) := by
  have hprod := isCompact_pi_infinite (fun a : M =>
    WeakDual.isCompact_closedBall (0 : StrongDual ℂ X) (C * ‖a‖))
  apply hprod.of_isClosed_subset (weakOperatorBall_isClosed C)
  intro F hF a
  simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using hF.2.2 a

/-- The pointwise weak-star image of an operator norm ball is compact. -/
theorem weakOperatorImage_ball_isCompact (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {C : ℝ} (hC : 0 ≤ C) :
    IsCompact (weakOperatorImage e '' {T : M →L[ℂ] M | ‖T‖ ≤ C}) := by
  have heq : weakOperatorImage e '' {T : M →L[ℂ] M | ‖T‖ ≤ C} = weakOperatorBall C := by
    ext F
    constructor
    · rintro ⟨T, hT, rfl⟩
      exact weakOperatorImage_mem e T hT
    · intro hF
      obtain ⟨T, hT, hTF⟩ := weakOperatorBall_realize e hC hF
      exact ⟨T, hT, hTF⟩
  rw [heq]
  exact weakOperatorBall_isCompact C

end BoundedHochschild.KadisonRingrose

end

end OAI
