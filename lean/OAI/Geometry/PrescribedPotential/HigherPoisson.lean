import Mathlib
import OAI.Geometry.PrescribedPotential.BoundedPoisson
import OAI.Geometry.PrescribedPotential.HigherResolvent
import OAI.Geometry.PrescribedPotential.PatchCutoffs

namespace OAI

/-! Higher Poisson. -/

section

 
noncomputable section
open Set Filter Topology
open scoped ContDiff Classical
namespace LinearNormalization
variable {U V W : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
lemma feedback_lift (q : V →L[ℝ] U) (p : W →L[ℝ] V) (r : W →L[ℝ] U)
    (T : U →L[ℝ] U) (S : V →L[ℝ] V) (C : U →L[ℝ] U) (K : W →L[ℝ] W)
    (R : U →L[ℝ] U) (R' : V →L[ℝ] W) (a : ℝ)
    (hp : ∀ x, q (p x) = r x) (hS : ∀ x, q (S x) = T (q x))
    (hK : ∀ x, r (K x) = C (r x)) (hR : ∀ x, r (R' x) = R (q x))
    (hT : ∀ x, T x = -x - C x + a • R (T x)) (x : W) :
    r (-x - K x + a • R' (S (p x))) = T (r x) := by
  rw [map_add, map_sub, map_neg, map_smul, hK, hR, hS, hp]
  exact (hT _).symm
end LinearNormalization

namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

omit [ConnectedSpace X] in
lemma resolventGain_order (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1) (k : ℕ) :
    ∃ R : D.localizers.Sobolev (k : ℝ) →L[ℝ] D.localizers.Sobolev ((k : ℝ)+1),
      ∀ f, D.localizers.lower ((k : ℝ)+1) 0 (R f) =
        D.resolventZero m hm he (D.localizers.lower (k : ℝ) 0 f) := by
  obtain ⟨R,hR⟩ := D.completedResolvent_order m hm he k
  refine ⟨D.localizers.lower ((k : ℝ)+2) ((k : ℝ)+1) ∘L R, fun f => ?_⟩
  simp only [ContinuousLinearMap.comp_apply]
  rw [D.localizers.lower_lower (by linarith : (k : ℝ)+1 ≤ (k : ℝ)+2) (by positivity : (0:ℝ) ≤ (k : ℝ)+1)]
  rw [← D.localizers.lower_lower (by linarith [Nat.cast_nonneg (α := ℝ) k] : (2:ℝ) ≤ (k : ℝ)+2)
    (by norm_num : (0:ℝ) ≤ 2), hR]
  rfl

def poissonCorrectionOrder (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (P : D.localizers.ConstantProjection) (s : ℝ) :
    D.localizers.Sobolev s →L[ℝ] D.localizers.Sobolev s :=
  D.localizers.constantsOrder s ∘L D.poissonResidue m hm he P ∘L D.localizers.lower s 0

lemma poissonCorrectionOrder_lower (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (P : D.localizers.ConstantProjection) {s : ℝ} (hs : 0 ≤ s) (f : D.localizers.Sobolev s) :
    D.localizers.lower s 0 (D.poissonCorrectionOrder m hm he P s f) =
      P.proj (D.poissonInput m hm he P (D.localizers.lower s 0 f)) := by
  change D.localizers.lower s 0 (D.localizers.embed s (Smooth.const
    (P.coefficient (D.poissonInput m hm he P (D.localizers.lower s 0 f))))) = _
  rw [D.localizers.lower_embed hs]
  exact P.coefficient_spec _

lemma poissonInput_step (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (P : D.localizers.ConstantProjection) (k : ℕ)
    (W : D.localizers.Sobolev (k : ℝ) →L[ℝ] D.localizers.Sobolev (k : ℝ))
    (hW : ∀ f, D.localizers.lower (k : ℝ) 0 (W f) =
      D.poissonInput m hm he P (D.localizers.lower (k : ℝ) 0 f)) :
    ∃ V : D.localizers.Sobolev ((k : ℝ)+1) →L[ℝ] D.localizers.Sobolev ((k : ℝ)+1),
      ∀ f, D.localizers.lower ((k : ℝ)+1) 0 (V f) =
        D.poissonInput m hm he P (D.localizers.lower ((k : ℝ)+1) 0 f) := by
  obtain ⟨R,hR⟩ := D.resolventGain_order m hm he k
  let W' : D.localizers.Sobolev ((k : ℝ)+1) →L[ℝ] D.localizers.Sobolev ((k : ℝ)+1) :=
    -ContinuousLinearMap.id ℝ _ -
      D.poissonCorrectionOrder m hm he P ((k : ℝ)+1) +
      (m^2 : ℝ) • (R ∘L W ∘L D.localizers.lower ((k : ℝ)+1) (k : ℝ))
  refine ⟨W', fun f => ?_⟩
  change D.localizers.lower ((k : ℝ)+1) 0
    (-f - D.poissonCorrectionOrder m hm he P ((k : ℝ)+1) f +
     (m^2 : ℝ) • R (W (D.localizers.lower ((k : ℝ)+1) (k : ℝ) f))) = _
  apply LinearNormalization.feedback_lift
    (D.localizers.lower (k : ℝ) 0) (D.localizers.lower ((k : ℝ)+1) (k : ℝ))
    (D.localizers.lower ((k : ℝ)+1) 0) (D.poissonInput m hm he P) W
    (P.proj ∘L D.poissonInput m hm he P)
    (D.poissonCorrectionOrder m hm he P ((k : ℝ)+1))
    (D.resolventZero m hm he) R (m^2)
  · exact fun f => D.localizers.lower_lower (by linarith : (k : ℝ) ≤ (k : ℝ)+1)
      (Nat.cast_nonneg k) f
  · exact hW
  · exact D.poissonCorrectionOrder_lower m hm he P (by positivity : (0:ℝ) ≤ (k : ℝ)+1)
  · exact hR
  · exact D.poissonInput_equation m hm he P

 

theorem poissonInput_order (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (P : D.localizers.ConstantProjection) (k : ℕ) :
    ∃ W : D.localizers.Sobolev (k : ℝ) →L[ℝ] D.localizers.Sobolev (k : ℝ),
      ∀ f, D.localizers.lower (k : ℝ) 0 (W f) =
        D.poissonInput m hm he P (D.localizers.lower (k : ℝ) 0 f) := by
  induction k with
  | zero =>
    rw [Nat.cast_zero]
    refine ⟨D.poissonInput m hm he P, fun f => ?_⟩
    simp only [D.localizers.lower_self, ContinuousLinearMap.id_apply]
  | succ k ih =>
    rw [Nat.cast_succ]
    obtain ⟨W,hW⟩ := ih
    exact D.poissonInput_step m hm he P k W hW

theorem poissonRaw_order (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (P : D.localizers.ConstantProjection) (k : ℕ) :
    ∃ R : D.localizers.Sobolev (k : ℝ) →L[ℝ] D.localizers.Sobolev ((k : ℝ)+2),
      ∀ f, D.localizers.lower ((k : ℝ)+2) 2 (R f) =
        D.poissonRaw m hm he P (D.localizers.lower (k : ℝ) 0 f) := by
  obtain ⟨W,hW⟩ := D.poissonInput_order m hm he P k
  obtain ⟨R,hR⟩ := D.completedResolvent_order m hm he k
  refine ⟨R ∘L W, fun f => ?_⟩
  simp only [ContinuousLinearMap.comp_apply]
  rw [hR, hW]
  rfl

end GluingData
end GlobalElliptic

end
end

end OAI
