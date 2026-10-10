import Mathlib
import OAI.Probability.LogConcave.LowerBounds.PrefixSpace

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise

namespace LogConcaveSampling.LowerBound

def frameTransport {d : ℕ} (F : Frames d) : Point d ≃ₗᵢ[ℝ] Point d :=
  rotationIsometry (frameCompletion F 1)

@[fun_prop] lemma measurable_frameTransport {d : ℕ} :
    Measurable (fun p : Frames d × Point d => frameTransport p.1 p.2) := by
  have continuous_completion : Continuous
      (fun pair : Frames d × Point d => frameCompletion pair.1 1) := by
    unfold frameCompletion
    exact (continuous_fst.fst.mul continuous_const).mul continuous_fst.snd.inv
  exact ((continuous_rotation_apply (d := d)).comp
    (continuous_completion.prodMk continuous_snd)).measurable

lemma frameCompletion_apply {d : ℕ} (F : Frames d) (H : Rotations d) (x : Point d) :
    rotationIsometry (frameCompletion F H) x =
      rotationIsometry F.1 (rotationIsometry H (rotationIsometry F.2⁻¹ x)) := by
  simp only [frameCompletion, rotationIsometry_mul]

lemma frameCompletion_eq_transport {d : ℕ} (E : Submodule ℝ (Point d))
    (F : Frames d) {H : Rotations d} (hH : H ∈ subspaceStabilizer E)
    {x : Point d} (hx : x ∈ frameSpace F.2 E) :
    rotationIsometry (frameCompletion F H) x = frameTransport F x := by
  rw [frameCompletion_apply, hH _ ((mem_frameSpace F.2 E x).mp hx)]
  simp only [frameTransport, frameCompletion_apply, rotationIsometry_one]

lemma frameTransport_swap {d : ℕ} (F : Frames d) (x : Point d) :
    frameTransport F.swap x = (frameTransport F).symm x := by
  unfold frameTransport
  rw [← rotationIsometry_inv_apply]
  have h : frameCompletion F.swap 1 = (frameCompletion F 1)⁻¹ := by
    simpa only [inv_one] using frameCompletion_swap F 1
  rw [h]

lemma frameCompletion_symm_eq_transport {d : ℕ} (E : Submodule ℝ (Point d))
    (F : Frames d) {H : Rotations d} (hH : H ∈ subspaceStabilizer E)
    {x : Point d} (hx : x ∈ frameSpace F.1 E) :
    (rotationIsometry (frameCompletion F H)).symm x = (frameTransport F).symm x := by
  rw [← rotationIsometry_inv_apply, ← frameCompletion_swap]
  rw [frameCompletion_eq_transport E F.swap ((subspaceStabilizer E).inv_mem hH) hx,
    frameTransport_swap]

lemma frameTransport_preimage_mem {d : ℕ} (E : Submodule ℝ (Point d))
    (F : Frames d) {x : Point d} (hx : x ∈ frameSpace F.1 E) :
    (frameTransport F).symm x ∈ frameSpace F.2 E := by
  rw [mem_frameSpace] at hx ⊢
  rw [← frameTransport_swap, frameTransport, frameCompletion_apply, rotationIsometry_one]
  simp only [rotationIsometry_inv_apply]
  change (rotationIsometry F.2).symm (rotationIsometry F.2 ((rotationIsometry F.1).symm x)) ∈ E
  rw [LinearIsometryEquiv.symm_apply_apply]
  simpa only [rotationIsometry_inv_apply] using hx

lemma extendFrame_relative_mem {d k : ℕ} (hk : k < d) (O : Rotations d) (x : Point d) :
    O⁻¹ * extendFrame hk O x ∈ subspaceStabilizer (prefixSpace d k) := by
  simpa only [extendFrame, inv_mul_cancel_left] using
    (complementSection (prefixSpace d k) (prefixUnit hk)
      (flagDirection hk (rotationIsometry O⁻¹ x))).property

def CompatibleFrames {d : ℕ} (E : Submodule ℝ (Point d)) (F F' : Frames d) : Prop :=
  F.1⁻¹ * F'.1 ∈ subspaceStabilizer E ∧ F.2⁻¹ * F'.2 ∈ subspaceStabilizer E

lemma compatibleFrames_reconstruct {d : ℕ} (E : Submodule ℝ (Point d))
    {F F' : Frames d} (h : CompatibleFrames E F F') {H : Rotations d}
    (hH : H ∈ subspaceStabilizer E) :
    ∃ H' ∈ subspaceStabilizer E, frameCompletion F' H = frameCompletion F H' := by
  refine ⟨(F.1⁻¹*F'.1)*H*(F.2⁻¹*F'.2)⁻¹,
    (subspaceStabilizer E).mul_mem ((subspaceStabilizer E).mul_mem h.1 hH)
      ((subspaceStabilizer E).inv_mem h.2),?_⟩
  unfold frameCompletion
  group

lemma compatibleFrames_inverseUpdate {d k : ℕ} (hk : k < d) (F : Frames d) (x g : Point d) :
    CompatibleFrames (prefixSpace d k) F (inverseFrameUpdate hk F x g) := by
  rw [inverseFrameUpdate_eq]
  exact ⟨extendFrame_relative_mem hk _ _, extendFrame_relative_mem hk _ _⟩

lemma compatibleFrames_forwardUpdate {d k : ℕ} (hk : k < d) (F : Frames d) (y g : Point d) :
    CompatibleFrames (prefixSpace d k) F (forwardFrameUpdate hk F y g) := by
  rw [forwardFrameUpdate_eq]
  exact ⟨extendFrame_relative_mem hk _ _, extendFrame_relative_mem hk _ _⟩

lemma subspaceStabilizer_anti {d : ℕ} {E F : Submodule ℝ (Point d)} (h : E ≤ F) :
    subspaceStabilizer F ≤ subspaceStabilizer E := by
  intro O hO x hx
  exact hO x (h hx)

lemma compatibleFrames_mono {d : ℕ} {E G : Submodule ℝ (Point d)} (h : E ≤ G)
    {F F' : Frames d} (hc : CompatibleFrames G F F') : CompatibleFrames E F F' :=
  ⟨subspaceStabilizer_anti h hc.1, subspaceStabilizer_anti h hc.2⟩

lemma compatibleFrames_trans {d : ℕ} {E : Submodule ℝ (Point d)} {F F' F'' : Frames d}
    (h : CompatibleFrames E F F') (h' : CompatibleFrames E F' F'') :
    CompatibleFrames E F F'' := by
  constructor
  · have hm := (subspaceStabilizer E).mul_mem h.1 h'.1
    simpa only [mul_assoc, mul_inv_cancel_left] using hm
  · have hm := (subspaceStabilizer E).mul_mem h.2 h'.2
    simpa only [mul_assoc, mul_inv_cancel_left] using hm

end LogConcaveSampling.LowerBound

open MeasureTheory ProbabilityTheory

end LowerProof
end
end
end

end OAI
