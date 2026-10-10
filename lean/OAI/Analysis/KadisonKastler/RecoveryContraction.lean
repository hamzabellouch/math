import OAI.Analysis.KadisonKastler.TraceNormPerturbation

namespace OAI

/-! # An explicit corner contraction for scalar recovery -/

namespace KadisonKastler

noncomputable section

universe u

variable {B : Type u} [CStarAlgebra B]

local instance recoveryContractionOrder : PartialOrder B := CStarAlgebra.spectralOrder B
local instance recoveryContractionStarOrder : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B

/-- The cutoff whose scaled trace loss is exactly one tenth. -/
def recoveryCutoff (n : ℕ) : ℝ := (10 * (n : ℝ))⁻¹

/-- The compressed square used by the scalar recovery argument. -/
def recoveryCompression (p f : B) : B := p * f * f * p

/-- A concrete contraction obtained from the adjoint of the clipped
polar approximation inside the projection corner. -/
def recoveryContraction (n : ℕ) (p f : B) : B :=
  (recoveryCutoff n)⁻¹ • star (spectralClip (recoveryCutoff n) (recoveryCompression p f))

theorem recoveryCutoff_pos {n : ℕ} (hn : 0 < n) : 0 < recoveryCutoff n := by
  unfold recoveryCutoff
  positivity

theorem recoveryCutoff_mul {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * recoveryCutoff n = 1 / 10 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold recoveryCutoff
  field_simp

/-- The formula has norm at most one. -/
theorem recoveryContraction_norm_le {n : ℕ} (hn : 0 < n) (p f : B) :
    ‖recoveryContraction n p f‖ ≤ 1 := by
  have heq : recoveryContraction n p f =
      star ((recoveryCutoff n)⁻¹ • spectralClip (recoveryCutoff n) (recoveryCompression p f)) := by
    simp only [recoveryContraction, star_smul, star_trivial]
  rw [heq, norm_star]
  exact normalized_spectralClip_norm_le (recoveryCutoff_pos hn) _

/-- The contraction belongs algebraically to the original projection
corner, without any approximation in the support identities. -/
theorem recoveryContraction_support {n : ℕ} (hn : 0 < n)
    (p f : B) (hp : IsStarProjection p) :
    p * recoveryContraction n p f = recoveryContraction n p f ∧
      recoveryContraction n p f * p = recoveryContraction n p f := by
  let A := recoveryCompression p f
  let c := spectralClip (recoveryCutoff n) A
  have hAp : A * p = A := by
    simp only [A, recoveryCompression, mul_assoc, hp.isIdempotentElem.eq]
  have hpA : p * A = A := by
    simp only [A, recoveryCompression, ← mul_assoc, hp.isIdempotentElem.eq]
  have hcp : c * p = c :=
    spectralClip_mul_right_eq (recoveryCutoff_pos hn) A p hAp
  have hpc : p * c = c := by
    change p * (A * cfc (clippingFunction (recoveryCutoff n)) (CFC.abs A)) = _
    rw [← mul_assoc, hpA]
    rfl
  have hpcStar : p * star c = star c := by
    simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star hcp
  have hcStarp : star c * p = star c := by
    simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star hpc
  constructor
  · change p * ((recoveryCutoff n)⁻¹ • star c) = (recoveryCutoff n)⁻¹ • star c
    rw [mul_smul_comm, hpcStar]
  · change ((recoveryCutoff n)⁻¹ • star c) * p = (recoveryCutoff n)⁻¹ • star c
    rw [smul_mul_assoc, hcStarp]

private theorem trace_corner_recovery (τ : FaithfulTracialState B) (p f v : B)
    (hpv : p * v = v) (hvp : v * p = v) :
    τ.toLinearMap (f * v * f) = τ.toLinearMap (v * recoveryCompression p f) := by
  have hl : τ.toLinearMap (f * v * f) = τ.toLinearMap (v * f * f) := by
    rw [mul_assoc, τ.tracial f]
  rw [hl]
  symm
  calc
    τ.toLinearMap (v * recoveryCompression p f) = τ.toLinearMap ((v * f * f) * p) := by
      simp only [recoveryCompression, ← mul_assoc, hvp]
    _ = τ.toLinearMap (p * (v * f * f)) := τ.tracial _ _
    _ = τ.toLinearMap (v * f * f) := by rw [← mul_assoc, ← mul_assoc, hpv]

/-- Fixed positive cutoffs depend continuously on the input element. -/
theorem spectralClip_continuous {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun x : B => spectralClip ε x) := by
  have hc : Continuous (fun x : B => cfc (clippingFunction ε) (CFC.abs x)) := by
    exact Continuous.cfc_of_mem_nhdsSet (s := Set.univ) (clippingFunction ε)
      (by simp) CFC.continuous_abs (fun x => (CFC.abs_nonneg x).isSelfAdjoint)
      (clippingFunction_continuous hε).continuousOn
  exact continuous_id.mul hc

/-- For each fixed corner dimension, the recovery contraction is a
continuous function of the Fourier-polynomial element. -/
theorem recoveryContraction_continuous {n : ℕ} (hn : 0 < n) (p : B) :
    Continuous (recoveryContraction n p) := by
  have hc : Continuous (fun f : B => recoveryCompression p f) := by
    unfold recoveryCompression
    fun_prop
  exact ((spectralClip_continuous (recoveryCutoff_pos hn)).comp hc).star.const_smul _

/-- The continuous cutoff recovers the compressed one-norm with loss
at most `1/10` after scaling by the corner dimension. -/
theorem recoveryContraction_trace_lower_bound (τ : FaithfulTracialState B)
    {n : ℕ} (hn : 0 < n) (p f : B) (hp : IsStarProjection p) :
    (n : ℝ) * traceOneNorm τ (recoveryCompression p f) - 1 / 10 ≤
      (τ.toLinearMap ((n : ℂ) • (f * recoveryContraction n p f * f))).re := by
  have happ := traceOneNorm_le_normalized_spectralClip_pair τ (recoveryCompression p f)
    (recoveryCutoff_pos hn)
  have hv : star ((recoveryCutoff n)⁻¹ • spectralClip (recoveryCutoff n)
      (recoveryCompression p f)) = recoveryContraction n p f := by
    simp only [recoveryContraction, star_smul, star_trivial]
  rw [hv] at happ
  obtain ⟨hpv, hvp⟩ := recoveryContraction_support hn p f hp
  have htrace := trace_corner_recovery τ p f (recoveryContraction n p f) hpv hvp
  have hscale : (τ.toLinearMap ((n : ℂ) • (f * recoveryContraction n p f * f))).re =
      (n : ℝ) * (τ.toLinearMap (recoveryContraction n p f * recoveryCompression p f)).re := by
    rw [map_smul, smul_eq_mul, htrace]
    simp
  rw [hscale]
  have hh := mul_le_mul_of_nonneg_left happ (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  rw [mul_add, recoveryCutoff_mul hn] at hh
  linarith

end

end KadisonKastler

end OAI
