import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingGateJetBounds
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.ResidualExpressions

namespace OAI

/-! Elementary closure rules for globally bounded smooth jets. These
transfer the stage estimates to the actual Navier–Stokes force. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows
open scoped ContDiff BigOperators

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

def UniformJets (f : E → F) : Prop :=
  ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ B

theorem UniformJets.add {f g : E → F} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfb : UniformJets f) (hgb : UniformJets g) : UniformJets (f+g) := by
  intro n
  obtain ⟨A,hA,hAf⟩ := hfb n
  obtain ⟨B,hB,hBg⟩ := hgb n
  refine ⟨A+B, add_nonneg hA hB, fun x => ?_⟩
  rw [iteratedFDeriv_add_apply (hf.contDiffAt.of_le (by simp)) (hg.contDiffAt.of_le (by simp))]
  exact (norm_add_le _ _).trans (add_le_add (hAf x) (hBg x))

theorem UniformJets.const_smul {f : E → F} (hf : ContDiff ℝ ∞ f)
    (hb : UniformJets f) (r : ℝ) : UniformJets (r • f) := by
  intro n
  obtain ⟨A,hA,hAf⟩ := hb n
  refine ⟨|r| * A, mul_nonneg (abs_nonneg _) hA, fun x => ?_⟩
  rw [iteratedFDeriv_const_smul_apply (hf.contDiffAt.of_le (by simp)), norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hAf x) (abs_nonneg _)

theorem UniformJets.sub {f g : E → F} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfb : UniformJets f) (hgb : UniformJets g) : UniformJets (f-g) := by
  have he : f-g = f + (-1 : ℝ) • g := by ext x; simp [sub_eq_add_neg]
  rw [he]
  exact hfb.add hf (hg.const_smul _) (hgb.const_smul hg (-1))

theorem UniformJets.linear_left {f : E → F} (hf : ContDiff ℝ ∞ f)
    (hb : UniformJets f) (L : F →L[ℝ] G) : UniformJets (L ∘ f) := by
  intro n
  obtain ⟨A,hA,hAf⟩ := hb n
  refine ⟨‖L‖*A, mul_nonneg (norm_nonneg _) hA, fun x => ?_⟩
  exact (L.norm_iteratedFDeriv_comp_left (hf.contDiffAt) (by simp)).trans
    (mul_le_mul_of_nonneg_left (hAf x) (norm_nonneg _))

theorem UniformJets.linear_right {f : F → G} (hf : ContDiff ℝ ∞ f)
    (hb : UniformJets f) (L : E →L[ℝ] F) : UniformJets (f ∘ L) := by
  intro n
  obtain ⟨A,hA,hAf⟩ := hb n
  refine ⟨A*‖L‖^n, by positivity, fun x => ?_⟩
  rw [L.iteratedFDeriv_comp_right hf x (by simp)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simpa using mul_le_mul_of_nonneg_right (hAf (L x)) (pow_nonneg (norm_nonneg L) n)

theorem UniformJets.derivative {f : E → F} (hb : UniformJets f) : UniformJets (fderiv ℝ f) := by
  intro n
  obtain ⟨A,hA,hAf⟩ := hb (n+1)
  exact ⟨A,hA, fun x => by simpa only [norm_iteratedFDeriv_fderiv] using hAf x⟩

theorem UniformJets.directional {f : E → F} (hf : ContDiff ℝ ∞ f)
    (hb : UniformJets f) (v : E) : UniformJets (fun x => fderiv ℝ f x v) := by
  intro n
  obtain ⟨A,hA,hAf⟩ := hb.derivative n
  refine ⟨‖v‖*A, mul_nonneg (norm_nonneg _) hA, fun x => ?_⟩
  exact (norm_iteratedFDeriv_clm_apply_const (hf.fderiv_right (m := ∞) (by simp)).contDiffAt
    (by simp)).trans (mul_le_mul_of_nonneg_left (hAf x) (norm_nonneg _))

theorem UniformJets.smul {f : E → ℝ} {g : E → F}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfb : UniformJets f) (hgb : UniformJets g) : UniformJets (fun x => f x • g x) := by
  choose A hA hAf using hfb
  choose B hB hBg using hgb
  intro n
  refine ⟨∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*A i*B (n-i),
    Finset.sum_nonneg (fun i _ => mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (hA i)) (hB (n-i))), fun x => ?_⟩
  apply (norm_iteratedFDeriv_smul_le hf hg x (by simp : (n : ℕ∞ω) ≤ ∞)).trans
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hAf i x) (Nat.cast_nonneg _))
    (hBg (n-i) x) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hA i))

theorem UniformJets.sum {ι : Type*} [Fintype ι] {f : ι → E → F}
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hb : ∀ i, UniformJets (f i)) :
    UniformJets (fun x => ∑ i, f i x) := by
  intro n
  choose B hB hBf using fun i => hb i n
  refine ⟨∑ i, B i, Finset.sum_nonneg (fun i _ => hB i), fun x => ?_⟩
  rw [iteratedFDeriv_fun_sum_apply (fun i _ => (hf i).contDiffAt.of_le (by simp))]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => hBf i x))

end ForcedComputation.VelocityDetector

end

end OAI
