import Mathlib
import OAI.Probability.LogConcave.Sampling.ContinuousFirstOrderReply

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
namespace LogConcaveSampling
open scoped RealInnerProductSpace NNReal

theorem quadratic_bounds_on_segment {d : ℕ} {F : Point d → ℝ}
    (hF : ContDiff ℝ 2 F) {a b : ℝ}
    (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ inner ℝ v (fderiv ℝ (gradient F) x v) ∧
      inner ℝ v (fderiv ℝ (gradient F) x v) ≤ b * ‖v‖ ^ 2)
    (x v : Point d) :
    F x + inner ℝ v (gradient F x) + a * ‖v‖ ^ 2 / 2 ≤ F (x + v) ∧
    F (x + v) ≤ F x + inner ℝ v (gradient F x) + b * ‖v‖ ^ 2 / 2 := by
  let f : ℝ → ℝ := fun t => F (x + t • v)
  let g : ℝ → ℝ := fun t => inner ℝ v (gradient F (x + t • v))
  let h : ℝ → ℝ := fun t => inner ℝ v (fderiv ℝ (gradient F) (x + t • v) v)
  have hp : ∀ t : ℝ, HasDerivAt (fun s : ℝ => x + s • v) v t := fun t => by
    convert! (hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const v) using 1
    simp
  have hgF : ContDiff ℝ 1 (gradient F) :=
    (InnerProductSpace.toDual ℝ (Point d)).symm.contDiff.comp
      (hF.fderiv_right (by norm_num))
  have hdg := hgF.differentiable (by norm_num)
  have hf : ∀ t, HasDerivAt f (g t) t := by
    intro t
    have hh := ((hF.differentiable (by norm_num) (x + t • v)).hasFDerivAt).comp_hasDerivAt t (hp t)
    convert! hh using 1
    change inner ℝ v (gradient F (x + t • v)) = fderiv ℝ F (x + t • v) v
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  have hg : ∀ t, HasDerivAt g (h t) t := by
    intro t
    have hh := (hdg (x + t • v)).hasFDerivAt.comp_hasDerivAt t (hp t)
    simpa [g, h, Function.comp_def] using (hasDerivAt_const t v).inner ℝ hh
  have ht := quadratic_bounds_of_hasDerivAt hf hg (fun t => hH (x + t • v) v)
  simpa only [f, g, zero_smul, one_smul, add_zero] using ht

theorem hessian_bounds_of_gradient_lipschitz {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hg : LipschitzWith lam (gradient F)) (x v : Point d) :
    -(lam : ℝ) * ‖v‖ ^ 2 ≤ inner ℝ v (fderiv ℝ (gradient F) x v) ∧
    inner ℝ v (fderiv ℝ (gradient F) x v) ≤ (lam : ℝ) * ‖v‖ ^ 2 := by
  have hb := (fderiv ℝ (gradient F) x).le_of_opNorm_le (norm_fderiv_le_of_lipschitz ℝ hg) v
  have hi := (abs_real_inner_le_norm v (fderiv ℝ (gradient F) x v)).trans
    (mul_le_mul_of_nonneg_left hb (norm_nonneg v))
  rw [abs_le] at hi
  constructor <;> nlinarith [hi.1, hi.2]

theorem quadratic_remainder_of_gradient_lipschitz {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : ContDiff ℝ 2 F) (hg : LipschitzWith lam (gradient F)) (x v : Point d) :
    |F (x + v) - F x - inner ℝ v (gradient F x)| ≤ (lam : ℝ) * ‖v‖ ^ 2 / 2 := by
  have hb := quadratic_bounds_on_segment hF (a := -(lam : ℝ)) (b := lam)
    (hessian_bounds_of_gradient_lipschitz hg) x v
  rw [abs_le]
  constructor <;> linarith [hb.1, hb.2]

end LogConcaveSampling

namespace LogConcaveSampling
open scoped RealInnerProductSpace NNReal

structure Primitive {d : ℕ} (F : Point d → ℝ) (lam : ℝ≥0) : Prop where
  smooth : ContDiff ℝ 2 F
  gradient_lipschitz : LipschitzWith lam (gradient F)

def primitivePotential {d : ℕ} (F : Point d → ℝ) (x : Point d) (r : ℝ) (z : Point d) : ℝ :=
  ‖z‖ ^ 2 / 2 + F (x + r • z)

def modeStep {d : ℕ} (g : Point d → Point d) (x : Point d) (r : ℝ) (z : Point d) : Point d :=
  -r • g (x + r • z)

def modeIterates {d : ℕ} (g : Point d → Point d) (x : Point d) (r : ℝ) (k : ℕ) : Point d :=
  (modeStep g x r)^[k] 0

theorem modeStep_lipschitz {d : ℕ} {g : Point d → Point d} {lam : ℝ≥0}
    (hg : LipschitzWith lam g) (x : Point d) {r : ℝ} (hr : 0 ≤ r) :
    LipschitzWith (lam * (NNReal.mk r hr) ^ 2) (modeStep g x r) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  dsimp [modeStep]
  rw [dist_smul₀, Real.norm_eq_abs, abs_neg, abs_of_nonneg hr]
  have h := hg.dist_le_mul (x + r • z) (x + r • w)
  rw [dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_nonneg hr] at h
  calc
    r * dist (g (x + r • z)) (g (x + r • w)) ≤ r * (lam * (r * dist z w)) :=
      mul_le_mul_of_nonneg_left h hr
    _ = ↑(lam * (NNReal.mk r hr) ^ 2) * dist z w := by simp only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_mk]; ring

theorem exists_mode_with_iteration_bound {d : ℕ} {g : Point d → Point d} {lam : ℝ≥0}
    (hg : LipschitzWith lam g) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam : ℝ) * r ^ 2 < 1) :
    ∃ z₀ : Point d,
      z₀ = -r • g (x + r • z₀) ∧
      (∀ z : Point d, z = -r • g (x + r • z) → z = z₀) ∧
      ‖z₀‖ ≤ r * ‖g x‖ / (1 - (lam : ℝ) * r ^ 2) ∧
      ∀ k : ℕ, ‖modeIterates g x r k - z₀‖ ≤
        ((lam : ℝ) * r ^ 2) ^ k * (r * ‖g x‖) / (1 - (lam : ℝ) * r ^ 2) := by
  let l : ℝ≥0 := lam * (NNReal.mk r hr) ^ 2
  have hl' : l < 1 := by exact_mod_cast hl
  have hc : ContractingWith l (modeStep g x r) := ⟨hl', modeStep_lipschitz hg x hr⟩
  let z₀ := hc.fixedPoint (modeStep g x r)
  refine ⟨z₀, hc.fixedPoint_isFixedPt.symm, ?_, ?_, ?_⟩
  · intro z hz
    exact hc.fixedPoint_unique hz.symm
  · have h := hc.dist_fixedPoint_le 0
    simpa [NNReal.coe_pow, z₀, l, dist_eq_norm, modeStep, norm_smul, abs_of_nonneg hr] using h
  · intro k
    have h := hc.apriori_dist_iterate_fixedPoint_le 0 k
    simpa [NNReal.coe_pow, z₀, modeIterates, l, dist_eq_norm, modeStep, norm_smul, abs_of_nonneg hr,
      mul_comm] using h

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
