import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLinearization
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousDuhamelRestart

namespace OAI

/-! # Quantitative bounds for the true whole-space linearized evolution

The Bielecki argument already constructs the mild trajectories. Its fixed
point estimate gives a data bound on every finite slab, for the actual
bounded real-linear derivative of the odd-power potential.
-/

open Set

namespace DefocusingNLS

attribute [local irreducible] homogeneousFreeOperator

private theorem homogeneousPotentialBielecki_zero_norm_le
    (a b k T η : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (hT : 0 ≤ T) (hη : 0 ≤ η)
    (B : HomogeneousY a k →L[ℝ] HomogeneousY a k) (u₀ : HomogeneousY a k) :
    ‖homogeneousPotentialBielecki a b k T η ha ha1 hk hT B u₀ 0‖ ≤ ‖u₀‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg u₀)).2
  intro t
  have hz : homogeneousPotentialHistory T hT B
      (homogeneousTimeWeight T η (0 : C(Icc (0 : ℝ) T, HomogeneousY a k))) = fun _ => 0 := by
    funext s
    change B (Real.exp (η * (projIcc 0 T hT s : ℝ)) • (0 : HomogeneousY a k)) = 0
    rw [smul_zero, map_zero]
  change ‖Real.exp (-η * (t : ℝ)) •
    (homogeneousFreeOperator a b k t ha ha1 hk u₀ +
      homogeneousDuhamel a b k ha ha1 hk t
        (homogeneousPotentialHistory T hT B (homogeneousTimeWeight T η 0)))‖ ≤ ‖u₀‖
  rw [hz, homogeneousDuhamel_zero, add_zero, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  have hf : ‖homogeneousFreeOperator a b k t ha ha1 hk u₀‖ ≤ ‖u₀‖ :=
    (homogeneousFreeOperator_forward_bound a b k t ha ha1 hk t.2.1 u₀).trans
      (mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (by
        nlinarith [t.2.1])))
  exact (mul_le_mul_of_nonneg_left hf (Real.exp_pos _).le).trans
    (mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (by
      nlinarith [mul_nonneg hη t.2.1])))

theorem homogeneousPotential_mild_bound
    (a b k T : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hT : 0 ≤ T)
    (B : HomogeneousY a k →L[ℝ] HomogeneousY a k) (u₀ : HomogeneousY a k)
    (u : C(Icc (0 : ℝ) T, HomogeneousY a k))
    (hu : ∀ t : Icc (0 : ℝ) T, u t = homogeneousFreeOperator a b k t ha ha1 hk u₀ +
      homogeneousDuhamel a b k ha ha1 hk t (homogeneousPotentialHistory T hT B u))
    (t : Icc (0 : ℝ) T) :
    ‖u t‖ ≤ 2 * Real.exp ((2 * (‖B‖ + 1)) * (t : ℝ)) * ‖u₀‖ := by
  let η := 2 * (‖B‖ + 1)
  have hη : 0 < η := by dsimp [η]; positivity
  let v := homogeneousTimeWeight T (-η) u
  let P := homogeneousPotentialBielecki a b k T η ha ha1 hk hT B u₀
  have hp : homogeneousPotentialPicard a b k T ha ha1 hk hT B u₀ u = u := by
    apply ContinuousMap.ext
    intro s
    exact (hu s).symm
  have hv : P v = v := by
    dsimp only [P, v, homogeneousPotentialBielecki]
    rw [homogeneousTimeWeight_cancel, hp]
  have hz : ‖P 0‖ ≤ ‖u₀‖ :=
    homogeneousPotentialBielecki_zero_norm_le a b k T η ha ha1 hk hT hη.le B u₀
  have hdist := homogeneousPotentialBielecki_dist_le a b k T η ha ha1 hk hT hη B u₀ v 0
  change dist (P v) (P 0) ≤ _ at hdist
  rw [hv, dist_eq_norm, dist_zero_right] at hdist
  have hratio : ‖B‖ / η ≤ 1 / 2 := (div_le_iff₀ hη).mpr (by dsimp [η]; nlinarith)
  have htri : ‖v‖ ≤ ‖v - P 0‖ + ‖P 0‖ := by
    calc
      ‖v‖ = ‖(v - P 0) + P 0‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have hdist' : ‖v - P 0‖ ≤ (1 / 2 : ℝ) * ‖v‖ :=
    hdist.trans (mul_le_mul_of_nonneg_right hratio (norm_nonneg v))
  have hvbound : ‖v‖ ≤ 2 * ‖u₀‖ := by linarith
  have heq : Real.exp (η * (t : ℝ)) • v t = u t := by
    exact congrArg (fun w : C(Icc (0 : ℝ) T, HomogeneousY a k) => w t)
      (homogeneousTimeWeight_cancel T η u)
  rw [← heq, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (η * (t : ℝ)) * (2 * ‖u₀‖) :=
      mul_le_mul_of_nonneg_left ((ContinuousMap.norm_coe_le_norm v t).trans hvbound)
        (Real.exp_pos _).le
    _ = _ := by dsimp [η]; ring

theorem homogeneousLinearized_mild_bound
    (a b k T : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hT : 0 ≤ T)
    (m : ℕ) (q u₀ : HomogeneousY a k) (u : C(Icc (0 : ℝ) T, HomogeneousY a k))
    (hu : ∀ t : Icc (0 : ℝ) T, u t = homogeneousFreeOperator a b k t ha ha1 hk u₀ +
      homogeneousDuhamel a b k ha ha1 hk t
        (homogeneousPotentialHistory T hT (homogeneousLinearizedPotential a k ha ha1 hk m q) u))
    (t : Icc (0 : ℝ) T) :
    ‖u t‖ ≤ 2 * Real.exp
      ((2 * (‖homogeneousLinearizedPotential a k ha ha1 hk m q‖ + 1)) * (t : ℝ)) * ‖u₀‖ :=
  homogeneousPotential_mild_bound a b k T ha ha1 hk hT _ u₀ u hu t

end DefocusingNLS

end OAI
