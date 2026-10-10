import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousComplexification
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLinearizedSemigroup

namespace OAI

/-! # The strongly continuous complexified linearized semigroup -/

open scoped NNReal

namespace DefocusingNLS

section

variable (a b k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
  (m : ℕ) (q : HomogeneousY a k)

local notation "H" => HomogeneousY a k

noncomputable def homogeneousComplexLinearizedStep (t : ℝ≥0) :
    (H × H) →L[ℂ] (H × H) :=
  homogeneousComplexification a k ha ha1 hk
    (homogeneousLinearizedStep a b k ha ha1 hk m q t)

@[simp] theorem homogeneousComplexLinearizedStep_zero :
    homogeneousComplexLinearizedStep a b k ha ha1 hk m q 0 =
      ContinuousLinearMap.id ℂ (H × H) := by
  rw [homogeneousComplexLinearizedStep, homogeneousLinearizedStep_zero,
    homogeneousComplexification_id]

theorem homogeneousComplexLinearizedStep_add (s t : ℝ≥0) :
    homogeneousComplexLinearizedStep a b k ha ha1 hk m q (s + t) =
      (homogeneousComplexLinearizedStep a b k ha ha1 hk m q t).comp
        (homogeneousComplexLinearizedStep a b k ha ha1 hk m q s) := by
  simp only [homogeneousComplexLinearizedStep, homogeneousLinearizedStep_add,
    homogeneousComplexification_comp]

theorem continuous_homogeneousComplexLinearizedStep_apply :
    Continuous (fun p : ℝ≥0 × (H × H) =>
      homogeneousComplexLinearizedStep a b k ha ha1 hk m q p.1 p.2) := by
  let X := homogeneousComplexReal a k ha ha1 hk
  let Y := homogeneousComplexImag a k ha ha1 hk
  let J := homogeneousConjugation a k ha ha1 hk
  have hX := (continuous_homogeneousLinearizedStep_apply a b k ha ha1 hk m q).comp
    (continuous_fst.prodMk (X.continuous.comp continuous_snd))
  have hY := (continuous_homogeneousLinearizedStep_apply a b k ha ha1 hk m q).comp
    (continuous_fst.prodMk (Y.continuous.comp continuous_snd))
  change Continuous (fun p : ℝ≥0 × (H × H) =>
    (homogeneousLinearizedStep a b k ha ha1 hk m q p.1 (X p.2) +
        Complex.I • homogeneousLinearizedStep a b k ha ha1 hk m q p.1 (Y p.2),
      J (homogeneousLinearizedStep a b k ha ha1 hk m q p.1 (X p.2)) +
        Complex.I • J (homogeneousLinearizedStep a b k ha ha1 hk m q p.1 (Y p.2))))
  exact (hX.add (hY.const_smul Complex.I)).prodMk
    ((J.continuous.comp hX).add ((J.continuous.comp hY).const_smul Complex.I))

end

end DefocusingNLS

end OAI
