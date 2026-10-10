import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRobinMatrix
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalCoupling
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace OAI

/-! # Exact transverse defect of the outgoing value plane

The two-channel second-order equation gives a closed first-order equation
for `U' - A U` whenever `A` satisfies its Riccati identity. This is the
starting point for excluding a transverse component using the actual
top-derivative L² bound.
-/

open Filter Topology

namespace DefocusingNLS

local notation "V" => ℂ × ℂ
local notation "End" => V →L[ℂ] V

theorem homogeneousPair_fst_hasDerivAt {u : ℝ → V} {v : V} {r : ℝ}
    (h : HasDerivAt u v r) : HasDerivAt (fun t => (u t).1) v.1 r :=
  (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt r h

theorem homogeneousPair_snd_hasDerivAt {u : ℝ → V} {v : V} {r : ℝ}
    (h : HasDerivAt u v r) : HasDerivAt (fun t => (u t).2) v.2 r :=
  (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt r h

noncomputable def homogeneousRadialDamping (r : ℝ) : End :=
  spectralTwoColumns (11 / (r : ℂ) + Complex.I * r / 2, 0)
    (0, 11 / (r : ℂ) - Complex.I * r / 2)

noncomputable def homogeneousRadialStiffness (νp νm eta : ℂ) (m : ℕ)
    (Q : ℂ) (r : ℝ) : End :=
  spectralTwoColumns
    (-Complex.I * νp / 2 - eta / (r : ℂ) ^ 2 - spectralDiagonalCoefficient m Q,
      -star (spectralCrossCoefficient m Q))
    (-spectralCrossCoefficient m Q,
      Complex.I * νm / 2 - eta / (r : ℂ) ^ 2 - star (spectralDiagonalCoefficient m Q))

theorem homogeneousRadial_acceleration (νp νm eta : ℂ) (m : ℕ) (Q : ℂ)
    (r : ℝ) (z : (ℂ × ℂ) × (ℂ × ℂ)) :
    ((spectralPhysicalCircularField νp νm eta m Q r z).1.2,
      (spectralPhysicalCircularField νp νm eta m Q r z).2.2) =
      -homogeneousRadialDamping r (z.1.2, z.2.2) -
        homogeneousRadialStiffness νp νm eta m Q r (z.1.1, z.2.1) := by
  apply Prod.ext <;>
    simp only [homogeneousRadialDamping, homogeneousRadialStiffness,
      spectralTwoColumns_apply, spectralPhysicalCircularField, Prod.fst_add,
      Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  all_goals ring

theorem homogeneousComplexOperator_hasDerivAt_apply
    (A : ℝ → End) (A' : End) (u : ℝ → V) (u' : V) (r : ℝ)
    (hA : HasDerivAt A A' r) (hu : HasDerivAt u u' r) :
    HasDerivAt (fun t => A t (u t)) (A' (u r) + A r u') r := by
  have hAr := (ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ).hasFDerivAt.comp_hasDerivAt r hA
  simpa only [ContinuousLinearMap.coe_restrict_scalarsL',
    Function.comp_def, ContinuousLinearMap.coe_restrictScalars'] using hAr.clm_apply hu

noncomputable def homogeneousRadialDefect (A : ℝ → End) (u v : ℝ → V) (r : ℝ) : V :=
  v r - A r (u r)

theorem homogeneousRadialDefect_hasDerivAt
    (B C : End) (A : ℝ → End) (u v : ℝ → V) (r : ℝ)
    (hu : HasDerivAt u (v r) r)
    (hv : HasDerivAt v (-B (v r) - C (u r)) r)
    (hA : HasDerivAt A (-B * A r - C - A r * A r) r) :
    HasDerivAt (homogeneousRadialDefect A u v)
      (-(B + A r) (homogeneousRadialDefect A u v r)) r := by
  apply (hv.sub (homogeneousComplexOperator_hasDerivAt_apply A _ u _ r hA hu)).congr_deriv
  simp only [homogeneousRadialDefect, sub_apply, neg_apply, add_apply,
    mul_apply_eq_comp, map_sub]
  abel

end DefocusingNLS

end OAI
