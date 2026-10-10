import OAI.NumberTheory.PrimePackets.ZetaDerivatives

namespace OAI

/-!
# The published analytic input for prime-degree packets

The conditional development uses Stark, *Some effective cases of the
Brauer–Siegel theorem*, Invent. Math. 23 (1974), 135–152, Lemmas 3 and 8
and equation (9). `StarkInput` records only the consequence needed here:
for fields with no quadratic subfield, the nontrivial zeros are separated
from 1 on the scale `1 / log D`, and their real Hadamard sum converges.
The zeros are indexed with multiplicity. The archimedean term and
Euler-product derivative estimate then give the uniform residue comparison.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace DukePrimeDegree

open PrimeDegreePackets

universe u

/-- The zero-free specialization of Stark's Lemmas 3 and 8, together
with his real Hadamard identity (9). Only fields of the fixed degree
and without quadratic subfields are used. -/
def StarkInput (n : ℕ) : Prop :=
  ∃ c L₀ : ℝ, 0 < c ∧ 4 ≤ L₀ ∧
    ∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyReal K],
      Module.finrank ℚ K = n →
      (∀ F : IntermediateField ℚ K, Module.finrank ℚ F ≠ 2) →
      L₀ ≤ Real.log |(NumberField.discr K : ℝ)| →
      ∃ (ι : Type) (ρ : ι → ℂ),
        (∀ i, NumberField.dedekindZeta K (ρ i) = 0 ∧ 0 ≤ (ρ i).re ∧ (ρ i).re ≤ 1) ∧
        (∀ i, c ^ 2 ≤
          (Real.log |(NumberField.discr K : ℝ)| * (1 - (ρ i).re)) ^ 2 +
          (Real.log |(NumberField.discr K : ℝ)| * (ρ i).im) ^ 2) ∧
        Summable (fun i => realPoleKernel
          (Real.log |(NumberField.discr K : ℝ)| * (1 - (ρ i).re))
          (Real.log |(NumberField.discr K : ℝ)| * (ρ i).im) 1) ∧
        ∀ h ∈ Ioc (0 : ℝ) (4 / Real.log |(NumberField.discr K : ℝ)|),
          Real.log |(NumberField.discr K : ℝ)| *
            (∑' i, realPoleKernel
              (Real.log |(NumberField.discr K : ℝ)| * (1 - (ρ i).re))
              (Real.log |(NumberField.discr K : ℝ)| * (ρ i).im)
              (Real.log |(NumberField.discr K : ℝ)| * h)) =
          1 / (1 + h) + 1 / h + Real.log |(NumberField.discr K : ℝ)| / 2 +
            deriv (realDedekindZeta K) (1 + h) / realDedekindZeta K (1 + h) +
            archimedeanZetaTerm n (1 + h)

/-- The manuscript's new uniform residue reduction, conditional on the
precisely stated published zero input above. -/
theorem uniformZetaScaleBound_of_stark {n : ℕ} (hn : n.Prime) (hn3 : 3 ≤ n)
    (H : StarkInput.{u} n) : UniformZetaScaleBound.{u} n := by
  obtain ⟨c, L₀, hc, hL₀, Hzero⟩ := H
  obtain ⟨B, hB, harch⟩ := archimedeanZetaTerm_bounded n
  let C := 4 * (1 + 3 / c) ^ 2 * (3 + B) + B + 2
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨A, E, hA, _, Hscale⟩ :=
    uniform_zeta_scale_of_large_discr_deriv n (D₀ := Real.exp L₀) hC (by
      intro K _ _ _ hdegree hD
      have hL : L₀ ≤ Real.log |(NumberField.discr K : ℝ)| := by
        have hp : 0 < |(NumberField.discr K : ℝ)| :=
          abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero K)
        exact (Real.le_log_iff_exp_le hp).mpr hD
      obtain ⟨ι, ρ, hρ, hgap, hsum, hidentity⟩ := Hzero K hdegree
        (no_quadratic_subfield hn hn3 hdegree) hL
      exact logRegularized_deriv_bound_of_zero_sum K n (hL₀.trans hL) hc hB
        (fun i => Real.log |(NumberField.discr K : ℝ)| * (1 - (ρ i).re))
        (fun i => Real.log |(NumberField.discr K : ℝ)| * (ρ i).im)
        (fun i => mul_nonneg (by linarith) (sub_nonneg.mpr (hρ i).2.2))
        hgap hsum harch hidentity)
  refine ⟨A, hA, ?_⟩
  filter_upwards [Hscale] with Q hQ
  intro K _ _ _ σ hdegree hD
  exact (hQ K σ hdegree hD).1

end DukePrimeDegree

end OAI
