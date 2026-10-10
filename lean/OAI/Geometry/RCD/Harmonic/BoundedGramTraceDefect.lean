import OAI.Geometry.RCD.Harmonic.GramTraceDefect
import OAI.Geometry.RCD.Harmonic.GramDefect

namespace OAI

/-! # Trace errors of the actual uniformly bounded coordinate Gram matrix -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem localGamma_family_abs_le {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    {S : Set X} {L : ℝ} (hL : 0≤L)
    (hu : ∀ i, ∀ᵐ x ∂μ.restrict S, localGamma μ hQ (u i) (u i) x≤L^2) :
    ∀ᵐ x ∂μ.restrict S, ∀ i j, |localGamma μ hQ (u i) (u j) x|≤L^2 := by
  have hn (i : Fin n) : ∀ᵐ x ∂μ, 0≤SobolevSpace.minimalSlope μ hQ (u i) x :=
    (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ (u i))
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  filter_upwards [hu i,hu j,ae_restrict_of_ae (localGamma_abs_le μ hQ (u i) (u j)),
    ae_restrict_of_ae (localGamma_self μ hQ (u i)),
    ae_restrict_of_ae (localGamma_self μ hQ (u j)),
    ae_restrict_of_ae (hn i),ae_restrict_of_ae (hn j)] with x hi hj hcs hei hej hni hnj
  rw [hei] at hi
  rw [hej] at hj
  have hsi : SobolevSpace.minimalSlope μ hQ (u i) x≤L := by nlinarith
  have hsj : SobolevSpace.minimalSlope μ hQ (u j) x≤L := by nlinarith
  exact hcs.trans (by nlinarith)

theorem bounded_gram_trace_defect {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    {S : Set X}
    (hu : ∀ i, ∀ᵐ x ∂μ.restrict S, localGamma μ hQ (u i) (u i) x≤4) :
    ∀ᵐ x ∂μ.restrict S,
      (|∑ i, localGamma μ hQ (u i) (u i) x-(n:ℝ)|≤5*gramDefect μ hQ u x) ∧
      (|∑ i, ∑ j, (localGamma μ hQ (u i) (u j) x)^2-(n:ℝ)|≤5*gramDefect μ hQ u x) := by
  have hh : ∀ i, ∀ᵐ x ∂μ.restrict S, localGamma μ hQ (u i) (u i) x≤(2:ℝ)^2 := by
    simpa only [show (2:ℝ)^2=4 by norm_num] using hu
  filter_upwards [localGamma_family_abs_le μ hQ u (by norm_num : (0:ℝ)≤2) hh] with x hx
  let G := fun i j => localGamma μ hQ (u i) (u j) x
  have hd : matrixGramDefect G=gramDefect μ hQ u x := rfl
  constructor
  · have ht := gram_trace_defect G
    rw [hd] at ht
    exact ht.trans (by nlinarith [gramDefect_nonneg μ hQ u x])
  · have ht := gram_square_defect G (by simpa only [show (2:ℝ)^2=4 by norm_num] using hx)
    simpa only [hd,show (4:ℝ)+1=5 by norm_num] using ht

end RegularPointCoordinates

end

end OAI
