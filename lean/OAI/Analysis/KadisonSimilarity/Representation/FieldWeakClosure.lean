import OAI.Analysis.KadisonSimilarity.Representation.CountableLpSubsequence
import OAI.Analysis.KadisonSimilarity.Derivation.DiagonalMatrixNorm
import Mathlib.Topology.MetricSpace.Equicontinuity

namespace OAI

/-! # Von Neumann closure of actual operator fields

A common subsequence on countably many constant L² columns turns strong
operator convergence into pointwise strong convergence almost everywhere.
The uniform norm bound extends convergence from the dense columns to every
fiber vector. Bicommutant closure then proves fiber membership.
-/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory Filter
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [TopologicalSpace.SeparableSpace H]

/-- Uniformly bounded operators converge strongly once they converge on a
fixed countable dense set. -/
theorem strong_tendsto_of_bounded_dense_columns
    (T : ℕ → H →L[ℂ] H) (S : H →L[ℂ] H) (C : ℝ)
    (hbound : ∀ n, ‖T n‖ ≤ C)
    (hcol : ∀ j, Tendsto (fun n => T n (TopologicalSpace.denseSeq H j))
      atTop (𝓝 (S (TopologicalSpace.denseSeq H j)))) :
    ∀ x : H, Tendsto (fun n => T n x) atTop (𝓝 (S x)) := by
  have hequi : Equicontinuous (fun n x => T n x) := by
    apply Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => C * r)
      (by simpa only [mul_zero] using (continuous_const_mul C).tendsto (0 : ℝ))
    intro x y n
    rw [dist_eq_norm, ← map_sub, dist_eq_norm]
    exact ((T n).le_opNorm (x - y)).trans
      (mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg _))
  intro x
  exact (TopologicalSpace.denseRange_denseSeq H).induction_on x
    (hequi.isClosed_setOfPred_tendsto S.continuous) hcol

variable [CompleteSpace H]

omit [TopologicalSpace.SeparableSpace H] in
/-- Strong limits preserve von Neumann membership directly by commuting
with every member of the commutant. -/
theorem vonNeumann_mem_of_strong_tendsto
    (P : VonNeumannAlgebra H) (T : ℕ → H →L[ℂ] H) (S : H →L[ℂ] H)
    (hmem : ∀ n, T n ∈ P)
    (hlim : ∀ x : H, Tendsto (fun n => T n x) atTop (𝓝 (S x))) : S ∈ P := by
  rw [← P.commutant_commutant]
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro A hA
  apply ContinuousLinearMap.ext
  intro x
  have hleft : Tendsto (fun n => A (T n x)) atTop (𝓝 (A (S x))) :=
    (A.continuous.tendsto (S x)).comp (hlim x)
  have heq : (fun n => A (T n x)) = (fun n => T n (A x)) := by
    funext n
    exact congrArg (fun R : H →L[ℂ] H => R x)
      (VonNeumannAlgebra.mem_commutant_iff.mp hA (T n) (hmem n)).symm
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft (hlim (A x))

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

/-- Fiber membership is inherited from uniformly bounded strong
approximants on L². The pointwise action hypotheses are per fixed vector,
so no uncountable intersection of conull sets is used. -/
theorem ae_field_mem_of_strong_approximation
    (P : Ω → VonNeumannAlgebra H)
    (T : ℕ → Lp H 2 μ →L[ℂ] Lp H 2 μ) (S : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (R : ℕ → Ω → H →L[ℂ] H) (Q : Ω → H →L[ℂ] H)
    (haction : ∀ n (f : Lp H 2 μ), ∀ᵐ a ∂μ, T n f a = R n a (f a))
    (hS : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, S f a = Q a (f a))
    (hstrong : ∀ f : Lp H 2 μ, Tendsto (fun n => T n f) atTop (𝓝 (S f)))
    (C : ℝ) (hbound : ∀ n, ∀ᵐ a ∂μ, ‖R n a‖ ≤ C)
    (hmem : ∀ n, ∀ᵐ a ∂μ, R n a ∈ P a) :
    ∀ᵐ a ∂μ, Q a ∈ P a := by
  let d := TopologicalSpace.denseSeq H
  obtain ⟨k, _, hlim⟩ := exists_countable_L2_ae_subsequence μ
    (fun n j => T n (Lp.const 2 μ (d j)))
    (fun j => S (Lp.const 2 μ (d j))) (fun j => hstrong _)
  have hsource : ∀ᵐ a ∂μ, ∀ j n,
      T (k n) (Lp.const 2 μ (d j)) a = R (k n) a (d j) :=
    eventually_countable_forall.mpr fun j => eventually_countable_forall.mpr fun n =>
      pointwise_action_column μ (T (k n)) (R (k n)) (haction (k n)) (d j)
  have htarget : ∀ᵐ a ∂μ, ∀ j,
      S (Lp.const 2 μ (d j)) a = Q a (d j) :=
    eventually_countable_forall.mpr fun j => pointwise_action_column μ S Q hS (d j)
  have hb : ∀ᵐ a ∂μ, ∀ n, ‖R n a‖ ≤ C :=
    eventually_countable_forall.mpr hbound
  have hm : ∀ᵐ a ∂μ, ∀ n, R n a ∈ P a :=
    eventually_countable_forall.mpr hmem
  filter_upwards [hlim, hsource, htarget, hb, hm] with a hlim hsource htarget hb hm
  have hcol : ∀ j, Tendsto (fun n => R (k n) a (TopologicalSpace.denseSeq H j))
      atTop (𝓝 (Q a (TopologicalSpace.denseSeq H j))) := by
    intro j
    have heq : (fun n => T (k n) (Lp.const 2 μ (d j)) a) =
        (fun n => R (k n) a (d j)) := funext (hsource j)
    have hj := hlim j
    rw [heq, htarget j] at hj
    exact hj
  exact vonNeumann_mem_of_strong_tendsto (P a) (fun n => R (k n) a) (Q a)
    (fun n => hm (k n))
    (strong_tendsto_of_bounded_dense_columns _ _ C (fun n => hb (k n)) hcol)

/-- In applications the uniform bound is a norm bound on the actual
approximating operators; the pointwise bound is then derived. -/
theorem ae_field_mem_of_norm_bounded_strong_approximation
    (P : Ω → VonNeumannAlgebra H)
    (T : ℕ → Lp H 2 μ →L[ℂ] Lp H 2 μ) (S : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (R : ℕ → Ω → H →L[ℂ] H) (Q : Ω → H →L[ℂ] H)
    (haction : ∀ n (f : Lp H 2 μ), ∀ᵐ a ∂μ, T n f a = R n a (f a))
    (hS : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, S f a = Q a (f a))
    (hstrong : ∀ f : Lp H 2 μ, Tendsto (fun n => T n f) atTop (𝓝 (S f)))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ n, ‖T n‖ ≤ C)
    (hmem : ∀ n, ∀ᵐ a ∂μ, R n a ∈ P a) :
    ∀ᵐ a ∂μ, Q a ∈ P a :=
  ae_field_mem_of_strong_approximation μ P T S R Q haction hS hstrong C
    (fun n => (pointwise_field_norm_iff μ (T n) (R n) (haction n) C hC).mp (hbound n)) hmem

end KadisonSimilarity

end

end OAI
