import OAI.NumberTheory.DukePrimeDegree.Dynamics.ReturnTowerMass
import OAI.NumberTheory.PrimePackets.ShannonEntropy

namespace OAI

/-! # Finite Shannon entropy of the first-return partition

The geometric reference distribution turns the mass-weighted return-time
bound into summable information. This is the return-partition estimate in
Einsiedler--Lindenstrauss, Proposition 7.44, paragraph 7.48.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

/-- A finite first moment controls the information of a subprobability
sequence; no normalization of the return section is necessary. -/
theorem summable_information_of_first_moment (p : ℕ → ℝ)
    (hp : ∀ n, 0 ≤ p n) (hp1 : ∀ n, p n ≤ 1)
    (hmean : Summable (fun n : ℕ => (n+1:ℝ)*p n)) :
    Summable (fun n => Real.negMulLog (p n)) := by
  have hg : Summable (fun n : ℕ => (1/2:ℝ)^(n+1)) := by
    simpa only [pow_succ] using
      (summable_geometric_of_lt_one (show (0:ℝ) ≤ 1/2 by norm_num)
        (show (1/2:ℝ) < 1 by norm_num)).mul_right (1/2)
  have hb : Summable (fun n : ℕ => ((n+1:ℝ)*p n)*Real.log 2 + (1/2:ℝ)^(n+1)) :=
    (hmean.mul_right (Real.log 2)).add hg
  apply Summable.of_nonneg_of_le (fun n => Real.negMulLog_nonneg (hp n) (hp1 n)) _ hb
  intro n
  have hq : 0 < (1/2:ℝ)^(n+1) := by positivity
  have H := negMulLog_le_cross (hp n) hq.le (fun h => (hq.ne' h).elim)
  have he : Real.log ((1/2:ℝ)^(n+1)) = -(n+1:ℝ)*Real.log 2 := by
    rw [Real.log_pow, show (1/2:ℝ)=(2:ℝ)⁻¹ by norm_num, Real.log_inv]
    push_cast
    ring
  rw [he] at H
  nlinarith [hp n]

theorem firstReturnPartition_information_summable
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ) (hE : MeasurableEmbedding T)
    {S : Set Y} (hS : MeasurableSet S) :
    Summable (fun n => Real.negMulLog (μ.real (firstReturnLevel T S n))) :=
  summable_information_of_first_moment _ (fun _ => measureReal_nonneg)
    (fun _ => measureReal_le_one) (summable_firstReturnLevel_mass μ hT hE hS)

end DukePrimeDegree

end

end OAI
