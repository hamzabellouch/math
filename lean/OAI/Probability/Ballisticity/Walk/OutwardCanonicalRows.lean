import Mathlib
import OAI.Probability.Ballisticity.Entropy.BufferCostBounds
import OAI.Probability.Ballisticity.Entropy.CanonicalLogExcess

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma outwardKernelMass_upper_rows {d : ℕ} (e f : Direction d) (H : ℕ) (hH : 0 < H)
    (a : ℝ) (x : Lattice d × Lattice d) (hx : x ∈ PairAtHeight (realPosition (step e)) a) :
    @Measurable _ _ (rowSigma {y | a ≤ dot (realPosition y) (realPosition (step e))}) _
      (outwardKernelMass e f H x) := by
  have h₁ : Strip (realPosition (step e)) x.1 H ⊆ {y | a ≤ dot (realPosition y) (realPosition (step e))} := by
    intro y hy
    change a ≤ dot (realPosition y) (realPosition (step e))
    simpa only [hx.1] using hy.1
  have h₂ : Strip (realPosition (step e)) x.2 H ⊆ {y | a ≤ dot (realPosition y) (realPosition (step e))} := by
    intro y hy
    change a ≤ dot (realPosition y) (realPosition (step e))
    simpa only [hx.2] using hy.1
  exact ((Measure.measurable_coe (Set.to_countable _).measurableSet).comp
    (rawPairEndpointLaw_rows (realPosition (step e)) x hH h₁ h₂)).ennreal_toReal

lemma measurable_outwardKernelMass {d : ℕ} (e f : Direction d) (H : ℕ)
    (x : Lattice d × Lattice d) : Measurable (outwardKernelMass e f H x) := by
  have h := ((variablePairHitKernel (realPosition (step e)) H).measurable_coe (Set.to_countable
    {y : Lattice d × Lattice d | signedCoordinate f (x.2-x.1) ≤ signedCoordinate f (y.2-y.1)}).measurableSet).comp
      (measurable_id.prodMk (measurable_const (a:=x)))
  change Measurable (fun ω => outwardKernelMass e f H x ω)
  simpa only [Function.comp_def,id_eq,variablePairHitKernel_apply,outwardKernelMass] using h.ennreal_toReal

noncomputable def outwardCanonicalExcess {d : ℕ} (e f : Direction d) (A : ℝ)
    (x : Lattice d × Lattice d) : Environment d → ℝ :=
  canonicalLogExcess A (fun n => outwardKernelMass e f (n+1) x)

lemma outwardCanonicalExcess_upper_rows {d : ℕ} (e f : Direction d) (A a : ℝ)
    (x : Lattice d × Lattice d) (hx : x ∈ PairAtHeight (realPosition (step e)) a) :
    @Measurable _ _ (rowSigma {y | a ≤ dot (realPosition y) (realPosition (step e))}) _
      (outwardCanonicalExcess e f A x) := by
  let : MeasurableSpace (Environment d) := rowSigma {y | a ≤ dot (realPosition y) (realPosition (step e))}
  apply measurable_canonicalLogExcess
  intro n
  exact outwardKernelMass_upper_rows e f (n+1) (Nat.succ_pos n) a x hx

lemma measurable_outwardCanonicalExcess {d : ℕ} (e f : Direction d) (A : ℝ)
    (x : Lattice d × Lattice d) : Measurable (outwardCanonicalExcess e f A x) :=
  measurable_canonicalLogExcess A _ (fun n => measurable_outwardKernelMass e f (n+1) x)
end DirectionalTransience

end

end

end OAI
