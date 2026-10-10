import OAI.Analysis.CircleDomains.Probability.FiniteChoiceLaw
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Topology.MetricSpace.PiNat

namespace OAI

/-! A probability measure on Baire addresses with a prescribed finite-history
transition law. The first coordinate is a dummy; later coordinates choose the
successive children. -/

open Set MeasureTheory ProbabilityTheory Function Preorder
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity
namespace FusionTrajectory

abbrev History (n : ℕ) := ↥(Finset.Iic n) → ℕ

def history (n : ℕ) (h : History n) : List ℕ :=
  PiNat.res (fun i => h ⟨min (i + 1) n, Finset.mem_Iic.mpr (Nat.min_le_right (i + 1) n)⟩) n

def branch (x : ℕ → ℕ) (i : ℕ) : ℕ := x (i + 1)

theorem history_restrict (n : ℕ) (x : ℕ → ℕ) :
    history n (frestrictLe n x) = PiNat.res (branch x) n := by
  apply PiNat.res_eq_res.mpr
  intro i hi
  simp only [frestrictLe_apply, branch]
  congr 1
  exact Nat.min_eq_left (by omega)

variable (step : List ℕ → ProbabilityMeasure ℕ)

def transition (n : ℕ) : Kernel (History n) ℕ where
  toFun h := (step (history n h) : Measure ℕ)
  measurable' := measurable_of_countable _

instance (n : ℕ) : IsMarkovKernel (transition step n) :=
  ⟨fun h => (step (history n h)).prop⟩

def measure : Measure (ℕ → ℕ) :=
  Kernel.trajMeasure (Measure.dirac 0) (transition step)

instance : IsProbabilityMeasure (measure step) := by
  unfold measure
  infer_instance

theorem measurable_branch : Measurable branch := by
  unfold branch
  fun_prop

theorem integral_next (n : ℕ) (g : List ℕ → ℕ → ℝ)
    (M : ℝ) (hM : ∀ l a, |g l a| ≤ M) :
    ∫ x, g (PiNat.res (branch x) n) (x (n + 1)) ∂measure step =
      ∫ h : History n, ∫ a, g (history n h) a ∂(step (history n h) : Measure ℕ)
        ∂(measure step).map (frestrictLe n) := by
  let f : History n × ℕ → ℝ := fun q => g (history n q.1) q.2
  have hfm : Measurable f := measurable_of_countable _
  have hf : Integrable f (((measure step).map (frestrictLe n)) ⊗ₘ transition step n) :=
    Integrable.of_bound hfm.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun q => by simpa only [Real.norm_eq_abs] using hM _ _)
  have heq := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ => ℕ) (μ₀ := Measure.dirac (0 : ℕ)) (κ := transition step) (a := n)
  change _ = ∫ h : History n, ∫ a, f (h, a) ∂transition step n h
    ∂(measure step).map (frestrictLe n)
  rw [← Measure.integral_compProd hf]
  change _ = ∫ q, f q ∂(((measure step).map (frestrictLe n)) ⊗ₘ transition step n)
  rw [show ((measure step).map (frestrictLe n)) ⊗ₘ transition step n =
    (measure step).map (fun x => (frestrictLe n x, x (n + 1))) from heq]
  rw [integral_map (by fun_prop) hfm.aestronglyMeasurable]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by simp only [f, history_restrict]

end FusionTrajectory
end CircleDomainRigidity

end

end OAI
