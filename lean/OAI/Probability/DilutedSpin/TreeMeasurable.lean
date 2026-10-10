import OAI.Probability.DilutedSpin.TreeAnchor

namespace OAI

section
section
namespace DilutedSpinGlass.FiniteLaw
open _root_.MeasureTheory _root_.OAI.MeasureTheory
variable {Ω X : Type} [Fintype Ω] [MeasurableSpace X]

theorem measurable_tilt_weight (P : FiniteLaw Ω) (m : ℝ) {f : X → Ω → ℝ}
    (hf : ∀ a, Measurable (fun x => f x a)) (a : Ω) :
    Measurable (fun x => (P.tilt m (f x)).weight a) := by
  change Measurable (fun x => P.weight a * Real.exp (m*f x a) /
    P.expect (fun b => Real.exp (m*f x b)))
  exact (measurable_const.mul ((hf a).const_mul m).exp).div
    (P.measurable_expect (fun b => ((hf b).const_mul m).exp))

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory
variable {Ω X : Type} [Fintype Ω] [MeasurableSpace X]

/-- Measurability of every finite prescribed-tree probability for the actual
recursively tilted conditional kernels. -/
theorem measurable_tilt_sample_weight {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin n → ℝ) {f : X → FinitePath Ω n → ℝ}
    (hf : ∀ y, Measurable (fun x => f x y)) (a : S.Sample Ω) :
    Measurable (fun x => (S.sampleLaw (KernelTower.tilt n T m (f x))).weight a) := by
  induction S with
  | leaf => exact measurable_const
  | @node n k C ih =>
    change Measurable (fun x => ∏ i : Fin k,
      (T.1.tilt (m 0) (fun z => KernelTower.backwardLog n (T.2 z)
        (fun j => m j.succ) (fun y => f x (z,y)))).weight (a i).1 *
      ((C i).sampleLaw (KernelTower.tilt n (T.2 (a i).1)
        (fun j => m j.succ) (fun y => f x ((a i).1,y)))).weight (a i).2)
    apply Finset.measurable_prod
    intro i _
    exact (T.1.measurable_tilt_weight (m 0)
      (fun z => KernelTower.measurable_backwardLog n (T.2 z) (fun j => m j.succ)
        (fun y => hf (z,y))) (a i).1).mul
      (ih i (T.2 (a i).1) (fun j => m j.succ) (fun y => hf ((a i).1,y)) (a i).2)

theorem measurable_tilt_sample_expect {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin n → ℝ) {f : X → FinitePath Ω n → ℝ}
    {g : X → S.Sample Ω → ℝ}
    (hf : ∀ y, Measurable (fun x => f x y)) (hg : ∀ a, Measurable (fun x => g x a)) :
    Measurable (fun x => (S.sampleLaw (KernelTower.tilt n T m (f x))).expect (g x)) := by
  apply Finset.measurable_sum
  intro a _
  exact (measurable_tilt_sample_weight S T m hf a).mul (hg a)

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
