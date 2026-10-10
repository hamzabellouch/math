import OAI.Probability.DilutedSpin.AnchorExtension

namespace OAI

section
section
namespace DilutedSpinGlass.FiniteLaw
variable {Ω X : Type} [Fintype Ω] [NormedAddCommGroup X] [NormedSpace ℝ X]
    {x : X} {smooth : WithTop ℕ∞}

lemma contDiffAt_expect (P : FiniteLaw Ω) {f : X → Ω → ℝ}
    (hf : ∀ a, ContDiffAt ℝ smooth (fun x => f x a) x) :
    ContDiffAt ℝ smooth (fun x => P.expect (f x)) x := by
  apply ContDiffAt.sum
  intro a _
  exact contDiffAt_const.mul (hf a)

lemma contDiffAt_expMoment (P : FiniteLaw Ω) (m : ℝ) {f : X → Ω → ℝ}
    (hf : ∀ a, ContDiffAt ℝ smooth (fun x => f x a) x) :
    ContDiffAt ℝ smooth (fun x => P.expMoment m (f x)) x :=
  P.contDiffAt_expect (fun a => (contDiffAt_const.mul (hf a)).exp)

lemma contDiffAt_logMean (P : FiniteLaw Ω) (m : ℝ) {f : X → Ω → ℝ}
    (hf : ∀ a, ContDiffAt ℝ smooth (fun x => f x a) x) :
    ContDiffAt ℝ smooth (fun x => P.logMean m (f x)) x := by
  exact ((P.contDiffAt_expMoment m hf).log (P.expMoment_pos m (f x)).ne').div_const m

lemma contDiffAt_tilt_weight (P : FiniteLaw Ω) (m : ℝ) {f : X → Ω → ℝ}
    (hf : ∀ a, ContDiffAt ℝ smooth (fun x => f x a) x) (a : Ω) :
    ContDiffAt ℝ smooth (fun x => (P.tilt m (f x)).weight a) x := by
  exact (contDiffAt_const.mul (contDiffAt_const.mul (hf a)).exp).div
    (P.contDiffAt_expMoment m hf) (P.expMoment_pos m (f x)).ne'
end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.KernelTower
variable {Ω X : Type} [Fintype Ω] [NormedAddCommGroup X] [NormedSpace ℝ X]
    {x : X} {smooth : WithTop ℕ∞}
lemma contDiffAt_backwardLog (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    {f : X → FinitePath Ω n → ℝ}
    (hf : ∀ a, ContDiffAt ℝ smooth (fun x => f x a) x) :
    ContDiffAt ℝ smooth (fun x => backwardLog n T m (f x)) x := by
  induction n with
  | zero => exact hf ()
  | succ n ih =>
    exact T.1.contDiffAt_logMean (m 0)
      (fun a => ih (T.2 a) (fun j => m j.succ) (fun b => hf (a,b)))
end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.PrescribedTree
variable {Ω X : Type} [Fintype Ω] [NormedAddCommGroup X] [NormedSpace ℝ X]
    {x : X} {smooth : WithTop ℕ∞}
lemma contDiffAt_tilt_sample_weight {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin n → ℝ) {f : X → FinitePath Ω n → ℝ}
    (hf : ∀ y, ContDiffAt ℝ smooth (fun x => f x y) x) (a : S.Sample Ω) :
    ContDiffAt ℝ smooth (fun x => (S.sampleLaw (KernelTower.tilt n T m (f x))).weight a) x := by
  induction S with
  | leaf => exact contDiffAt_const
  | @node n k C ih =>
    change ContDiffAt ℝ smooth (fun x => ∏ i : Fin k,
      (T.1.tilt (m 0) (fun z => KernelTower.backwardLog n (T.2 z)
        (fun j => m j.succ) (fun y => f x (z,y)))).weight (a i).1 *
      ((C i).sampleLaw (KernelTower.tilt n (T.2 (a i).1)
        (fun j => m j.succ) (fun y => f x ((a i).1,y)))).weight (a i).2) x
    apply contDiffAt_prod
    intro i _
    exact (T.1.contDiffAt_tilt_weight (m 0)
      (fun z => KernelTower.contDiffAt_backwardLog n (T.2 z) (fun j => m j.succ)
        (fun y => hf (z,y))) (a i).1).mul
      (ih i (T.2 (a i).1) (fun j => m j.succ) (fun y => hf ((a i).1,y)) (a i).2)

lemma contDiffAt_tilt_sample_expect {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin n → ℝ) {f : X → FinitePath Ω n → ℝ}
    {g : X → S.Sample Ω → ℝ}
    (hf : ∀ y, ContDiffAt ℝ smooth (fun x => f x y) x)
    (hg : ∀ a, ContDiffAt ℝ smooth (fun x => g x a) x) :
    ContDiffAt ℝ smooth (fun x => (S.sampleLaw (KernelTower.tilt n T m (f x))).expect (g x)) x := by
  apply ContDiffAt.sum
  intro a _
  exact (contDiffAt_tilt_sample_weight S T m hf a).mul (hg a)
end DilutedSpinGlass.PrescribedTree
end

end

end OAI
