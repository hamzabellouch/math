import OAI.Probability.DilutedSpin.UpperInsertion

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    {n p N : ℕ} [NeZero N]

/-- The actual root energy difference on appending a fresh independent block,
with the ordinary physical energy held fixed. -/
noncomputable def mixedRootIncrement (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (f : FinitePath Ω n → ℝ)
    (z : InteractionSample p) (sel : Fin p → Bool) : ℝ :=
  (FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)))).expect (fun i =>
    (FiniteLaw.pi (fun _ : Fin p => Q)).expect (fun r =>
      KernelTower.backwardLog n (KernelTower.prod n T (KernelTower.piTower n (fun j : Fin p => U (r j))))
        (fun j => m j.succ) (fun w => f (KernelTower.pathFst n w)+mixedTreeEnergy z sel V x r i w)-
      KernelTower.backwardLog n T (fun j => m j.succ) f))

lemma mixedRootIncrement_eq (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (f : FinitePath Ω n → ℝ)
    (z : InteractionSample p) (sel : Fin p → Bool) :
    mixedRootIncrement T Q U V x m f z sel =
      mixedEnergyAvg (KernelTower.tilt n T (fun j => m j.succ) f) Q U V x m z sel := by
  unfold mixedRootIncrement mixedEnergyAvg
  apply FiniteLaw.expect_congr
  intro i
  apply FiniteLaw.expect_congr
  intro r
  rw [← KernelTower.backwardLog_prod_fst n T (KernelTower.piTower n (fun j : Fin p => U (r j)))
    (fun j => m j.succ) f,KernelTower.insertion,KernelTower.tilt_prod_fst]

/-- The local upper interpolation decrement, now a difference of actual
unperturbed root free energies rather than an assumed tilted increment. -/
lemma integral_mixedRoot_combination_nonpos (M : Model p) (hM : Admissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ j,0 ≤ m j)
    (hstrict : ∀ j : Fin n,0 < m j.succ) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (f : FinitePath Ω n → ℝ) (j : Fin p) :
    (∫ z,mixedRootIncrement T Q U V x m f z (fun _ => true) ∂M.disorder.toMeasure)-
      (p:ℝ)*(∫ z,mixedRootIncrement T Q U V x m f z (fun l => decide (l=j)) ∂M.disorder.toMeasure)+
      ((p-1:ℕ):ℝ)*(∫ z,mixedRootIncrement T Q U V x m f z (fun _ => false) ∂M.disorder.toMeasure) ≤0 := by
  simp only [mixedRootIncrement_eq]
  exact integral_mixedEnergy_combination_nonpos M hM _ Q U V x m hm hpos hstrict hroot hend j

end DilutedSpinGlass.PrescribedTree

end

end OAI
