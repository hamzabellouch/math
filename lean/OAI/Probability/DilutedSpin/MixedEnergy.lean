import OAI.Probability.DilutedSpin.NormalizedInsertion

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory Filter
open scoped BigOperators Topology

noncomputable def mixedSpinLaw {p : ℕ} (sel : Fin p → Bool) (s : Fin p → Spin) (x : Fin p → ℝ) :
    FiniteLaw (Fin p → Spin) :=
  FiniteLaw.pi (fun l => if sel l then FiniteLaw.point (s l) else qLaw (x l))

lemma mixedSpinLaw_factor {p : ℕ} (z : InteractionSample p)
    (sel : Fin p → Bool) (s : Fin p → Spin) (x : Fin p → ℝ) :
    (mixedSpinLaw sel s x).expect (fun σ => z.2.2.1*∏ l,z.2.2.2 l (σ l))=
      mixedFactor z sel s x := by
  classical
  unfold mixedSpinLaw mixedFactor
  rw [FiniteLaw.expect_mul_left,FiniteLaw.expect_pi_product]
  congr 1
  apply Finset.prod_congr rfl
  intro l _
  cases h : sel l <;> simp only [Bool.false_eq_true,↓reduceIte,FiniteLaw.expect_point]
  rfl

noncomputable def mixedEnergy {p : ℕ} (z : InteractionSample p)
    (sel : Fin p → Bool) (s : Fin p → Spin) (x : Fin p → ℝ) : ℝ :=
  (mixedSpinLaw sel s x).logMean 1 z.1

lemma mixedEnergy_bound {p : ℕ} (z : InteractionSample p)
    (sel : Fin p → Bool) (s : Fin p → Spin) (x : Fin p → ℝ) :
    |mixedEnergy z sel s x|≤‖z.1‖ := by
  have h := (mixedSpinLaw sel s x).logMean_stability (m := 1) zero_lt_one
    (f := z.1) (g := fun _ => 0) (c := ‖z.1‖)
    (fun σ => by simpa only [sub_zero,Real.norm_eq_abs] using norm_le_pi_norm z.1 σ)
  simpa only [mixedEnergy,FiniteLaw.logMean_const _ one_ne_zero,sub_zero] using h

lemma measurable_mixedEnergy {p : ℕ} (sel : Fin p → Bool) (s : Fin p → Spin) (x : Fin p → ℝ) :
    Measurable (fun z : InteractionSample p => mixedEnergy z sel s x) :=
  FiniteLaw.measurable_logMean _ _ (fun σ => by fun_prop)

namespace PrescribedTree
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    {n p N : ℕ} [NeZero N]

noncomputable def mixedTreeEnergy (z : InteractionSample p) (sel : Fin p → Bool)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (r : Fin p → R) (i : Fin p → Fin N) (w : FinitePath (Ω × (Fin p → Λ)) n) : ℝ :=
  mixedEnergy z sel (fun l => V (KernelTower.pathFst n w) (i l))
    (fun l => x (r l) (KernelTower.pathMap (fun a : Fin p → Λ => a l) n (KernelTower.pathSnd n w)))

noncomputable def mixedEnergyAvg (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (z : InteractionSample p) (sel : Fin p → Bool) : ℝ :=
  (FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)))).expect (fun i =>
    (FiniteLaw.pi (fun _ : Fin p => Q)).expect (fun r =>
      KernelTower.backwardLog n (KernelTower.prod n T (KernelTower.piTower n (fun j : Fin p => U (r j))))
        (fun j => m j.succ) (mixedTreeEnergy z sel V x r i)))

lemma measurable_mixedEnergyAvg (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (sel : Fin p → Bool) :
    Measurable (fun z => mixedEnergyAvg T Q U V x m z sel) := by
  apply FiniteLaw.measurable_expect
  intro i
  apply FiniteLaw.measurable_expect
  intro r
  apply KernelTower.measurable_backwardLog
  intro y
  exact measurable_mixedEnergy sel _ _

lemma mixedEnergyAvg_bound (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : ∀ j : Fin n,0 < m j.succ)
    (z : InteractionSample p) (sel : Fin p → Bool) :
    |mixedEnergyAvg T Q U V x m z sel|≤‖z.1‖ := by
  apply FiniteLaw.abs_expect_le
  intro i
  apply FiniteLaw.abs_expect_le
  intro r
  exact KernelTower.backwardLog_bound n _ _ hm (fun y => mixedEnergy_bound z sel _ _)

lemma integrable_mixedEnergyAvg (M : Model p) (hM : Admissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : ∀ j : Fin n,0 < m j.succ) (sel : Fin p → Bool) :
    Integrable (fun z => mixedEnergyAvg T Q U V x m z sel) M.disorder.toMeasure := by
  apply hM.interaction_integrable.mono' (measurable_mixedEnergyAvg T Q U V x m sel).aestronglyMeasurable
  exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using mixedEnergyAvg_bound T Q U V x m hm z sel)

end PrescribedTree
end DilutedSpinGlass

end

end OAI
