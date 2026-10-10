import OAI.Probability.DilutedSpin.FullThermalAverage
import OAI.Probability.DilutedSpin.SingletonRoot
import OAI.Probability.DilutedSpin.TreeMeasurable

namespace OAI

section
section
namespace DilutedSpinGlass.KernelTower
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
variable {Ω Z : Type} [Fintype Ω] [MeasurableSpace Z] {N : ℕ}

lemma measurable_covarianceEnergy_tilt (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    {f : Z → FinitePath Ω n → ℝ} {X : Z → FinitePath Ω n → Fin N → ℝ}
    (hf : ∀ y, Measurable (fun z => f z y)) (hX : ∀ y i, Measurable (fun z => X z y i)) :
    Measurable (fun z => (law n (tilt n T m (f z))).covarianceEnergy (X z)) := by
  unfold FiniteLaw.covarianceEnergy FiniteLaw.covariance
  apply Measurable.div_const
  apply Finset.measurable_sum; intro i _
  apply Finset.measurable_sum; intro j _
  apply Measurable.pow_const
  exact (measurable_path_expect n T m hf (fun y => (hX y i).mul (hX y j))).sub
    ((measurable_path_expect n T m hf (fun y => hX y i)).mul
      (measurable_path_expect n T m hf (fun y => hX y j)))

lemma measurable_prefixEnergyAt_tilt (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (d : ℕ) {f : Z → FinitePath Ω n → ℝ} {X : Z → FinitePath Ω n → Fin N → ℝ}
    (hf : ∀ y, Measurable (fun z => f z y)) (hX : ∀ y i, Measurable (fun z => X z y i)) :
    Measurable (fun z => prefixEnergyAt n (tilt n T m (f z)) d (X z)) := by
  induction n generalizing d with
  | zero => exact measurable_covarianceEnergy_tilt 0 T m hf hX
  | succ n ih =>
    cases d with
    | zero => exact measurable_covarianceEnergy_tilt (n+1) T m hf hX
    | succ d =>
      apply T.1.measurable_tilt_expect (m 0)
      · intro a
        exact measurable_backwardLog n (T.2 a) (fun j => m j.succ) (fun y => hf (a,y))
      · intro a
        exact ih (T.2 a) (fun j => m j.succ) d (fun y => hf (a,y)) (fun y i => hX (a,y) i)

lemma prefixEnergyAt_le_two (n : ℕ) (T : KernelTower Ω n) (d : ℕ) (hd : d < n)
    (X : FinitePath Ω n → Fin N → ℝ) (hX : ∀ x i, |X x i| ≤ 1) :
    prefixEnergyAt n T d X ≤ 2 := by
  have h3 := prefix_three_copy_bound_at n T d hd X
  have hb : tripleExpectAt n T d
      (fun x y z => (FiniteLaw.dot (X x) (X y)-FiniteLaw.dot (X x) (X z))^2) ≤ 4 := by
    clear h3
    induction n generalizing d with
    | zero => omega
    | succ n ih =>
      cases d with
      | zero =>
        change (law (n+1) T).expect _ ≤ _
        calc
          _ ≤ (law (n+1) T).expect (fun _ => (4:ℝ)) := by
            apply FiniteLaw.expect_mono; intro x
            calc
              _ ≤ (law (n+1) T).expect (fun _ => (4:ℝ)) := by
                apply FiniteLaw.expect_mono; intro y
                calc
                  _ ≤ (law (n+1) T).expect (fun _ => (4:ℝ)) := by
                    apply FiniteLaw.expect_mono; intro z
                    have ha := FiniteLaw.abs_dot_le_one (X x) (X y) (hX x) (hX y)
                    have hb := FiniteLaw.abs_dot_le_one (X x) (X z) (hX x) (hX z)
                    rcases abs_le.mp ha with ⟨ha,ha'⟩
                    rcases abs_le.mp hb with ⟨hb,hb'⟩
                    nlinarith [sq_nonneg (FiniteLaw.dot (X x) (X y)-FiniteLaw.dot (X x) (X z))]
                  _ = _ := FiniteLaw.expect_const _ _
              _ = _ := FiniteLaw.expect_const _ _
          _ = _ := FiniteLaw.expect_const _ _
      | succ d =>
        exact (T.1.expect_mono (fun z => ih (T.2 z) d (by omega) (fun y => X (z,y))
          (fun y i => hX (z,y) i))).trans_eq (T.1.expect_const 4)
  linarith

end DilutedSpinGlass.KernelTower
end

end

end OAI
