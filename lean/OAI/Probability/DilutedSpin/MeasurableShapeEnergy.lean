import OAI.Probability.DilutedSpin.MeasurableProjector
import OAI.Probability.DilutedSpin.PrefixProjection

namespace OAI

section
section
namespace DilutedSpinGlass.FiniteLaw
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
variable {Ω Z : Type} [Fintype Ω] [MeasurableSpace Z] {N : ℕ}

lemma covarianceEnergy_le_four (P : FiniteLaw Ω) (X : Ω → Fin N → ℝ)
    (hX : ∀ x i, |X x i|≤1) : P.covarianceEnergy X≤4 := by
  by_cases hN : N=0
  · simp [covarianceEnergy,hN]
  · have hpos : 0<(N:ℝ)^2 := sq_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN))
    unfold covarianceEnergy
    apply (div_le_iff₀ hpos).mpr
    calc
      _ ≤ ∑ i : Fin N, ∑ j : Fin N, (4:ℝ) := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        have h1 : |P.expect (fun x => X x i*X x j)|≤1 := P.abs_expect_le (fun x => by
          rw [abs_mul]; exact (mul_le_mul (hX x i) (hX x j) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1))
        have h2 : |P.expect (fun x => X x i)*P.expect (fun x => X x j)|≤1 := by
          rw [abs_mul]
          exact (mul_le_mul (P.abs_expect_le (fun x => hX x i)) (P.abs_expect_le (fun x => hX x j))
            (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
        have h : |P.covariance (fun x => X x i) (fun x => X x j)|≤2 := by
          exact (abs_sub _ _).trans (by linarith)
        have hs := sq_le_sq.mpr (show |P.covariance (fun x => X x i) (fun x => X x j)|≤|(2:ℝ)| by simpa using h)
        norm_num at hs
        exact hs
      _ = _ := by simp; ring

end DilutedSpinGlass.FiniteLaw
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
variable {Ω Z : Type} [Fintype Ω] [MeasurableSpace Z] {n N : ℕ}

lemma measurable_child_expect_tilt (C : PrescribedTree n) (T : KernelTower Ω (n+1))
    (m : Fin (n+1) → ℝ) {f : Z → FinitePath Ω (n+1) → ℝ}
    {g : Z → Ω × C.Sample Ω → ℝ}
    (hf : ∀ y, Measurable (fun z => f z y)) (hg : ∀ a, Measurable (fun z => g z a)) :
    Measurable (fun z => ((KernelTower.tilt (n+1) T m (f z)).1.bind
      (fun a => C.sampleLaw ((KernelTower.tilt (n+1) T m (f z)).2 a))).expect (g z)) := by
  simp_rw [FiniteLaw.expect_bind]
  apply T.1.measurable_tilt_expect (m 0)
  · intro a
    exact KernelTower.measurable_backwardLog n (T.2 a) (fun j => m j.succ) (fun y => hf (a,y))
  · intro a
    exact measurable_tilt_sample_expect C (T.2 a) (fun j => m j.succ)
      (fun y => hf (a,y)) (fun y => hg (a,y))

lemma measurable_childEnergy_tilt (C : PrescribedTree n) (T : KernelTower Ω (n+1))
    (m : Fin (n+1) → ℝ) {f : Z → FinitePath Ω (n+1) → ℝ}
    {X : Z → FinitePath Ω (n+1) → Fin N → ℝ}
    (hf : ∀ y, Measurable (fun z => f z y)) (hX : ∀ y i, Measurable (fun z => X z y i)) :
    Measurable (fun z => childEnergy C (KernelTower.tilt (n+1) T m (f z)) (X z)) := by
  have hY (a : Ω × C.Sample Ω) (i : Fin N) :
      Measurable (fun z => C.leafProduct (fun y => X z (a.1,y) i) a.2) :=
    measurable_leafProduct C (fun y => hX (a.1,y) i) a.2
  unfold childEnergy FiniteLaw.covarianceEnergy FiniteLaw.covariance
  apply Measurable.div_const
  apply Finset.measurable_sum; intro i _
  apply Finset.measurable_sum; intro j _
  apply Measurable.pow_const
  exact (measurable_child_expect_tilt C T m hf (fun a => (hY a i).mul (hY a j))).sub
    ((measurable_child_expect_tilt C T m hf (fun a => hY a i)).mul
      (measurable_child_expect_tilt C T m hf (fun a => hY a j)))

lemma measurable_shapeEnergyAt_tilt (C : PrescribedTree n) (d : ℕ)
    (T : KernelTower Ω (n+1+d)) (m : Fin (n+1+d) → ℝ)
    {f : Z → FinitePath Ω (n+1+d) → ℝ} {X : Z → FinitePath Ω (n+1+d) → Fin N → ℝ}
    (hf : ∀ y, Measurable (fun z => f z y)) (hX : ∀ y i, Measurable (fun z => X z y i)) :
    Measurable (fun z => shapeEnergyAt C d (KernelTower.tilt (n+1+d) T m (f z)) (X z)) := by
  induction d with
  | zero => exact measurable_childEnergy_tilt C T m hf hX
  | succ d ih =>
    apply T.1.measurable_tilt_expect (m 0)
    · intro a
      exact KernelTower.measurable_backwardLog (n+1+d) (T.2 a) (fun j => m j.succ) (fun y => hf (a,y))
    · intro a
      exact ih (T.2 a) (fun j => m j.succ) (fun y => hf (a,y)) (fun y i => hX (a,y) i)

lemma shapeEnergyAt_le_four (C : PrescribedTree n) (d : ℕ)
    (T : KernelTower Ω (n+1+d)) (X : FinitePath Ω (n+1+d) → Fin N → ℝ)
    (hX : ∀ y i, |X y i|≤1) : shapeEnergyAt C d T X≤4 := by
  induction d with
  | zero =>
      unfold shapeEnergyAt childEnergy
      apply FiniteLaw.covarianceEnergy_le_four
      intro a i
      exact leafProduct_bound C (fun y => hX (a.1,y) i) a.2
  | succ d ih =>
      exact (T.1.expect_mono (fun a => ih (T.2 a) (fun y => X (a,y))
        (fun y i => hX (a,y) i))).trans_eq (T.1.expect_const 4)

lemma measurable_descendantEnergyAt_tilt (C : PrescribedTree n) (r d : ℕ)
    (T : KernelTower Ω (n+1+r+1+d)) (m : Fin (n+1+r+1+d) → ℝ)
    {f : Z → FinitePath Ω (n+1+r+1+d) → ℝ} {X : Z → FinitePath Ω (n+1+r+1+d) → Fin N → ℝ}
    (hf : ∀ y, Measurable (fun z => f z y)) (hX : ∀ y i, Measurable (fun z => X z y i)) :
    Measurable (fun z => descendantEnergyAt C r d (KernelTower.tilt (n+1+r+1+d) T m (f z)) (X z)) := by
  induction d with
  | zero => exact measurable_shapeEnergyAt_tilt C (r+1) T m hf hX
  | succ d ih =>
    apply T.1.measurable_tilt_expect (m 0)
    · intro a
      exact KernelTower.measurable_backwardLog (n+1+r+1+d) (T.2 a) (fun j => m j.succ) (fun y => hf (a,y))
    · intro a
      exact ih (T.2 a) (fun j => m j.succ) (fun y => hf (a,y)) (fun y i => hX (a,y) i)

lemma descendantEnergyAt_le_four (C : PrescribedTree n) (r d : ℕ)
    (T : KernelTower Ω (n+1+r+1+d)) (X : FinitePath Ω (n+1+r+1+d) → Fin N → ℝ)
    (hX : ∀ y i, |X y i|≤1) : descendantEnergyAt C r d T X≤4 := by
  induction d with
  | zero => exact shapeEnergyAt_le_four C (r+1) T X hX
  | succ d ih =>
      exact (T.1.expect_mono (fun a => ih (T.2 a) (fun y => X (a,y))
        (fun y i => hX (a,y) i))).trans_eq (T.1.expect_const 4)

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
