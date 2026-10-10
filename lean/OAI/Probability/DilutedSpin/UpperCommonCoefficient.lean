import OAI.Probability.DilutedSpin.CommonTreeSample
import OAI.Probability.DilutedSpin.RootCoefficients

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    {n p N : ℕ} [NeZero N]

noncomputable def mixedLeafAvg (S : PrescribedTree n) (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (z : InteractionSample p) (sel : Fin p → Bool) : ℝ :=
  (FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)))).expect (fun i =>
    (FiniteLaw.pi (fun _ : Fin p => Q)).expect (fun r =>
      (S.sampleLaw (KernelTower.prod n T (KernelTower.piTower n (fun j : Fin p => U (r j))))).expect
        (leafProduct S (fun y => -mixedTreeD z sel V x r i y))))

lemma measurable_mixedLeafAvg (S : PrescribedTree n) (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (sel : Fin p → Bool) : Measurable (fun z => mixedLeafAvg S T Q U V x z sel) := by
  unfold mixedLeafAvg
  simp_rw [common_tree_point]
  exact FiniteLaw.measurable_expect _ (fun old => measurable_insertionPoint _ _ _ _)

lemma mixedLeafAvg_bound (S : PrescribedTree n) (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (z : InteractionSample p) (hz : ∀ s : Fin p → Spin,|z.2.2.1*∏ l,z.2.2.2 l (s l)|≤1)
    (sel : Fin p → Bool) : |mixedLeafAvg S T Q U V x z sel|≤1 := by
  rw [mixedLeafAvg,common_tree_point]
  exact FiniteLaw.abs_expect_le _ (fun old => insertionPoint_bound z hz _ _ _ _)

lemma integrable_mixedLeafAvg (M : Model p) (hM : Admissible M)
    (S : PrescribedTree n) (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (sel : Fin p → Bool) : Integrable (fun z => mixedLeafAvg S T Q U V x z sel) M.disorder.toMeasure := by
  apply Integrable.of_bound (measurable_mixedLeafAvg S T Q U V x sel).aestronglyMeasurable 1
  filter_upwards [hM.factorization] with z hz
  simpa only [Real.norm_eq_abs] using mixedLeafAvg_bound S T Q U V x z (fun s => (hz.2 s).2.le) sel

lemma integratedMixedLeaf_identity (M : Model p) (hM : Admissible M)
    (S : PrescribedTree n) (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (sel : Fin p → Bool) :
    (∫ z,mixedLeafAvg S T Q U V x z sel ∂M.disorder.toMeasure)=
    (S.sampleLaw T).expect (fun old => insertionCoefficient M
      (fun i a => V (S.pathAt ((Fintype.equivFin S.Leaf).symm a) old) i)
      (Q.bind (fun r => S.sampleLaw (U r)))
      (fun w a => x w.1 (S.pathAt ((Fintype.equivFin S.Leaf).symm a) w.2)) sel) := by
  unfold mixedLeafAvg
  simp_rw [common_tree_point]
  exact integral_expected_insertionPoint M hM _ _ _ _ _

lemma integratedMixedLeaf_combination_nonneg (M : Model p) (hM : Admissible M)
    (S : PrescribedTree n) (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ) (j : Fin p) :
    0 ≤ (∫ z,mixedLeafAvg S T Q U V x z (fun _ => true) ∂M.disorder.toMeasure)-
      (p:ℝ)*(∫ z,mixedLeafAvg S T Q U V x z (fun l => decide (l=j)) ∂M.disorder.toMeasure)+
      ((p-1:ℕ):ℝ)*(∫ z,mixedLeafAvg S T Q U V x z (fun _ => false) ∂M.disorder.toMeasure) := by
  simp only [integratedMixedLeaf_identity M hM]
  apply expected_insertionCoefficient_nonneg M hM
  rw [card_leaf]
  exact leaves_pos S

lemma qExpect_expect {A : Type} [Fintype A] (P : FiniteLaw A)
    (m : Fin (n+1) → ℝ) (F : A → PrescribedTree n → ℝ) (k : ℕ) (S : PrescribedTree n) :
    qExpect m (fun S => P.expect (fun a => F a S)) k S =
      P.expect (fun a => qExpect m (F a) k S) := by
  unfold FiniteLaw.expect
  rw [qExpect_sum]
  apply Finset.sum_congr rfl
  intro a _
  simpa only [mul_comm (P.weight a)] using qExpect_mul_const m (F a) (P.weight a) k S

lemma qExpect_linear_combination (m : Fin (n+1) → ℝ)
    (F G H : PrescribedTree n → ℝ) (a b : ℝ) (k : ℕ) (S : PrescribedTree n) :
    qExpect m (fun S => F S-a*G S+b*H S) k S =
      qExpect m F k S-a*qExpect m G k S+b*qExpect m H k S := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih =>
    simp only [qExpect,ih,mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib]
    congr 1
    · congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      ring
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      ring

lemma mixedQMoment_combination_nonneg (M : Model p) (hM : Admissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (k : ℕ) (S : PrescribedTree n) (j : Fin p) :
    0 ≤ qExpect m (fun S => ∫ z,mixedLeafAvg S T Q U V x z (fun _ => true) ∂M.disorder.toMeasure) k S-
      (p:ℝ)*qExpect m (fun S => ∫ z,mixedLeafAvg S T Q U V x z (fun l => decide (l=j)) ∂M.disorder.toMeasure) k S+
      ((p-1:ℕ):ℝ)*qExpect m (fun S => ∫ z,mixedLeafAvg S T Q U V x z (fun _ => false) ∂M.disorder.toMeasure) k S := by
  rw [← qExpect_linear_combination]
  exact qExpect_nonneg m hm hpos _ (fun S => integratedMixedLeaf_combination_nonneg M hM S T Q U V x j) k S

end DilutedSpinGlass.PrescribedTree

end

end OAI
