import OAI.Probability.DilutedSpin.MixedPatterns
import OAI.Probability.DilutedSpin.RootCoefficients

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory PrescribedTree KernelTower ConcreteReservoir
open scoped BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}
variable (T : KernelTower Ω (L+1)) (Q : (i : I) → Fin (L+1) → FiniteLaw (A i))
    (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω (L+1) → ℝ)
    (old : (i : I) → FinitePath Ω (L+1) → FinitePath (A i) (L+1) → ℝ)
    (V : FinitePath Ω (L+1) → Site N → Spin)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

noncomputable def sameInsertionAverage (a : ℕ) (F : (Fin a → Spin) → ℝ)
    (z : FullRootState Y X I M) : ℝ :=
  (FiniteLaw.uniform : FiniteLaw (Fin a → Site N)).expect (fun i => rootInsertion T Q m base old V a F (z,i))

include hb in
lemma measurable_sameInsertionAverage (a : ℕ) (F : (Fin a → Spin) → ℝ) :
    Measurable (sameInsertionAverage T Q m base old V a F) := by
  unfold sameInsertionAverage FiniteLaw.expect
  exact Finset.measurable_fun_sum _ (fun i _ =>
    ((measurable_rootInsertion T Q m base old V hb a F).comp
      (measurable_id.prodMk measurable_const)).const_mul _)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma sameInsertionAverage_bound (hm : ∀ i, 0 < m i) (a : ℕ)
    (F : (Fin a → Spin) → ℝ) {C : ℝ} (hF : ∀ s, |F s|≤C) (z : FullRootState Y X I M) :
    |sameInsertionAverage T Q m base old V a F z|≤C := by
  apply FiniteLaw.abs_expect_le
  intro i
  exact backwardLog_bound (L+1) _ m hm (fun y => hF _)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma independentInsertion_bound (hm : ∀ i, 0 < m i) (a : ℕ)
    (F : (Fin a → Spin) → ℝ) {C : ℝ} (hF : ∀ s, |F s|≤C)
    (z : Fin a → FullRootState Y X I M × Site N) :
    |independentInsertion T Q m base old V a F z|≤C :=
  backwardLog_bound (L+1) _ m hm (fun _ => hF _)

variable (q : Fin (L+2) → ℝ)
omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma same_qMoment (a : ℕ) (f : (Fin a → Spin) → ℝ) (k : ℕ) (S : PrescribedTree (L+1))
    (z : FullRootState Y X I M) :
    (FiniteLaw.uniform : FiniteLaw (Fin a → Site N)).expect (fun i =>
      qMoment q (rootTower T Q m base old z)
        (fun y => f (fun j => V (physical (rootArray z.2.2.1 z.2.2.2) (L+1) y) (i j))) k S) =
      qExpect q (fun R => sameTreeCoefficient R T Q m base old V a f z) k S := by
  simp only [qMoment, ← treeMean_eq_expect]
  rw [expect_qExpect]
  rfl

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma sameInsertionAverage_tail (hm : Monotone q) (hpos : ∀ j, 0 ≤ q j)
    (hnz : ∀ j : Fin (L+1), q j.succ≠0) (hroot : q 0=0) (hend : q (Fin.last (L+1))=1)
    (a : ℕ) (F : (Fin a → Spin) → ℝ) {C : ℝ} (hC : 0≤C) (hF : ∀ s, |F s|≤C)
    (z : FullRootState Y X I M) (K : ℕ) :
    |(sameInsertionAverage T Q (fun i => q i.succ) base old V a F z-C)-
      ∑ k∈Finset.range K, (-1:ℝ)^k/(k+1)*
        qExpect q (fun R => sameTreeCoefficient R T Q (fun i => q i.succ) base old V a
          (fun s => normalizedInsertion C (F s)) z) k (single (L+1))*insertionRadius C^(k+1)| ≤
      ∑' k : ℕ, |insertionRadius C|^(k+K+1)/(k+K+1) := by
  have hh := (FiniteLaw.uniform : FiniteLaw (Fin a → Site N)).abs_expect_le (fun i =>
    normalized_backwardLog_tail (rootTower T Q (fun j => q j.succ) base old z)
      q hm hpos hnz hroot hend
      (fun y => F (fun j => V (physical (rootArray z.2.2.1 z.2.2.2) (L+1) y) (i j)))
      hC (fun y => hF _) K)
  simp only [FiniteLaw.expect_sub,FiniteLaw.expect_const,FiniteLaw.expect_sum,
    FiniteLaw.expect_mul_left,FiniteLaw.expect_mul_right] at hh
  change |(sameInsertionAverage T Q (fun i => q i.succ) base old V a F z-C)-
    ∑ k∈Finset.range K, (-1:ℝ)^k/(k+1)*
      (FiniteLaw.uniform : FiniteLaw (Fin a → Site N)).expect (fun i =>
        qMoment q (rootTower T Q (fun j => q j.succ) base old z)
          (fun y => normalizedInsertion C (F (fun j =>
            V (physical (rootArray z.2.2.1 z.2.2.2) (L+1) y) (i j)))) k (single (L+1)))*
        insertionRadius C^(k+1)| ≤ _ at hh
  simp_rw [same_qMoment T Q (fun i => q i.succ) base old V q a
    (fun s => normalizedInsertion C (F s))] at hh
  exact hh

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma independentInsertion_tail (hm : Monotone q) (hpos : ∀ j, 0 ≤ q j)
    (hnz : ∀ j : Fin (L+1), q j.succ≠0) (hroot : q 0=0) (hend : q (Fin.last (L+1))=1)
    (a : ℕ) (F : (Fin a → Spin) → ℝ) {C : ℝ} (hC : 0≤C) (hF : ∀ s, |F s|≤C)
    (z : Fin a → FullRootState Y X I M × Site N) (K : ℕ) :
    |(independentInsertion T Q (fun i => q i.succ) base old V a F z-C)-
      ∑ k∈Finset.range K, (-1:ℝ)^k/(k+1)*
        qExpect q (fun R => independentTreeCoefficient R T Q (fun i => q i.succ) base old V a
          (fun s => normalizedInsertion C (F s)) z) k (single (L+1))*insertionRadius C^(k+1)| ≤
      ∑' k : ℕ, |insertionRadius C|^(k+K+1)/(k+K+1) := by
  have hh := normalized_backwardLog_tail
    (KernelTower.pi (L+1) (fun i : Fin a => rootTower T Q (fun j => q j.succ) base old (z i).1))
    q hm hpos hnz hroot hend
    (fun y => F (fun i => V
      (physical (rootArray (z i).1.2.2.1 (z i).1.2.2.2) (L+1) (FinitePath.proj (L+1) y i)) (z i).2))
    hC (fun y => hF _) K
  simpa only [qMoment,← treeMean_eq_expect, independentInsertion,
    independentTreeCoefficient] using hh
end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
