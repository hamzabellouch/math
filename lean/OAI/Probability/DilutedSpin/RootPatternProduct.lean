import OAI.Probability.DilutedSpin.RootEncoding
import OAI.Probability.DilutedSpin.RootPatternComparison

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory PrescribedTree Pattern ConcreteReservoir
open scoped BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}
variable (μ : Measure (FullRootState Y X I M)) [IsProbabilityMeasure μ]
    (S : PrescribedTree L) (T : KernelTower Ω L)
    (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (V : FinitePath Ω L → Site N → Spin)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

noncomputable def rootSitePattern (e : S.Leaf → Spin)
    (z : FullRootState Y X I M × Site N) : ℝ :=
  rootTreeMean S T Q m base old (fun y => if (fun a => V (y a) z.2)=e then 1 else 0) z.1

include hb in
lemma measurable_rootSitePattern (e : S.Leaf → Spin) :
    Measurable (rootSitePattern S T Q m base old V e) := by
  unfold rootSitePattern
  apply measurable_from_prod_countable_left
  intro i
  exact measurable_rootTreeMean S T Q m base old
    (fun y : S.Leaf → FinitePath Ω L => if (fun a => V (y a) i)=e then 1 else 0) hb

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma rootSitePattern_bound (e : S.Leaf → Spin) (z : FullRootState Y X I M × Site N) :
    |rootSitePattern S T Q m base old V e z|≤1 :=
  rootTreeMean_bound S T Q m base old _ (fun y => by split_ifs <;> norm_num) z.1

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma rootSitePattern_eq (e : S.Leaf → Spin) (z : FullRootState Y X I M × Site N) :
    rootSitePattern S T Q m base old V e z =
      patternMass S (rootTower T Q m base old z.1)
        (fun y => V (physical (rootArray z.1.2.2.1 z.1.2.2.2) L y) z.2) e := by
  apply FiniteLaw.expect_congr
  intro w
  dsimp only

include hb in
lemma integral_rootSitePattern (e : S.Leaf → Spin) :
    (∫ z, rootSitePattern S T Q m base old V e z ∂μ.prod (siteLaw N)) =
      rootPatternMass μ S T Q m base old V e := by
  have hi : Integrable (rootSitePattern S T Q m base old V e) (μ.prod (siteLaw N)) :=
    (bounded_memLp (measurable_rootSitePattern S T Q m base old V hb e)
      (rootSitePattern_bound S T Q m base old V e) 1).integrable le_rfl
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [integral_siteLaw]
  change (∑ i : Site N, (sampleLaw S (rootTower T Q m base old z)).expect
    (fun w => if (fun a => V (physical (rootArray z.2.2.1 z.2.2.2) L (S.pathAt a w)) i)=e then 1 else 0)) / (max N 1:ℕ) = _
  rw [← FiniteLaw.expect_fintype_sum,← FiniteLaw.expect_div]
  apply FiniteLaw.expect_congr
  intro w
  rfl

include hb in
lemma integral_independent_patterns (a : ℕ) (f : (Fin a → S.Leaf → Spin) → ℝ) :
    (∫ z : Fin a → FullRootState Y X I M × Site N,
      ∑ e : Fin a → S.Leaf → Spin,
        (∏ i, rootSitePattern S T Q m base old V (e i) (z i))*f e
      ∂Measure.pi (fun _ : Fin a => μ.prod (siteLaw N))) =
      ∑ e, (∏ i, rootPatternMass μ S T Q m base old V (e i))*f e := by
  have hip (e : Fin a → S.Leaf → Spin) : Integrable
      (fun z : Fin a → FullRootState Y X I M × Site N =>
        ∏ i, rootSitePattern S T Q m base old V (e i) (z i))
      (Measure.pi (fun _ : Fin a => μ.prod (siteLaw N))) := by
    apply (bounded_memLp (Finset.measurable_fun_prod _ (fun i _ =>
      (measurable_rootSitePattern S T Q m base old V hb (e i)).comp (measurable_pi_apply i)))
      (B := 1) ?_ 1).integrable le_rfl
    intro z
    rw [Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun i _ => rootSitePattern_bound S T Q m base old V (e i) (z i))
  rw [integral_finsetSum _ (fun e _ => (hip e).mul_const _)]
  simp only [integral_mul_const]
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  rw [integral_fintype_prod_eq_prod]
  exact Finset.prod_congr rfl (fun i _ => integral_rootSitePattern μ S T Q m base old V hb (e i))

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
