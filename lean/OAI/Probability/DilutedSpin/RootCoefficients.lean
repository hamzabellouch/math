import OAI.Probability.DilutedSpin.QIntegration
import OAI.Probability.DilutedSpin.QTopologyBound
import OAI.Probability.DilutedSpin.RootPatternProduct

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

noncomputable def sameTreeCoefficient (a : ℕ) (f : (Fin a → Spin) → ℝ)
    (z : FullRootState Y X I M) : ℝ :=
  (FiniteLaw.uniform : FiniteLaw (Fin a → Site N)).expect (fun i =>
    treeMean S (rootTower T Q m base old z)
      (fun y => f (fun j => V (physical (rootArray z.2.2.1 z.2.2.2) L y) (i j))))

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma sameTreeCoefficient_patterns (a : ℕ) (f : (Fin a → Spin) → ℝ)
    (z : FullRootState Y X I M) :
    sameTreeCoefficient S T Q m base old V a f z =
      rootTreeMean S T Q m base old (fun y => ∑ e : Fin a → S.Leaf → Spin,
        (∏ j, empirical (fun i b => V (y b) i) (e j))*(∏ b, f (fun j => e j b))) z := by
  unfold sameTreeCoefficient
  rw [treeMean_uniform_patterns]
  rfl

include hb in
lemma measurable_sameTreeCoefficient (a : ℕ) (f : (Fin a → Spin) → ℝ) :
    Measurable (sameTreeCoefficient S T Q m base old V a f) := by
  simp_rw [show sameTreeCoefficient S T Q m base old V a f = fun z =>
      rootTreeMean S T Q m base old (fun y => ∑ e : Fin a → S.Leaf → Spin,
        (∏ j, empirical (fun i b => V (y b) i) (e j))*(∏ b, f (fun j => e j b))) z from
    funext (sameTreeCoefficient_patterns S T Q m base old V a f)]
  exact measurable_rootTreeMean S T Q m base old _ hb

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma sameTreeCoefficient_bound (a : ℕ) (f : (Fin a → Spin) → ℝ) (hf : ∀ s, |f s|≤1)
    (z : FullRootState Y X I M) : |sameTreeCoefficient S T Q m base old V a f z|≤1 := by
  apply FiniteLaw.abs_expect_le
  intro i
  exact treeMean_bound S _ (fun y => hf _)

noncomputable def independentTreeCoefficient (a : ℕ) (f : (Fin a → Spin) → ℝ)
    (z : Fin a → FullRootState Y X I M × Site N) : ℝ :=
  treeMean S (KernelTower.pi L (fun i => rootTower T Q m base old (z i).1))
    (fun y => f (fun i => V (physical (rootArray (z i).1.2.2.1 (z i).1.2.2.2) L
      (FinitePath.proj L y i)) (z i).2))

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma independentTreeCoefficient_patterns (a : ℕ) (f : (Fin a → Spin) → ℝ)
    (z : Fin a → FullRootState Y X I M × Site N) :
    independentTreeCoefficient S T Q m base old V a f z =
      ∑ e : Fin a → S.Leaf → Spin,
        (∏ i, rootSitePattern S T Q m base old V (e i) (z i))*(∏ b, f (fun j => e j b)) := by
  unfold independentTreeCoefficient
  have hh := treeMean_pi_patterns (α := fun i : Fin a => rootAlphabet (Ω := Ω) (A := A) (z i).1)
    S (fun i => rootTower T Q m base old (z i).1)
    (fun i y => V (physical (rootArray (z i).1.2.2.1 (z i).1.2.2.2) L y) (z i).2) f
  simpa only [rootSitePattern_eq] using hh

include hb in
lemma measurable_independentTreeCoefficient (a : ℕ) (f : (Fin a → Spin) → ℝ) :
    Measurable (independentTreeCoefficient S T Q m base old V a f) := by
  simp_rw [show independentTreeCoefficient S T Q m base old V a f = fun z =>
      ∑ e : Fin a → S.Leaf → Spin,
        (∏ i, rootSitePattern S T Q m base old V (e i) (z i))*(∏ b, f (fun j => e j b)) from
    funext (independentTreeCoefficient_patterns S T Q m base old V a f)]
  apply Finset.measurable_fun_sum
  intro e _
  apply Measurable.mul_const
  exact Finset.measurable_fun_prod _ (fun i _ =>
    (measurable_rootSitePattern S T Q m base old V hb (e i)).comp (measurable_pi_apply i))

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma independentTreeCoefficient_bound (a : ℕ) (f : (Fin a → Spin) → ℝ)
    (hf : ∀ s, |f s|≤1) (z : Fin a → FullRootState Y X I M × Site N) :
    |independentTreeCoefficient S T Q m base old V a f z|≤1 :=
  treeMean_bound S _ (fun _ => hf _)

include hb in
lemma integral_treeCoefficient_comparison (a : ℕ) (f : (Fin a → Spin) → ℝ) (hf : ∀ s, |f s|≤1) :
    |(∫ z, sameTreeCoefficient S T Q m base old V a f z ∂μ)-
      (∫ z, independentTreeCoefficient S T Q m base old V a f z
        ∂Measure.pi (fun _ : Fin a => μ.prod (siteLaw N)))| ≤
      (a:ℝ)*shapeDeviation μ (rootAlphabet (Ω := Ω) (A := A)) S (rootTower T Q m base old)
        (rootVector (fun y i => spin (V y i))) := by
  simp_rw [sameTreeCoefficient_patterns,independentTreeCoefficient_patterns]
  rw [integral_independent_patterns μ S T Q m base old V hb]
  apply root_pattern_replacement μ S T Q m base old V hb (by omega) a
  intro e
  rw [Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun _ _ => hf _)
end DilutedSpinGlass.HeterogeneousMarks

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
namespace PrescribedTree
variable {β : Type} [Fintype β] {n : ℕ}
lemma expect_qExpect (P : FiniteLaw β) (m : Fin (n+1) → ℝ)
    (F : β → PrescribedTree n → ℝ) (k : ℕ) (S : PrescribedTree n) :
    P.expect (fun z => qExpect m (F z) k S) = qExpect m (fun T => P.expect (fun z => F z T)) k S := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih => simp only [qExpect, FiniteLaw.expect_fintype_sum, FiniteLaw.expect_mul_left, ih]

lemma normalized_backwardLog_tail {Ω : Type} [Fintype Ω] (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hnz : ∀ j : Fin n, m j.succ≠0) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (F : FinitePath Ω n → ℝ) {C : ℝ} (hC : 0≤C) (hF : ∀ y, |F y|≤C) (K : ℕ) :
    |(KernelTower.backwardLog n T (fun i => m i.succ) F-C)-∑ k∈Finset.range K,
      (-1:ℝ)^k/(k+1)*qMoment m T (fun y => normalizedInsertion C (F y)) k (single n)*
        insertionRadius C^(k+1)|≤∑' k : ℕ, |insertionRadius C|^(k+K+1)/(k+K+1) := by
  rw [KernelTower.backwardLog_normalized T m hnz F hC,add_sub_cancel_right]
  exact logInsertion_tail_bound T m hm hpos hnz hroot hend _
    (fun y => normalizedInsertion_bound hC (hF y))
    (by rw [abs_of_pos (insertionRadius_pos hC)]; exact insertionRadius_lt_one _) K
end PrescribedTree

lemma integral_expansion_tail {Z : Type} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    (A : Z → ℝ) (a : Z → ℕ → ℝ) (K : ℕ) (c : ℕ → ℝ) {C R : ℝ}
    (hA : Integrable A μ) (ha : ∀ k, Integrable (fun z => a z k) μ)
    (h : ∀ z, |(A z-C)-∑ k∈Finset.range K,c k*a z k|≤R) :
    |((∫ z, A z ∂μ)-C)-∑ k∈Finset.range K,c k*(∫ z, a z k ∂μ)|≤R := by
  have he : (∑ k∈Finset.range K,c k*(∫ z, a z k ∂μ)) =
      ∫ z, ∑ k∈Finset.range K,c k*a z k ∂μ := by
    rw [integral_finsetSum _ (fun k _ => (ha k).const_mul _)]
    simp only [integral_const_mul]
  have hai : Integrable (fun z => A z-C) μ := hA.sub (integrable_const C)
  have hbi : Integrable (fun z => ∑ k∈Finset.range K,c k*a z k) μ :=
    integrable_finsetSum _ (fun k _ => (ha k).const_mul (c k))
  have hc : (∫ _z : Z, C ∂μ)=C := by simp
  rw [he,← hc,← integral_sub hA (integrable_const C),
    ← integral_sub hai hbi]
  exact abs_integral_le_bound h
end DilutedSpinGlass

end

section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

lemma qExpect_leaf_power {n : ℕ} (m : Fin (n+1) → ℝ)
    (F : PrescribedTree n → ℝ) (c : ℝ) (k : ℕ) (S : PrescribedTree n) :
    qExpect m (fun R => c^R.leaves*F R) k S = c^(S.leaves+k)*qExpect m F k S := by
  induction k generalizing S with
  | zero => simp [qExpect]
  | succ k ih =>
    simp only [qExpect,ih,leaves_grow]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    rw [show S.leaves+1+k=S.leaves+(k+1) by omega]
    ring

variable {Ω : Type} [Fintype Ω]
lemma qMoment_neg {n : ℕ} (m : Fin (n+1) → ℝ) (T : KernelTower Ω n)
    (D : FinitePath Ω n → ℝ) (k : ℕ) (S : PrescribedTree n) :
    qMoment m T (fun y => -D y) k S=(-1:ℝ)^(S.leaves+k)*qMoment m T D k S := by
  unfold qMoment
  have he (R : PrescribedTree n) :
      (sampleLaw R T).expect (leafProduct R (fun y => -D y))=
        (-1:ℝ)^R.leaves*(sampleLaw R T).expect (leafProduct R D) := by
    rw [← FiniteLaw.expect_mul_left]
    apply FiniteLaw.expect_congr
    intro x
    simp only [leafProduct_eq_prod,Finset.prod_neg,Finset.card_univ,card_leaf]
  simp_rw [he]
  exact qExpect_leaf_power _ _ _ _ _

lemma logInsertion_negative_tail {n : ℕ} (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hnz : ∀ j : Fin n,m j.succ≠0) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (D : FinitePath Ω n → ℝ) (hD : ∀ y,|D y|≤1) {t : ℝ} (ht : |t|<1) (K : ℕ) :
    |logInsertion T m D t - ∑ k∈Finset.range K,
      -(t^(k+1)/(k+1))*qMoment m T (fun y => -D y) k (single n)| ≤
      ∑' k : ℕ,|t|^(k+K+1)/(k+K+1) := by
  convert logInsertion_tail_bound T m hm hpos hnz hroot hend D hD ht K using 2
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [qMoment_neg,leaves_single]
  rw [show 1+k=k+1 by omega,pow_succ (-1:ℝ)]
  ring

end DilutedSpinGlass.PrescribedTree

end

end OAI
