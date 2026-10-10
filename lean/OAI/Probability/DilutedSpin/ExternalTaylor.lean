import OAI.Probability.DilutedSpin.MatrixPair
import OAI.Probability.DilutedSpin.ParameterRate
import OAI.Probability.DilutedSpin.UniformRootDecorrelation

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory PrescribedTree
open scoped NNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}

noncomputable def rootPairObservable (T : KernelTower Ω L)
    (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (S : PrescribedTree L) (a : S.Leaf) (d : ℕ)
    (R : FinitePath Ω L → FinitePath Ω L → ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ)
    (z : FullRootState Y X I M) : ℝ :=
  pairObservableHistory (rootTower T Q (fun j => m j.succ) base old z) m S a d
    (fun x y => R (physical (rootArray z.2.2.1 z.2.2.2) L x) (physical (rootArray z.2.2.1 z.2.2.2) L y))
    (fun x => f (fun b => physical (rootArray z.2.2.1 z.2.2.2) L (S.pathAt b x)))

variable (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (S : PrescribedTree L) (a : S.Leaf) (d : ℕ)
    (R : FinitePath Ω L → FinitePath Ω L → ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

include hb in
lemma measurable_rootPairObservable : Measurable (rootPairObservable T Q m base old S a d R f) := by
  change Measurable (packRoot (fun h k x n y => pairObservableHistory
    (KernelTower.tilt L (tower (rootArray n y) L T Q) (fun j => m j.succ)
      (logWeight (base h k x) (rootArray n y) old)) m S a d
    (fun x y' => R (physical (rootArray n y) L x) (physical (rootArray n y) L y'))
    (fun x => f (fun b => physical (rootArray n y) L (S.pathAt b x)))))
  apply measurable_packRoot
  intro k n
  apply measurable_from_prod_countable_left
  intro y
  dsimp only
  exact measurable_pairObservableHistory_tilt (tower (rootArray n y) L T Q) (fun j => m j.succ)
    m S a d (fun w => (hb k _).add measurable_const) (fun _ _ => measurable_const)
    (fun _ => measurable_const)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] in
lemma rootPairObservable_bound {B : ℝ} (hB : 0 ≤ B)
    (hR : ∀ x y, |R x y| ≤ 1) (hf : ∀ x, |f x| ≤ B) (z : FullRootState Y X I M) :
    |rootPairObservable T Q m base old S a d R f z| ≤ pairHistoryMass S m a*B :=
  pairObservableHistory_bound _ m S a d _ _ hB (fun _ _ => hR _ _) (fun _ => hf _)

include hb in
lemma integrable_rootPairObservable (μ : Measure (FullRootState Y X I M)) [IsFiniteMeasure μ]
    {B : ℝ} (hB : 0 ≤ B) (hR : ∀ x y, |R x y| ≤ 1) (hf : ∀ x, |f x| ≤ B) :
    Integrable (rootPairObservable T Q m base old S a d R f) μ := by
  apply Integrable.of_bound (measurable_rootPairObservable T Q m base old S a d R f hb).aestronglyMeasurable
    (pairHistoryMass S m a*B)
  exact ae_of_all _ (fun z => by
    simpa only [Real.norm_eq_abs] using (rootPairObservable_bound T Q m base old S a d R f hB hR hf z))

end DilutedSpinGlass.HeterogeneousMarks
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory
variable {Ω Z : Type} [Fintype Ω] [MeasurableSpace Z] {n : ℕ}

/-- Measurability of every coefficient of the actual finite extension
recursion, from measurable old-tree expectations. -/
theorem measurable_anchorIterate_zero (T : Z → KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : ∀ j : Fin n, m j.succ ≠ 0)
    (hT : ∀ (S : PrescribedTree n) (G : S.Sample Ω → ℝ),
      Measurable (fun z => (S.sampleLaw (T z)).expect G))
    (D : FinitePath Ω n → ℝ) {ι : Type} [DecidableEq ι]
    (k : ℕ) (S : PrescribedTree n) (A : Finset ι)
    (U : ι → S.Sample Ω → FinitePath Ω n) (G : S.Sample Ω → ℝ) :
    Measurable (fun z => anchorIterate (T z) m D k S A U G 0) := by
  induction k generalizing S A with
  | zero => simpa only [anchorIterate,anchorEval_zero S _ m hm] using hT S G
  | succ k ih =>
    apply Measurable.add
    · exact Finset.measurable_sum _ (fun i _ => ih S (A.erase i) U _)
    · exact Finset.measurable_sum _ (fun v _ => (ih (grow S v) A _ _).const_mul _)

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
variable {Ω I Z : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [MeasurableSpace Z] {L n : ℕ}

noncomputable def externalCoefficient (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin n → I) (i : I)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (D E : FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) (k : ℕ) : ℝ :=
  PrescribedTree.anchorCoefficient S
    (KernelTower.prod L (KernelTower.tilt L (tower roots L T Q) (fun j => m j.succ)
      (logWeight base roots old)) (markPrior L (Q i))) m
    (fun y => D (physical roots L (KernelTower.pathFst L y)) (KernelTower.pathSnd L y)) a
    (fun x => f (fun b => physical roots L (KernelTower.pathFst L (S.pathAt b x))) *
      E (physical roots L (KernelTower.pathFst L (S.pathAt a x)))
        (KernelTower.pathSnd L (S.pathAt a x))) k

lemma measurable_externalTreeScore (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : Z → FinitePath Ω L → ℝ) (roots : Fin n → I) (i : I)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (new E : FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ)
    (hb : ∀ y, Measurable (fun z => base z y)) :
    Measurable (fun z => externalTreeScore S a T Q m (base z) roots i old new E f) := by
  unfold externalTreeScore
  simp_rw [← KernelTower.tilt_prod_fst,KernelTower.tilt_insertion]
  refine PrescribedTree.measurable_tilt_sample_expect S
    (KernelTower.prod L (tower roots L T Q) (markPrior L (Q i))) m ?_ ?_
  · exact fun y => ((hb _).add measurable_const).add measurable_const
  · exact fun x => measurable_const

lemma measurable_externalCoefficient (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ j : Fin L, m j.succ ≠ 0)
    (base : Z → FinitePath Ω L → ℝ) (roots : Fin n → I) (i : I)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (D E : FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) (k : ℕ)
    (hb : ∀ y, Measurable (fun z => base z y)) :
    Measurable (fun z => externalCoefficient S a T Q m (base z) roots i old D E f k) := by
  unfold externalCoefficient PrescribedTree.anchorCoefficient
  apply Measurable.div_const
  apply PrescribedTree.measurable_anchorIterate_zero _ m hm
  intro S G
  simp_rw [← KernelTower.tilt_prod_fst]
  refine PrescribedTree.measurable_tilt_sample_expect S
    (KernelTower.prod L (tower roots L T Q) (markPrior L (Q i))) (fun j => m j.succ) ?_ ?_
  · exact fun y => (hb _).add measurable_const
  · exact fun x => measurable_const

lemma abs_externalTreeScore_le (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin n → I) (i : I)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (new E : FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) {B : ℝ}
    (hf : ∀ x, |f x| ≤ B) (hE : ∀ x y, |E x y| ≤ 1) (hA : ∀ x y, 1/2 ≤ new x y) :
    |externalTreeScore S a T Q m base roots i old new E f| ≤ 2*B := by
  apply FiniteLaw.abs_expect_le
  intro x
  let xa := physical roots L (KernelTower.pathFst L (S.pathAt a x))
  let ya := KernelTower.pathSnd L (S.pathAt a x)
  have hp : 0 < new xa ya := lt_of_lt_of_le (by norm_num) (hA xa ya)
  change |f (fun b => physical roots L (KernelTower.pathFst L (S.pathAt b x))) * (E xa ya/new xa ya)| ≤ 2*B
  rw [abs_mul,abs_div,abs_of_pos hp]
  have hq : |E xa ya| / new xa ya ≤ 2 := by
    apply (div_le_iff₀ hp).mpr
    linarith [hE xa ya,hA xa ya]
  have hB : 0 ≤ B := (abs_nonneg _).trans (hf (fun b => physical roots L (KernelTower.pathFst L (S.pathAt b x))))
  calc
    _ ≤ B*2 := mul_le_mul (hf _) hq (div_nonneg (abs_nonneg _) hp.le) hB
    _ = 2*B := mul_comm _ _

variable (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ j : Fin L, m j.succ ≠ 0) (hmono : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last L) = 1)
    (base : FinitePath Ω L → ℝ) (roots : Fin n → I) (i : I)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (D E : FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) {B : ℝ}
    (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B) (hD : ∀ x y, |D x y| ≤ 1) (hE : ∀ x y, |E x y| ≤ 1)

include hmono hpos hroot hend hB hf hD hE in
lemma externalCoefficient_bound (k : ℕ) :
    |externalCoefficient S a T Q m base roots i old D E f k| ≤
      B*PrescribedTree.derivativeBound (S.leaves+(Finset.univ.erase a).card) k/(k.factorial:ℝ) := by
  unfold externalCoefficient PrescribedTree.anchorCoefficient
  rw [abs_div,abs_of_nonneg (by positivity : (0:ℝ) ≤ (k.factorial:ℝ))]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply PrescribedTree.abs_anchorIterate_le _ m hmono hpos hroot hend _ (fun y => hD _ _) k S _ _ _ hB
  · intro x
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul (hf _) (hE _ _) (abs_nonneg _) hB
  · norm_num

include hm hmono hpos hroot hend hB hf hD hE in
 
lemma externalTreeScore_sub_le {t u : ℝ} (ht : |t| ≤ 1/4) (huz : 0 ≤ u) (hu : u ≤ 1/4) :
    |externalTreeScore S a T Q (fun j => m j.succ) base roots i old
        (fun x y => 1+t*D x y+u*E x y) E f -
      externalTreeScore S a T Q (fun j => m j.succ) base roots i old
        (fun x y => 1+t*D x y) E f| ≤ (4+8*(S.leaves:ℝ))*B*u := by
  rw [external_eq_anchorInsertion,external_eq_anchorInsertion]
  apply PrescribedTree.anchorInsertion_sub_le S _ m hm hmono hpos hroot hend a _ _ _ hB
  · intro x
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul (hf _) (hE _ _) (abs_nonneg _) hB
  · exact fun y => hD _ _
  · exact fun y => hE _ _
  · exact ht
  · exact huz
  · exact hu

include hm hmono hpos hroot hend hB hf hD hE in
lemma externalTreeScore_taylor_bound {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) (1/2)) (k : ℕ) :
    |externalTreeScore S a T Q (fun j => m j.succ) base roots i old
        (fun x y => 1+t*D x y) E f -
      ∑ j ∈ Finset.range (k+1), externalCoefficient S a T Q m base roots i old D E f j*t^j| ≤
        (B*PrescribedTree.derivativeBound (S.leaves+(Finset.univ.erase a).card) (k+1)/(k.factorial:ℝ))*t^(k+1) := by
  rw [external_eq_anchorInsertion]
  apply PrescribedTree.anchorInsertion_taylor_bound S _ m hm hmono hpos hroot hend _ (fun y => hD _ _) a _ hB
  · intro x
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul (hf _) (hE _ _) (abs_nonneg _) hB
  · exact ht

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
