import OAI.Probability.DilutedSpin.ExternalTaylor
import OAI.Probability.DilutedSpin.FullTreeScore
import OAI.Probability.DilutedSpin.ZeroShape

namespace OAI

section
section
namespace DilutedSpinGlass.ConcreteReservoir
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
lemma integral_siteLaw (N : ℕ) (f : Site N → ℝ) :
    (∫ i, f i ∂siteLaw N) = (∑ i, f i)/(max N 1:ℕ) := by
  rw [siteLaw,PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply,ENNReal.toReal_inv,ENNReal.toReal_natCast,
    smul_eq_mul,Fintype.card_fin]
  simp only [div_eq_mul_inv,Finset.sum_mul,mul_comm]
end DilutedSpinGlass.ConcreteReservoir

namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PrescribedTree ConcreteReservoir
open scoped NNReal BigOperators
variable {Ω X Y : Type} [Fintype Ω] [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}

noncomputable def pairSplitTest (d : ℕ) (B : Option (Fin 1) → Option (Fin 1) → ℕ) : ℝ :=
  if B none (some 0) = d then 1 else 0

def readVector (read : Site N → FinitePath Ω (L+1) → Spin) (x : FinitePath Ω (L+1)) :
    Fin (max N 1) → ℝ := fun i => spin (read i x)

omit [Fintype Ω] in
lemma readVector_bound (read : Site N → FinitePath Ω (L+1) → Spin) (x) (i) :
    |readVector read x i| ≤ 1 := by simp only [readVector,abs_spin,le_refl]

variable (S : PrescribedTree (L+1)) (a : S.Leaf) (T : KernelTower Ω (L+1))
    (m : Fin (L+2) → ℝ)
    (base : RootPath Y M → (n : ℕ) → RootPath X n → FinitePath Ω (L+1) → ℝ)
    (old : (i : Labels L (Site N)) → FinitePath Ω (L+1) → FinitePath (Alphabet i.1.1) (L+1) → ℝ)
    (read : Site N → FinitePath Ω (L+1) → Spin) (d : ℕ)
    (f : (S.Leaf → FinitePath Ω (L+1)) → ℝ)

omit [MeasurableSpace X] [MeasurableSpace Y] in
lemma rootShapeHistory_pair (z : FullRootState Y X (Labels L (Site N)) M) (v : Site N) :
    rootShapeHistory S a T m base old read (pairSplitTest d) true f z v =
      rootPairObservable T (fun i => prior i.1.1) m base old S a d
        (fun x y => spin (read v x)*spin (read v y)) f z := by
  exact shapeHistory_pair
    (rootTower T (fun i => prior i.1.1) (fun j => m j.succ) base old z) m S a d
    (fun x => spin (read v (physical (rootArray z.2.2.1 z.2.2.2) (L+1) x)))
    (fun x => f (fun b => physical (rootArray z.2.2.1 z.2.2.2) (L+1) (S.pathAt b x)))

omit [MeasurableSpace X] [MeasurableSpace Y] in
lemma integral_rootShapeHistory_pair (z : FullRootState Y X (Labels L (Site N)) M) :
    (∫ i, rootShapeHistory S a T m base old read (pairSplitTest d) true f z i ∂siteLaw N) =
      rootPairObservable T (fun i => prior i.1.1) m base old S a d
        (fun x y => FiniteLaw.dot (readVector read x) (readVector read y)) f z := by
  rw [integral_siteLaw]
  symm
  exact pair_history_dot (rootTower T (fun i => prior i.1.1) (fun j => m j.succ) base old z)
    m S a d (rootVector (readVector read) z)
    (fun x => f (fun b => physical (rootArray z.2.2.1 z.2.2.2) (L+1) (S.pathAt b x)))

variable (hb : ∀ n y, Measurable (fun z : RootPath Y M × RootPath X n => base z.1 n z.2 y))
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
include hb hB hf

omit hB hf in
lemma measurable_rootShapeHistory_pair_slice (v : Site N) :
    Measurable (fun z => rootShapeHistory S a T m base old read (pairSplitTest d) true f z v) := by
  have h := measurable_rootPairObservable T (fun i => prior i.1.1) m base old S a d
    (fun x y => spin (read v x)*spin (read v y)) f hb
  have he : rootPairObservable T (fun i => prior i.1.1) m base old S a d
      (fun x y => spin (read v x)*spin (read v y)) f =
      (fun z => rootShapeHistory S a T m base old read (pairSplitTest d) true f z v) :=
    funext (fun z => (rootShapeHistory_pair S a T m base old read d f z v).symm)
  exact he ▸ h

omit hB hf in
lemma measurable_rootShapeHistory_pair : Measurable (fun z : FullRootState Y X (Labels L (Site N)) M × Site N =>
      rootShapeHistory S a T m base old read (pairSplitTest d) true f z.1 z.2) := by
  exact measurable_from_prod_countable_left
    (fun i => measurable_rootShapeHistory_pair_slice S a T m base old read d f hb i)

omit hb [MeasurableSpace X] [MeasurableSpace Y] in
lemma rootShapeHistory_pair_bound (z : FullRootState Y X (Labels L (Site N)) M) (v : Site N) :
    |rootShapeHistory S a T m base old read (pairSplitTest d) true f z v| ≤ pairHistoryMass S m a*B := by
  rw [rootShapeHistory_pair S a T m base old read d f z v]
  apply rootPairObservable_bound T (fun i => prior i.1.1) m base old S a d _ f hB _ hf
  intro x y
  simp only [abs_mul,abs_spin,mul_one,le_refl]

lemma integrable_rootShapeHistory_pair (μ : Measure (FullRootState Y X (Labels L (Site N)) M))
    [IsFiniteMeasure μ] :
    Integrable (fun z : FullRootState Y X (Labels L (Site N)) M × Site N =>
      rootShapeHistory S a T m base old read (pairSplitTest d) true f z.1 z.2) (μ.prod (siteLaw N)) := by
  apply Integrable.of_bound (measurable_rootShapeHistory_pair S a T m base old read d f hb).aestronglyMeasurable
    (pairHistoryMass S m a*B)
  apply ae_of_all
  intro z
  rw [Real.norm_eq_abs]
  exact rootShapeHistory_pair_bound S a T m base old read d f hB hf z.1 z.2

lemma shapeAverage_pair (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure (Labels L (Site N))) [IsProbabilityMeasure ν] (rate score : ℝ≥0) :
    shapeAverage ξ μ ν (siteLaw N) rate score S a T m base old read (pairSplitTest d) true f =
      ∫ z, rootPairObservable T (fun i => prior i.1.1) m base old S a d
        (fun x y => FiniteLaw.dot (readVector read x) (readVector read y)) f z
        ∂fullRootLaw ξ μ ν rate score := by
  unfold shapeAverage
  rw [integral_prod _ (integrable_rootShapeHistory_pair S a T m base old read d f hb hB hf
    (fullRootLaw ξ μ ν rate score))]
  exact integral_congr_ae (ae_of_all _ (fun z => integral_rootShapeHistory_pair S a T m base old read d f z))

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
