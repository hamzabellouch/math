import OAI.Probability.DilutedSpin.PhysicalPairConnection
import OAI.Probability.DilutedSpin.ShapeMatrix

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PrescribedTree ConcreteReservoir
open scoped NNReal BigOperators
variable {Ω X Y : Type} [Fintype Ω] [MeasurableSpace X] [MeasurableSpace Y] {L M N k : ℕ}

variable (S : PrescribedTree (L+1)) (a : S.Leaf) (K : KernelTower Ω (L+1))
    (m : Fin (L+2) → ℝ)
    (base : RootPath Y M → (n : ℕ) → RootPath X n → FinitePath Ω (L+1) → ℝ)
    (old : (i : Labels L (Site N)) → FinitePath Ω (L+1) → FinitePath (Alphabet i.1.1) (L+1) → ℝ)
    (read : Site N → FinitePath Ω (L+1) → Spin)
    (T : PrescribedTree (L+1)) (q : Option (Fin k) → T.Leaf)
    (f : (S.Leaf → FinitePath Ω (L+1)) → ℝ)

/-- A matrix multioverlap at the actual heterogeneous physical root,
retaining the literal old-test transport and root-dependent alphabet. -/
noncomputable def rootMatrixObservable (z : FullRootState Y X (Labels L (Site N)) M) : ℝ :=
  matrixObservableHistory T q
    (rootTower K (fun i => prior i.1.1) (fun j => m j.succ) base old z) m
    (List.ofFn (fun j : Fin k => (some j : Option (Fin k)))).reverse S a
    (spatialProduct (fun _ => rootVector (readVector read) z))
    (fun x => f (fun b => physical (rootArray z.2.2.1 z.2.2.2) (L+1) (S.pathAt b x)))

omit [MeasurableSpace X] [MeasurableSpace Y] in
lemma integral_rootShapeHistory_matrix (z : FullRootState Y X (Labels L (Site N)) M) :
    (∫ i, rootShapeHistory S a K m base old read (matrixSplitTest T q) true f z i ∂siteLaw N) =
      rootMatrixObservable S a K m base old read T q f z := by
  rw [integral_siteLaw]
  symm
  exact matrix_history_spatialProduct_same T q
    (rootTower K (fun i => prior i.1.1) (fun j => m j.succ) base old z) m
    (rootVector (readVector read) z) S a
    (fun x => f (fun b => physical (rootArray z.2.2.1 z.2.2.2) (L+1) (S.pathAt b x)))

variable (hb : ∀ n y, Measurable (fun z : RootPath Y M × RootPath X n => base z.1 n z.2 y))
    (hm : ∀ j : Fin (L+1), m j.succ ≠ 0) (hmono : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last (L+1)) = 1)
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
include hb hm hmono hpos hroot hend hB hf

omit T q in
lemma integrable_rootShapeHistory_general
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure (Labels L (Site N))) [IsProbabilityMeasure ν] (rate score : ℝ≥0)
    (hk : 0 < k) (F : (Option (Fin k) → Option (Fin k) → ℕ) → ℝ) (spinAnchor : Bool) :
    Integrable (fun z : FullRootState Y X (Labels L (Site N)) M × Site N =>
      rootShapeHistory S a K m base old read F spinAnchor f z.1 z.2)
      ((fullRootLaw ξ μ ν rate score).prod (siteLaw N)) := by
  have he : (fun z : FullRootState Y X (Labels L (Site N)) M × Site N =>
      rootShapeHistory S a K m base old read F spinAnchor f z.1 z.2) =
      (fun z => ∑ s : Finset (SharingIndex L (Option (Fin k))),
        BooleanPolynomial.coefficient (fun y => F (splitFromProfile y)) s *
        rootHistory S a K m base old read
          (fun j => (requirementMap s j).1) (fun j => (requirementMap s j).2.1)
          (fun j => (requirementMap s j).2.2) spinAnchor f z.1 z.2) := by
    funext z
    exact rootShapeHistory_expansion S a K m base old read F spinAnchor f z.1 z.2
  rw [he]
  apply integrable_finsetSum
  intro s hs
  exact (integrable_rootHistory ξ μ ν (siteLaw N) rate score S a K m base old read
    (fun j => (requirementMap s j).1) (fun j => (requirementMap s j).2.1)
    (fun j => (requirementMap s j).2.2) spinAnchor f hb hm hmono hpos hroot hend hB hf hk).const_mul _

lemma shapeAverage_matrix (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure (Labels L (Site N))) [IsProbabilityMeasure ν] (rate score : ℝ≥0) (hk : 0 < k) :
    shapeAverage ξ μ ν (siteLaw N) rate score S a K m base old read (matrixSplitTest T q) true f =
      ∫ z, rootMatrixObservable S a K m base old read T q f z ∂fullRootLaw ξ μ ν rate score := by
  unfold shapeAverage
  rw [integral_prod _ (integrable_rootShapeHistory_general S a K m base old read f
    hb hm hmono hpos hroot hend hB hf ξ μ ν rate score hk (matrixSplitTest T q) true)]
  exact integral_congr_ae (ae_of_all _ (fun z => integral_rootShapeHistory_matrix S a K m base old read T q f z))

lemma shapeCovariance_matrix (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure (Labels L (Site N))) [IsProbabilityMeasure ν] (rate score : ℝ≥0) (hk : 0 < k) :
    shapeCovariance ξ μ ν (siteLaw N) rate score S a K m base old read (matrixSplitTest T q) true f =
      matrixRootCovariance (fullRootLaw ξ μ ν rate score)
        (rootAlphabet (Ω := Ω) (A := fun i : Labels L (Site N) => Alphabet i.1.1)) T S q
        (rootTower K (fun i => prior i.1.1) (fun j => m j.succ) base old) m
        (List.ofFn (fun j : Fin k => (some j : Option (Fin k)))).reverse a
        (fun z => spatialProduct (fun _ => rootVector (readVector read) z))
        (fun z x => f (fun b => physical (rootArray z.2.2.1 z.2.2.2) (L+1) (S.pathAt b x))) := by
  unfold shapeCovariance
  rw [shapeAverage_matrix S a K m base old read T q f hb hm hmono hpos hroot hend hB hf
    ξ μ ν rate score hk,
    shapeAverage_matrix S a K m base old read T q (fun _ => 1) hb hm hmono hpos hroot hend
    (by norm_num : (0:ℝ) ≤ 1) (fun _ => by simp) ξ μ ν rate score hk]
  rfl

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
