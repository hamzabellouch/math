import OAI.Probability.DilutedSpin.MarkerRootIdentity

namespace OAI

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
noncomputable def rootMarkerObservable (z : FullRootState Y X (Labels L (Site N)) M) : ℝ :=
  matrixObservableHistory T q
    (rootTower K (fun i => prior i.1.1) (fun j => m j.succ) base old z) m
    (List.ofFn (fun j : Fin k => (some j : Option (Fin k)))).reverse S a
    (spatialProduct (fun c x i => match c with | none => 1 | some _ => rootVector (readVector read) z x i))
    (fun x => f (fun b => physical (rootArray z.2.2.1 z.2.2.2) (L+1) (S.pathAt b x)))

omit [MeasurableSpace X] [MeasurableSpace Y] in
lemma integral_rootShapeHistory_marker (z : FullRootState Y X (Labels L (Site N)) M) :
    (∫ i, rootShapeHistory S a K m base old read (matrixSplitTest T q) false f z i ∂siteLaw N) =
      rootMarkerObservable S a K m base old read T q f z := by
  rw [integral_siteLaw]
  symm
  exact matrix_history_spatialProduct T q
    (rootTower K (fun i => prior i.1.1) (fun j => m j.succ) base old z) m
    (fun c x i => match c with | none => 1 | some _ => rootVector (readVector read) z x i) S a
    (fun x => f (fun b => physical (rootArray z.2.2.1 z.2.2.2) (L+1) (S.pathAt b x)))

variable (hb : ∀ n y, Measurable (fun z : RootPath Y M × RootPath X n => base z.1 n z.2 y))
    (hm : ∀ j : Fin (L+1), m j.succ ≠ 0) (hmono : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last (L+1)) = 1)
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
include hb hm hmono hpos hroot hend hB hf


lemma shapeAverage_marker (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure (Labels L (Site N))) [IsProbabilityMeasure ν] (rate score : ℝ≥0) (hk : 0 < k) :
    shapeAverage ξ μ ν (siteLaw N) rate score S a K m base old read (matrixSplitTest T q) false f =
      ∫ z, rootMarkerObservable S a K m base old read T q f z ∂fullRootLaw ξ μ ν rate score := by
  unfold shapeAverage
  rw [integral_prod _ (integrable_rootShapeHistory_general S a K m base old read f
    hb hm hmono hpos hroot hend hB hf ξ μ ν rate score hk (matrixSplitTest T q) false)]
  exact integral_congr_ae (ae_of_all _ (fun z => integral_rootShapeHistory_marker S a K m base old read T q f z))

lemma shapeCovariance_marker (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure (Labels L (Site N))) [IsProbabilityMeasure ν] (rate score : ℝ≥0) (hk : 0 < k) :
    shapeCovariance ξ μ ν (siteLaw N) rate score S a K m base old read (matrixSplitTest T q) false f =
      matrixRootCovariance (fullRootLaw ξ μ ν rate score)
        (rootAlphabet (Ω := Ω) (A := fun i : Labels L (Site N) => Alphabet i.1.1)) T S q
        (rootTower K (fun i => prior i.1.1) (fun j => m j.succ) base old) m
        (List.ofFn (fun j : Fin k => (some j : Option (Fin k)))).reverse a
        (fun z => spatialProduct (fun c x i => match c with | none => 1 | some _ => rootVector (readVector read) z x i))
        (fun z x => f (fun b => physical (rootArray z.2.2.1 z.2.2.2) (L+1) (S.pathAt b x))) := by
  unfold shapeCovariance
  rw [shapeAverage_marker S a K m base old read T q f hb hm hmono hpos hroot hend hB hf
    ξ μ ν rate score hk,
    shapeAverage_marker S a K m base old read T q (fun _ => 1) hb hm hmono hpos hroot hend
    (by norm_num : (0:ℝ) ≤ 1) (fun _ => by simp) ξ μ ν rate score hk]
  rfl

end DilutedSpinGlass.UniversalDictionary

end

end OAI
