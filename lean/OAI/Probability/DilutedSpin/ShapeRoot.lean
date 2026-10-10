import OAI.Probability.DilutedSpin.ConcreteHistory
import OAI.Probability.DilutedSpin.ProfileHistory

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PrescribedTree
open scoped NNReal BigOperators
variable {Ω X Y Z : Type} [Fintype Ω]
    [MeasurableSpace X] [MeasurableSpace Y]
    [Countable Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] {L M n k : ℕ}

noncomputable def externalShapeHistory (S : PrescribedTree (L+1)) (anchorLeaf : S.Leaf)
    (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (base : FinitePath Ω (L+1) → ℝ) (roots : Fin n → Labels L Z)
    (old : (i : Labels L Z) → FinitePath Ω (L+1) → FinitePath (Alphabet i.1.1) (L+1) → ℝ)
    (read : Z → FinitePath Ω (L+1) → Spin) (v : Z)
    (F : (Option (Fin k) → Option (Fin k) → ℕ) → ℝ) (spinAnchor : Bool)
    (f : (S.Leaf → FinitePath Ω (L+1)) → ℝ) : ℝ :=
  shapeHistory
    (KernelTower.tilt (L+1) (tower roots (L+1) T (fun i => prior i.1.1)) (fun j => m j.succ)
      (HeterogeneousMarks.logWeight base roots old)) m F
    (fun c x => match c with
      | none => if spinAnchor then spin (read v (physical roots (L+1) x)) else 1
      | some _ => spin (read v (physical roots (L+1) x))) S anchorLeaf
    (fun x => f (fun a => physical roots (L+1) (S.pathAt a x)))

omit [Countable Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
lemma externalShapeHistory_expansion (S : PrescribedTree (L+1)) (anchorLeaf : S.Leaf)
    (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (base : FinitePath Ω (L+1) → ℝ) (roots : Fin n → Labels L Z)
    (old : (i : Labels L Z) → FinitePath Ω (L+1) → FinitePath (Alphabet i.1.1) (L+1) → ℝ)
    (read : Z → FinitePath Ω (L+1) → Spin) (v : Z)
    (F : (Option (Fin k) → Option (Fin k) → ℕ) → ℝ) (spinAnchor : Bool)
    (f : (S.Leaf → FinitePath Ω (L+1)) → ℝ) :
    externalShapeHistory S anchorLeaf T m base roots old read v F spinAnchor f =
      ∑ s : Finset (SharingIndex L (Option (Fin k))),
        BooleanPolynomial.coefficient (fun y => F (splitFromProfile y)) s *
        externalHistory S anchorLeaf T m base roots old read v
          (fun j => (requirementMap s j).1) (fun j => (requirementMap s j).2.1)
          (fun j => (requirementMap s j).2.2) spinAnchor f := by
  exact shapeHistory_expansion _ m F _ S anchorLeaf _

noncomputable def rootShapeHistory (S : PrescribedTree (L+1)) (anchorLeaf : S.Leaf)
    (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (base : RootPath Y M → (n : ℕ) → RootPath X n → FinitePath Ω (L+1) → ℝ)
    (old : (i : Labels L Z) → FinitePath Ω (L+1) → FinitePath (Alphabet i.1.1) (L+1) → ℝ)
    (read : Z → FinitePath Ω (L+1) → Spin)
    (F : (Option (Fin k) → Option (Fin k) → ℕ) → ℝ) (spinAnchor : Bool)
    (f : (S.Leaf → FinitePath Ω (L+1)) → ℝ) (z : FullRootState Y X (Labels L Z) M) (v : Z) : ℝ :=
  packRoot (fun h n x t y => externalShapeHistory S anchorLeaf T m (base h n x)
    (rootArray t y) old read v F spinAnchor f) z

omit [MeasurableSpace X] [MeasurableSpace Y]
    [Countable Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
lemma rootShapeHistory_expansion (S : PrescribedTree (L+1)) (anchorLeaf : S.Leaf)
    (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (base : RootPath Y M → (n : ℕ) → RootPath X n → FinitePath Ω (L+1) → ℝ)
    (old : (i : Labels L Z) → FinitePath Ω (L+1) → FinitePath (Alphabet i.1.1) (L+1) → ℝ)
    (read : Z → FinitePath Ω (L+1) → Spin)
    (F : (Option (Fin k) → Option (Fin k) → ℕ) → ℝ) (spinAnchor : Bool)
    (f : (S.Leaf → FinitePath Ω (L+1)) → ℝ) (z : FullRootState Y X (Labels L Z) M) (v : Z) :
    rootShapeHistory S anchorLeaf T m base old read F spinAnchor f z v =
      ∑ s : Finset (SharingIndex L (Option (Fin k))),
        BooleanPolynomial.coefficient (fun y => F (splitFromProfile y)) s *
        rootHistory S anchorLeaf T m base old read
          (fun j => (requirementMap s j).1) (fun j => (requirementMap s j).2.1)
          (fun j => (requirementMap s j).2.2) spinAnchor f z v := by
  exact externalShapeHistory_expansion S anchorLeaf T m (base z.1 z.2.1.1 z.2.1.2)
    (rootArray z.2.2.1 z.2.2.2) old read v F spinAnchor f

variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure (Labels L Z)) [IsProbabilityMeasure ν]
    (τ : Measure Z) [IsProbabilityMeasure τ] (rate score : ℝ≥0)
    (S : PrescribedTree (L+1)) (anchorLeaf : S.Leaf)
    (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (base : RootPath Y M → (n : ℕ) → RootPath X n → FinitePath Ω (L+1) → ℝ)
    (old : (i : Labels L Z) → FinitePath Ω (L+1) → FinitePath (Alphabet i.1.1) (L+1) → ℝ)
    (read : Z → FinitePath Ω (L+1) → Spin)
    (F : (Option (Fin k) → Option (Fin k) → ℕ) → ℝ) (spinAnchor : Bool)
    (f : (S.Leaf → FinitePath Ω (L+1)) → ℝ)

noncomputable def shapeAverage : ℝ :=
  ∫ z : FullRootState Y X (Labels L Z) M × Z,
    rootShapeHistory S anchorLeaf T m base old read F spinAnchor f z.1 z.2
      ∂(fullRootLaw ξ μ ν rate score).prod τ

noncomputable def shapeCovariance : ℝ :=
  shapeAverage ξ μ ν τ rate score S anchorLeaf T m base old read F spinAnchor f -
    oldTreeAverage ξ μ ν rate score S T (fun i => prior i.1.1) (fun j => m j.succ) base old f *
      shapeAverage ξ μ ν τ rate score S anchorLeaf T m base old read F spinAnchor (fun _ => 1)

variable (hb : ∀ n y, Measurable (fun z : RootPath Y M × RootPath X n => base z.1 n z.2 y))
    (hm : ∀ j : Fin (L+1), m j.succ ≠ 0) (hmono : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last (L+1)) = 1)
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
include hb hm hmono hpos hroot hend hB hf

lemma shapeAverage_expansion (hk : 0 < k) :
    shapeAverage ξ μ ν τ rate score S anchorLeaf T m base old read F spinAnchor f =
      ∑ s : Finset (SharingIndex L (Option (Fin k))),
        BooleanPolynomial.coefficient (fun y => F (splitFromProfile y)) s *
        historyAverage ξ μ ν τ rate score S anchorLeaf T m base old read
          (fun j => (requirementMap s j).1) (fun j => (requirementMap s j).2.1)
          (fun j => (requirementMap s j).2.2) spinAnchor f := by
  unfold shapeAverage
  simp_rw [rootShapeHistory_expansion S anchorLeaf T m base old read F spinAnchor f]
  rw [integral_finsetSum]
  · simp only [integral_const_mul,historyAverage]
  · intro s _
    exact (integrable_rootHistory ξ μ ν τ rate score S anchorLeaf T m base old read
      (fun j => (requirementMap s j).1) (fun j => (requirementMap s j).2.1)
      (fun j => (requirementMap s j).2.2) spinAnchor f hb hm hmono hpos hroot hend hB hf hk).const_mul _

lemma shapeCovariance_expansion (hk : 0 < k) :
    shapeCovariance ξ μ ν τ rate score S anchorLeaf T m base old read F spinAnchor f =
      ∑ s : Finset (SharingIndex L (Option (Fin k))),
        BooleanPolynomial.coefficient (fun y => F (splitFromProfile y)) s *
        historyCovariance ξ μ ν τ rate score S anchorLeaf T m base old read
          (fun j => (requirementMap s j).1) (fun j => (requirementMap s j).2.1)
          (fun j => (requirementMap s j).2.2) spinAnchor f := by
  unfold shapeCovariance
  rw [shapeAverage_expansion ξ μ ν τ rate score S anchorLeaf T m base old read F spinAnchor f
      hb hm hmono hpos hroot hend hB hf hk,
    shapeAverage_expansion ξ μ ν τ rate score S anchorLeaf T m base old read F spinAnchor (fun _ => 1)
      hb hm hmono hpos hroot hend (B := 1) (by norm_num) (by intro; norm_num) hk]
  simp only [historyCovariance,mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  ring

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
