import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingWeightTests
import OAI.Analysis.IrrationalRotation.Sampling.SamplingOrbitWeak
import OAI.Analysis.IrrationalRotation.Product.ProductScaleConsequences

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped BigOperators
open Filter

namespace Invariant233.ProductModel.SamplingWeights
open SamplingCylinderWeak

def cylinderSupport (t : CylinderTest (Bool × ℕ)) : Finset ℕ :=
  t.image (fun v => v.1.2)

def cylinderCoordinateSet (t : CylinderTest (Bool × ℕ)) (b : Bool) (i : ℕ) : Set ℝ :=
  {s | ∀ v ∈ t, v.1 = (b, i) → (v.2.1 : ℝ) < s ∧ s < (v.2.2 : ℝ)}

@[simp] theorem cylinderCoordinateSet_empty (b : Bool) (i : ℕ) :
    cylinderCoordinateSet ∅ b i = univ := by
  ext s
  simp [cylinderCoordinateSet]

theorem cylinderCoordinateSet_eq_univ_of_not_mem
    (t : CylinderTest (Bool × ℕ)) (b : Bool) {i : ℕ}
    (hi : i ∉ cylinderSupport t) : cylinderCoordinateSet t b i = univ := by
  ext s
  simp only [cylinderCoordinateSet, mem_ofPred_eq, mem_univ, iff_true]
  intro v hv hvi
  apply (hi _).elim
  exact Finset.mem_image.mpr ⟨v, hv, congrArg Prod.snd hvi⟩

theorem measurableSet_cylinderCoordinateSet (t : CylinderTest (Bool × ℕ))
    (b : Bool) (i : ℕ) : MeasurableSet (cylinderCoordinateSet t b i) := by
  unfold cylinderCoordinateSet
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro v
  apply MeasurableSet.iInter
  intro _hv
  apply MeasurableSet.iInter
  intro _hvi
  exact measurableSet_Ioo

theorem cylinderCoordinateSet_normal_form (t : CylinderTest (Bool × ℕ))
    (b : Bool) (i : ℕ) :
    cylinderCoordinateSet t b i = univ ∨
      ∃ a c : ℚ, cylinderCoordinateSet t b i = Ioo (a : ℝ) (c : ℝ) := by
  classical
  induction t using Finset.induction_on with
  | empty => exact Or.inl (cylinderCoordinateSet_empty b i)
  | @insert v t hv ih =>
    by_cases hvi : v.1 = (b, i)
    · have he : cylinderCoordinateSet (insert v t) b i =
          Ioo (v.2.1 : ℝ) (v.2.2 : ℝ) ∩ cylinderCoordinateSet t b i := by
        ext s
        simp [cylinderCoordinateSet, hvi]
      rw [he]
      rcases ih with heq | ⟨a, c, heq⟩
      · exact Or.inr ⟨v.2.1, v.2.2, by rw [heq, inter_univ]⟩
      · right
        refine ⟨max v.2.1 a, min v.2.2 c, ?_⟩
        rw [heq, Ioo_inter_Ioo]
        simp
    · have he : cylinderCoordinateSet (insert v t) b i =
          cylinderCoordinateSet t b i := by
        ext s
        simp [cylinderCoordinateSet, hvi]
      rwa [he]

theorem endpointCylinder_eq_rectangle (t : CylinderTest (Bool × ℕ))
    (D : Finset ℕ) (hD : cylinderSupport t ⊆ D) :
    endpointCylinder t = rectangle D
      (cylinderCoordinateSet t false) (cylinderCoordinateSet t true) := by
  ext xy
  change (∀ v ∈ t, (v.2.1 : ℝ) < cutCoordinates xy v.1 ∧
    cutCoordinates xy v.1 < (v.2.2 : ℝ)) ↔
    (∀ i ∈ D, circleRepresentative (xy.1 i) ∈ cylinderCoordinateSet t false i ∧
      circleRepresentative (xy.2 i) ∈ cylinderCoordinateSet t true i)
  constructor
  · intro hx i _hi
    constructor
    · intro v hv hvi
      simpa only [hvi, cutCoordinates, Bool.false_eq_true, ite_false] using hx v hv
    · intro v hv hvi
      simpa only [hvi, cutCoordinates, ite_true] using hx v hv
  · intro hx v hv
    have hi : v.1.2 ∈ D := hD (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
    rcases v with ⟨⟨b, i⟩, a, c⟩
    cases b
    · exact (hx i hi).1 _ hv rfl
    · exact (hx i hi).2 _ hv rfl

theorem cylinder_orbitTestWeight_eq_first_product
    (D I : Finset ℕ) (h α : ℝ) (θ : ℕ → ℝ) (n : ℕ)
    (t : CylinderTest (Bool × ℕ)) (hD : cylinderSupport t ⊆ D) (x : Base) :
    TailTrimming.orbitTestWeight θ (endpointCylinder t) (orbitWeight D I h α θ) n x =
      ∏ i ∈ D, testedCoordinateWeight false I h α i
        (cylinderCoordinateSet t false i) (cylinderCoordinateSet t true i)
        (circleRepresentative (x i)) (Int.fract ((n : ℝ) * θ i)) := by
  rw [endpointCylinder_eq_rectangle t D hD]
  exact orbitTestWeight_eq_first_product D I h α θ n _ _ x

theorem cylinder_orbitTestWeight_eq_second_product
    (D I : Finset ℕ) (h α : ℝ) (θ : ℕ → ℝ) (n : ℕ)
    (t : CylinderTest (Bool × ℕ)) (hD : cylinderSupport t ⊆ D) (y : Base) :
    TailTrimming.orbitTestWeight θ (endpointCylinder t) (orbitWeight D I h α θ) n
        (rotationIterate θ (-(n : ℤ)) y) =
      ∏ i ∈ D, testedCoordinateWeight true I h α i
        (cylinderCoordinateSet t false i) (cylinderCoordinateSet t true i)
        (circleRepresentative (y i)) (Int.fract ((n : ℝ) * θ i)) := by
  rw [endpointCylinder_eq_rectangle t D hD]
  exact orbitTestWeight_eq_second_product D I h α θ n _ _ y

theorem cylinderTestAverage_eq_product_average
    (D I N : Finset ℕ) (h α : ℝ) (θ : ℕ → ℝ)
    (t : CylinderTest (Bool × ℕ)) (hD : cylinderSupport t ⊆ D) (x : Base) :
    TailTrimming.cylinderTestAverage θ N (orbitWeight D I h α θ) t x =
      (N.card : ℝ)⁻¹ * ∑ n ∈ N, ∏ i ∈ D, testedCoordinateWeight false I h α i
        (cylinderCoordinateSet t false i) (cylinderCoordinateSet t true i)
        (circleRepresentative (x i)) (Int.fract ((n : ℝ) * θ i)) := by
  unfold TailTrimming.cylinderTestAverage
  simp_rw [cylinder_orbitTestWeight_eq_first_product D I h α θ _ t hD]

theorem eventually_cylinderSupport_subset_sourcePrefix
    {p : ProductScaleData} (hp : ProductScaleLaws p)
    (t : CylinderTest (Bool × ℕ)) :
    ∀ᶠ l in atTop, cylinderSupport t ⊆ Finset.range (p.prefixCount (l + 1)) := by
  have hcount (l : ℕ) : l ≤ p.prefixCount l := by
    calc
      l = ∑ _i ∈ Finset.range l, 1 := by simp
      _ ≤ ∑ i ∈ Finset.range l, p.m i :=
        Finset.sum_le_sum (fun i _ => hp.m_pos i)
  change ∀ᶠ l in atTop, ∀ i ∈ cylinderSupport t,
    i ∈ Finset.range (p.prefixCount (l + 1))
  rw [Finset.eventually_all]
  intro i _hi
  filter_upwards [eventually_ge_atTop i] with l hl
  exact Finset.mem_range.mpr (lt_of_le_of_lt hl
    (lt_of_lt_of_le (Nat.lt_succ_self l) (hcount (l + 1))))

end Invariant233.ProductModel.SamplingWeights

end

end OAI
