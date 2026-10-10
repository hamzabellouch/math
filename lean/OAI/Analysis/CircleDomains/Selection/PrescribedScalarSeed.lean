import OAI.Analysis.CircleDomains.Selection.ScalarSeedCompatibility
import OAI.Analysis.CircleDomains.Selection.PresentedRealSeed
import OAI.Analysis.CircleDomains.Selection.ZeroRealCoordinate

namespace OAI

/-! A prescribed finite scalar list with null trace pairs gives actual
selectable real seed coordinates, with unchanged functions and zero bands. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

 def PhysicalRealCoordinate.continuousTest
    {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {EStar : Set Sphere}
    (Q : PhysicalRealCoordinate d π) (hQ : Continuous Q.quotient)
    (hz : ∀ x ∈ EStar, Q.quotient x = 0) (hdense : Dense d.quotientDomain) :
    UngatedRealTest d π EStar where
  coordinate := Q
  region := ∅
  region_open := isOpen_empty
  zero := hz
  one := fun _ hx => hx.1.elim
  exclusions := ∅
  exclusions_countable := countable_empty
  weight := fun _ => 0
  weight_finite := by simp
  weight_support := by simp
  band_bound := by
    intro x _
    let : NeBot (𝓝[d.quotientDomain] x) := mem_closure_iff_nhdsWithin_neBot.mp (hdense x)
    have ht := hQ.continuousAt.continuousWithinAt.tendsto (s := d.quotientDomain) (x := x)
    rw [ht.limsup_eq, ht.liminf_eq, sub_self, ENNReal.ofReal_zero]

 def finiteScalarSeedTests
    {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {EStar : Set Sphere}
    {m : ℕ} (Q : Fin m → UngatedRealTest d π EStar) : ℕ → UngatedRealTest d π EStar
  | 0 => UngatedRealTest.zeroTest d π EStar
  | n + 1 => if h : n < m then Q ⟨n, h⟩ else UngatedRealTest.zeroTest d π EStar

 omit [MeasurableSpace C(PathTime, Sphere)] in
 private theorem pair_image_zero_left {X : Type*} (B : Set X) (v : X → ℝ) :
    volume ((fun x => ((0 : ℝ), v x)) '' B) = 0 := by
  rw [Measure.volume_eq_prod]
  apply measure_mono_null (t := ({0} : Set ℝ) ×ˢ univ)
  · rintro _ ⟨x, _, rfl⟩
    exact ⟨rfl, mem_univ _⟩
  · simp only [Measure.prod_prod, measure_singleton, zero_mul]

 omit [MeasurableSpace C(PathTime, Sphere)] in
 private theorem pair_image_zero_right {X : Type*} (B : Set X) (v : X → ℝ) :
    volume ((fun x => (v x, (0 : ℝ))) '' B) = 0 := by
  rw [Measure.volume_eq_prod]
  apply measure_mono_null (t := univ ×ˢ ({0} : Set ℝ))
  · rintro _ ⟨x, _, rfl⟩
    exact ⟨mem_univ _, rfl⟩
  · simp only [Measure.prod_prod, measure_singleton, mul_zero]

 theorem finiteScalarSeedTests_pair_null
    {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {EStar : Set Sphere}
    {m : ℕ} (Q : Fin m → UngatedRealTest d π EStar)
    (hpair : ∀ i j, i ≠ j → volume
      ((fun x => ((Q i).coordinate.quotient x, (Q j).coordinate.quotient x)) '' d.dust) = 0) :
    ∀ i j, i ≠ j → volume ((fun x =>
      ((finiteScalarSeedTests Q i).coordinate.quotient x,
        (finiteScalarSeedTests Q j).coordinate.quotient x)) '' d.dust) = 0 := by
  intro i j hij
  cases i with
  | zero => exact pair_image_zero_left _ _
  | succ i =>
    cases j with
    | zero => exact pair_image_zero_right _ _
    | succ j =>
      by_cases hi : i < m
      · by_cases hj : j < m
        · simp only [finiteScalarSeedTests, dite_eq_left hi, dite_eq_left hj]
          exact hpair ⟨i, hi⟩ ⟨j, hj⟩ (fun h => hij (congrArg Nat.succ (congrArg Fin.val h)))
        · simp only [finiteScalarSeedTests, dite_eq_left hi, dite_eq_right hj,
            UngatedRealTest.zeroTest, PhysicalRealCoordinate.zero]
          exact pair_image_zero_right _ _
      · simp only [finiteScalarSeedTests, dite_eq_right hi,
          UngatedRealTest.zeroTest, PhysicalRealCoordinate.zero]
        exact pair_image_zero_left _ _

 theorem exists_prescribed_scalar_seed
    (hcoarea : WeightedPlanarScalarCoarea)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdense : Dense d.quotientDomain)
    (π : Sphere → Sphere) (hπ : Continuous π)
    (he : ∀ x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hB : d.dust = π '' d.physicalDomainᶜ) (p : d.dust) (EStar : Set Sphere)
    (hinfty : π OnePoint.infty ∈ interior EStar)
    {m : ℕ} (Q : Fin m → PhysicalRealCoordinate d π)
    (hQ : ∀ i, Continuous (Q i).quotient)
    (hz : ∀ i x, x ∈ EStar → (Q i).quotient x = 0)
    (hpair : ∀ i j, i ≠ j → volume
      ((fun x => ((Q i).quotient x, (Q j).quotient x)) '' d.dust) = 0) :
    ∃ seed : ℕ → SelectableMaskedCoordinate d π,
      (seed 0).coordinate.graph = circleBandGraph d.quotientDomain (fun _ => 0) ∧
      (∀ (j n : ℕ) (labels : Fin n → ℕ), (∀ i, labels i < j) →
        (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
          (freeComponentFailure (d.dust \ ⋃ k, (seed k).flags) (seed j).coordinate.graph
            (fun k => (seed k).coordinate.graph) labels) = 0) ∧
      ∃ P : ∀ i, RealCoordinatePresentation d π (seed i).coordinate,
        ∀ i : Fin m, (P (i.val + 1)).coordinate = Q i := by
  let T (i : Fin m) := (Q i).continuousTest (hQ i) (hz i) hdense
  let c := finiteScalarSeedTests T
  have hc : ∀ n, Continuous (c n).coordinate.quotient := by
    intro n
    cases n with
    | zero => exact continuous_const
    | succ n =>
      by_cases hn : n < m
      · simpa only [c, finiteScalarSeedTests, dite_eq_left hn, T,
          PhysicalRealCoordinate.continuousTest] using hQ ⟨n, hn⟩
      · simp only [c, finiteScalarSeedTests, dite_eq_right hn,
          UngatedRealTest.zeroTest, PhysicalRealCoordinate.zero]
        exact continuous_const
  have hpairs := finiteScalarSeedTests_pair_null T hpair
  have hcomp : OrderedLevelNullCompatibility (realTestLevelData d c).levels (d.dust \ ∅) := by
    intro j n labels hlt
    simp only [sdiff_empty, realTestLevelData.level_relation]
    exact scalar_family_ordered_compatibility d.quotientDomain d.dust
      (fun i => (c i).coordinate.quotient) hc hpairs j n labels hlt
  obtain ⟨seed, _, hzero, hcompat, P, hP⟩ := exists_presented_real_seed hcoarea d hU hG hdense
    π hπ he hB p EStar hinfty c rfl ∅ countable_empty (empty_subset _) hcomp
  refine ⟨seed, hzero, hcompat, P, ?_⟩
  intro i
  exact (hP (i.val + 1)).trans (by simp only [c, finiteScalarSeedTests, dite_eq_left i.isLt]; rfl)

end CircleDomainRigidity

end

end OAI
