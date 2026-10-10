import OAI.Analysis.CircleDomains.Modulus.RealBarrierSize
import OAI.Analysis.CircleDomains.Topology.GreedyOpenSelection

namespace OAI

/-! The actual real tests used by the countable selection. Compatibility is
with every finite sublist of previously selected tests, retaining repetitions. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

structure UngatedRealTest (d : PathCodeData Sphere Sphere) (π : Sphere → Sphere)
    (EStar : Set Sphere) where
  coordinate : PhysicalRealCoordinate d π
  region : Set Sphere
  region_open : IsOpen region
  zero : ∀ x ∈ EStar, coordinate.quotient x = 0
  one : ∀ x ∈ region ∩ d.quotientDomain, coordinate.quotient x = 1
  exclusions : Set Sphere
  exclusions_countable : exclusions.Countable
  weight : Sphere → ℝ≥0∞
  weight_finite : (∑' x, weight x ^ 2) < ∞
  weight_support : support weight ⊆ exclusions
  band_bound : ∀ x ∈ d.dust, ENNReal.ofReal
    (limsup coordinate.quotient (𝓝[d.quotientDomain] x) -
      liminf coordinate.quotient (𝓝[d.quotientDomain] x)) ≤ weight x

namespace UngatedRealTest
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {EStar : Set Sphere}

def size (c : UngatedRealTest d π EStar) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt (∫ x in FiniteTransfer.realChartDomain d.physicalDomain,
    FiniteTransfer.gradientEnergy c.coordinate.physical
      (fun z => FiniteTransfer.sphericalMetricFactor z • 1) x)) + countingSquareNorm c.weight

theorem ordinary_norm_le_size
    (R : UngatedRealTest d π EStar)
    (hclosure : d.dust ⊆ closure d.quotientDomain)
    {A : Type*} (a : A → Sphere) (ha : Injective a) (haB : range a ⊆ d.dust) :
    Real.sqrt (∫ x in FiniteTransfer.realChartDomain d.physicalDomain,
      FiniteTransfer.gradientEnergy R.coordinate.physical
        (fun z => FiniteTransfer.sphericalMetricFactor z • 1) x) +
    Real.sqrt (∑' s, (limsup R.coordinate.quotient (𝓝[d.quotientDomain] (a s)) -
      liminf R.coordinate.quotient (𝓝[d.quotientDomain] (a s))) ^ 2) ≤
      R.size.toReal := by
  have hunit (x : Sphere) (_ : x ∈ d.quotientDomain) : |R.coordinate.quotient x| ≤ 1 := by
    rw [abs_of_nonneg (R.coordinate.quotient_unit x).1]
    exact (R.coordinate.quotient_unit x).2
  have hnorm := real_square_norm_le_counting
    (fun s => limsup R.coordinate.quotient (𝓝[d.quotientDomain] (a s)) -
      liminf R.coordinate.quotient (𝓝[d.quotientDomain] (a s))) R.weight a ha
    (fun s => boundary_width_nonneg hunit (hclosure (haB (mem_range_self s))))
    (fun s => R.band_bound (a s) (haB (mem_range_self s))) R.weight_finite
  rw [size, ENNReal.toReal_add ENNReal.ofReal_ne_top
    (show countingSquareNorm R.weight ≠ ∞ from
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) R.weight_finite.ne),
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  exact add_le_add le_rfl hnorm


def openEnds (c : UngatedRealTest d π EStar) : Set d.dust := Subtype.val ⁻¹' c.region

theorem open_openEnds (c : UngatedRealTest d π EStar) : IsOpen c.openEnds :=
  c.region_open.preimage continuous_subtype_val

def CompatibleWith (c : UngatedRealTest d π EStar)
    (A : Set (UngatedRealTest d π EStar)) : Prop :=
  (∀ a ∈ A, a.exclusions ∩ d.dust ⊆ c.exclusions) ∧
  ∀ (n : ℕ) (q : Fin n → UngatedRealTest d π EStar), (∀ i, q i ∈ A) →
    (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
      (freeComponentFailure (d.dust \ c.exclusions)
        (circleBandGraph d.quotientDomain c.coordinate.quotient)
        (fun i : Fin n => circleBandGraph d.quotientDomain (q i).coordinate.quotient) id) = 0

theorem CompatibleWith.mono {c : UngatedRealTest d π EStar}
    {A B : Set (UngatedRealTest d π EStar)} (h : c.CompatibleWith B) (hAB : A ⊆ B) :
    c.CompatibleWith A :=
  ⟨fun a ha => h.1 a (hAB ha), fun n q hq => h.2 n q (fun i => hAB (hq i))⟩

def of_barrier {previous : ℕ → PhysicalRealCoordinate d π} {flags : Set Sphere}
    {regions : ℕ → Set Sphere} {f : d.quotientDomain → Sphere}
    (R : CompatibleRealBarrier d π previous flags EStar regions f univ)
    (hopen : IsOpen (regions R.level)) : UngatedRealTest d π EStar where
  coordinate := R.coordinate
  region := regions R.level
  region_open := hopen
  zero := R.zero
  one := fun x hx => R.one x ⟨subset_closure hx.1, hx.2⟩
  exclusions := R.exclusions
  exclusions_countable := R.exclusions_countable
  weight := R.weight
  weight_finite := R.weight_finite
  weight_support := R.weight_support
  band_bound := R.band_bound

theorem size_of_barrier {previous : ℕ → PhysicalRealCoordinate d π} {flags : Set Sphere}
    {regions : ℕ → Set Sphere} {f : d.quotientDomain → Sphere}
    (R : CompatibleRealBarrier d π previous flags EStar regions f univ)
    (hopen : IsOpen (regions R.level)) : (of_barrier R hopen).size = R.controlledSize :=
  R.controlledSize_of_univ.symm

omit [MeasurableSpace C(PathTime, Sphere)] in
theorem freeComponentFailure_congr_selected
    {X T I J K : Type*} [TopologicalSpace X]
    (F : Set X) (N : Set (X × T)) (R : I → Set (X × T)) (S : J → Set (X × T))
    (a : K → I) (b : K → J) (h : ∀ k, R (a k) = S (b k)) :
    freeComponentFailure F N R a = freeComponentFailure F N S b := by
  have he : finiteLevelUnionGraph R a = finiteLevelUnionGraph S b := by
    unfold finiteLevelUnionGraph
    apply iUnion_congr
    intro k
    rw [h k]
  unfold freeComponentFailure
  rw [he]

theorem of_barrier_compatible
    {previous : ℕ → PhysicalRealCoordinate d π} {flags : Set Sphere}
    {regions : ℕ → Set Sphere} {f : d.quotientDomain → Sphere}
    (R : CompatibleRealBarrier d π previous flags EStar regions f univ)
    (hopen : IsOpen (regions R.level)) (A : Set (UngatedRealTest d π EStar))
    (labels : UngatedRealTest d π EStar → ℕ)
    (hflags : ∀ c ∈ A, c.exclusions ∩ d.dust ⊆ flags)
    (hQ : ∀ c ∈ A, c.coordinate.quotient = (previous (labels c)).quotient) :
    (of_barrier R hopen).CompatibleWith A := by
  refine ⟨fun c hc => (hflags c hc).trans R.prior_flags, ?_⟩
  intro n q hq
  change (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
    (freeComponentFailure (d.dust \ R.exclusions)
      (circleBandGraph d.quotientDomain R.coordinate.quotient)
      (fun i : Fin n => circleBandGraph d.quotientDomain (q i).coordinate.quotient) id) = 0
  rw [freeComponentFailure_congr_selected (d.dust \ R.exclusions)
    (circleBandGraph d.quotientDomain R.coordinate.quotient)
    (fun i : Fin n => circleBandGraph d.quotientDomain (q i).coordinate.quotient)
    (fun i => circleBandGraph d.quotientDomain (previous i).quotient) id (labels ∘ q)
    (fun i => by simp only [id_eq, Function.comp_apply, hQ (q i) (hq i)])]
  exact R.finite_compatibility n (labels ∘ q)

end UngatedRealTest
end CircleDomainRigidity

end

end OAI
