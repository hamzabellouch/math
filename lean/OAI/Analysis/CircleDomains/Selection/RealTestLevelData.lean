import OAI.Analysis.CircleDomains.Modulus.RealBarrierTests
import OAI.Analysis.CircleDomains.Selection.FreeLevelSections
import OAI.Analysis.CircleDomains.Transfer.CountableRealTransfer
import OAI.Analysis.CircleDomains.Selection.FiniteTupleCompatibility
import OAI.Analysis.CircleDomains.Modulus.BarrierRebase

namespace OAI

/-! The selected real tests supply the actual level graphs and their
square-summable incidence weights for the next positive-law application. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

def realTestLevelData (d : PathCodeData Sphere Sphere) {π : Sphere → Sphere}
    {EStar : Set Sphere} (c : ℕ → UngatedRealTest d π EStar) : PathCodeData Sphere Sphere :=
  {d with
    levels := fun i => Prod.swap ⁻¹' circleBandGraph d.quotientDomain (c i).coordinate.quotient
    levelWeights := fun i => d.dust.indicator (c i).weight}

namespace realTestLevelData
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {EStar : Set Sphere}
  (c : ℕ → UngatedRealTest d π EStar)

def previous (i : ℕ) : PhysicalRealCoordinate (realTestLevelData d c) π :=
  (c i).coordinate.rebase rfl rfl

theorem weight_finite (i : ℕ) : (∑' x, (realTestLevelData d c).levelWeights i x ^ 2) < ∞ := by
  apply lt_of_le_of_lt (b := ∑' x, (c i).weight x ^ 2) _ (c i).weight_finite
  apply ENNReal.tsum_le_tsum
  intro x
  change (d.dust.indicator (c i).weight x) ^ 2 ≤ (c i).weight x ^ 2
  by_cases hx : x ∈ d.dust
  · simp only [indicator_of_mem hx, le_refl]
  · simp only [indicator_of_notMem hx, zero_pow (by decide : 2 ≠ 0), zero_le]

theorem marked_weights (M : Set Sphere)
    (hM : ∀ i, (c i).exclusions ∩ d.dust ⊆ M) (i : ℕ) :
    support ((realTestLevelData d c).levelWeights i) ⊆ M := by
  intro x hx
  change d.dust.indicator (c i).weight x ≠ 0 at hx
  by_cases hxB : x ∈ d.dust
  · rw [indicator_of_mem hxB] at hx
    exact hM i ⟨(c i).weight_support hx, hxB⟩
  · exact (hx (indicator_of_notMem hxB _)).elim

theorem point_bound (hU : IsOpen d.quotientDomain) (hdense : Dense d.quotientDomain)
    (hBU : d.dustᶜ ⊆ d.quotientDomain) (i : ℕ) (x : Sphere) :
    volume {t | (t, x) ∈ (realTestLevelData d c).levels i} ≤
      (realTestLevelData d c).levelWeights i x := by
  change volume {t | (x, t) ∈ circleBandGraph d.quotientDomain (c i).coordinate.quotient} ≤
    d.dust.indicator (c i).weight x
  have hunit (y : Sphere) (_ : y ∈ d.quotientDomain) : |(c i).coordinate.quotient y| ≤ 1 := by
    rw [abs_of_nonneg ((c i).coordinate.quotient_unit y).1]
    exact ((c i).coordinate.quotient_unit y).2
  by_cases hx : x ∈ d.dust
  · rw [indicator_of_mem hx]
    exact (volume_circleBandGraph_incidence_le_budget hunit
      (by rw [hdense.closure_eq]; trivial) le_rfl).trans ((c i).band_bound x hx)
  · rw [indicator_of_notMem hx]
    have he : {t | (x, t) ∈ circleBandGraph d.quotientDomain (c i).coordinate.quotient} =
        {((c i).coordinate.quotient x : UnitAddCircle)} := by
      ext t
      change (x, t) ∈ circleBandGraph d.quotientDomain (c i).coordinate.quotient ↔
        t = ((c i).coordinate.quotient x : UnitAddCircle)
      rw [circleBandGraph_on_open hU (c i).coordinate.quotient_continuous (hBU hx)]
      exact eq_comm
    rw [he, unitAddCircle_volume_singleton]

theorem unique_free_trace (hdense : Dense d.quotientDomain) (M : Set Sphere)
    (hM : ∀ i, (c i).exclusions ∩ d.dust ⊆ M)
    (x : Sphere) (hx : x ∈ d.dust \ M) (i : ℕ) (a b : UnitAddCircle)
    (ha : (a, x) ∈ (realTestLevelData d c).levels i)
    (hb : (b, x) ∈ (realTestLevelData d c).levels i) : a = b := by
  have hunit (y : Sphere) (_ : y ∈ d.quotientDomain) : |(c i).coordinate.quotient y| ≤ 1 := by
    rw [abs_of_nonneg ((c i).coordinate.quotient_unit y).1]
    exact ((c i).coordinate.quotient_unit y).2
  have hcl : x ∈ closure d.quotientDomain := by rw [hdense.closure_eq]; trivial
  have hw : (c i).weight x = 0 := by
    by_contra h
    exact hx.2 (hM i ⟨(c i).weight_support h, hx.1⟩)
  have hle : limsup (c i).coordinate.quotient (𝓝[d.quotientDomain] x) -
      liminf (c i).coordinate.quotient (𝓝[d.quotientDomain] x) ≤ 0 := by
    apply ENNReal.ofReal_eq_zero.mp
    exact le_antisymm (by simpa only [hw] using (c i).band_bound x hx.1) bot_le
  have heq : limsup (c i).coordinate.quotient (𝓝[d.quotientDomain] x) =
      liminf (c i).coordinate.quotient (𝓝[d.quotientDomain] x) :=
    sub_eq_zero.mp (le_antisymm hle (boundary_width_nonneg hunit hcl))
  have hf : {t | (x, t) ∈ circleBandGraph d.quotientDomain (c i).coordinate.quotient} =
      {((liminf (c i).coordinate.quotient (𝓝[d.quotientDomain] x) : ℝ) : UnitAddCircle)} := by
    rw [circleBandGraph_fiber_eq_image_realFiber,
      intervalFiberHull_clusterGraph_eq_boundary_band hunit hcl, heq, Icc_self,
      image_singleton]
  have ha' : a ∈ ({t | (x, t) ∈ circleBandGraph d.quotientDomain (c i).coordinate.quotient}) := ha
  have hb' : b ∈ ({t | (x, t) ∈ circleBandGraph d.quotientDomain (c i).coordinate.quotient}) := hb
  rw [hf] at ha' hb'
  exact ha'.trans hb'.symm

theorem level_relation (i : ℕ) :
    levelRelation (realTestLevelData d c).levels i =
      circleBandGraph d.quotientDomain (c i).coordinate.quotient := by
  ext p
  rfl

theorem compatibility {M : Set Sphere}
    (hB : d.dust = π '' d.physicalDomainᶜ)
    (F : FiniteTransfer.CountableRealCoordinates d.physicalDomain π (fun x : M => x.val))
    (hF : F.NaturalCompatibility)
    (hsource : F.source = d.quotientDomain)
    (hcoordinate : ∀ k, F.coordinate k = (c k).coordinate.quotient) :
    OrderedLevelNullCompatibility (realTestLevelData d c).levels (d.dust \ M) := by
  intro j n labels hlt
  have h := hF j n labels hlt
  have hrel : levelRelation (realTestLevelData d c).levels =
      (fun i => circleBandGraph d.quotientDomain (c i).coordinate.quotient) :=
    funext (level_relation c)
  rw [hrel]
  simpa only [← hB, Subtype.range_val, hsource, hcoordinate, level_relation,
    MeasureTheory.volume_pi] using h

end realTestLevelData

omit [MeasurableSpace C(PathTime, Sphere)] in
theorem OrderedLevelNullCompatibility.mono {H : ℕ → Set (UnitAddCircle × Sphere)}
    {F K : Set Sphere} (h : OrderedLevelNullCompatibility H K) (hFK : F ⊆ K) :
    OrderedLevelNullCompatibility H F := by
  intro j n labels hlt
  apply measure_mono_null _ (h j n labels hlt)
  rintro _ ⟨⟨x, t, θ⟩, hx, rfl⟩
  exact ⟨(x, t, θ), ⟨hFK hx.1, hx.2⟩, rfl⟩

end CircleDomainRigidity

end

end OAI
