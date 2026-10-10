import OAI.Analysis.CircleDomains.Selection.SelectedLevelPresentation
import OAI.Analysis.CircleDomains.Selection.RealCoordinateSubfamily

namespace OAI

/-! Retain every selected real presentation in the mixed transfer, including
real barriers chosen after the initial seed. Its physical function and
actual marked band widths are the same ones used by the selection. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

 theorem PhysicalRealCoordinate.boundary_width_le_one
    {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    (Q : PhysicalRealCoordinate d π) (hdense : Dense d.quotientDomain) (x : Sphere) :
    limsup Q.quotient (𝓝[d.quotientDomain] x) -
      liminf Q.quotient (𝓝[d.quotientDomain] x) ≤ 1 := by
  have hcl : x ∈ closure d.quotientDomain := by rw [hdense.closure_eq]; trivial
  let : NeBot (𝓝[d.quotientDomain] x) := mem_closure_iff_nhdsWithin_neBot.mp hcl
  have hlo : 0 ≤ liminf Q.quotient (𝓝[d.quotientDomain] x) :=
    le_liminf_of_le (isBoundedUnder_of_eventually_le
      (Eventually.of_forall fun y => (Q.quotient_unit y).2)).isCoboundedUnder_ge
      (Eventually.of_forall fun y => (Q.quotient_unit y).1)
  have hhi : limsup Q.quotient (𝓝[d.quotientDomain] x) ≤ 1 :=
    limsup_le_of_le (isBoundedUnder_of_eventually_ge
      (Eventually.of_forall fun y => (Q.quotient_unit y).1)).isCoboundedUnder_le
      (Eventually.of_forall fun y => (Q.quotient_unit y).2)
  linarith

 theorem RealCoordinatePresentation.width_le
    {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {C : MaskedCoordinateData d.physicalDomain d.quotientDomain π
      (fun x : d.dust => x.val)}
    (R : RealCoordinatePresentation d π C) (hdense : Dense d.quotientDomain) (s : d.dust) :
    limsup R.coordinate.quotient (𝓝[d.quotientDomain] s.val) -
      liminf R.coordinate.quotient (𝓝[d.quotientDomain] s.val) ≤ C.upper s - C.lower s := by
  apply (ENNReal.ofReal_le_ofReal_iff (C.width_nonneg s)).mp
  apply band_width_le_of_fiber_subset (M := 1)
    (fun x _ => by
      rw [abs_of_nonneg (R.coordinate.quotient_unit x).1]
      exact (R.coordinate.quotient_unit x).2)
    (by rw [hdense.closure_eq]; trivial) (R.coordinate.boundary_width_le_one hdense s.val)
  intro θ hθ
  apply C.marked_fiber s
  rwa [R.graph_eq]

 def realSubfamily_of_presentations
    {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {L A : Type*}
    (C : L → MaskedCoordinateData d.physicalDomain d.quotientDomain π
      (fun x : d.dust => x.val))
    (ι : A → L) (R : ∀ j, RealCoordinatePresentation d π (C (ι j)))
    (hdense : Dense d.quotientDomain) : RealCoordinateSubfamily C ι where
  physical j := (R j).coordinate.physical
  quotient j := (R j).coordinate.quotient
  bound _ := 1
  bounded j x _ := by
    rw [abs_of_nonneg ((R j).coordinate.quotient_unit x).1]
    exact ((R j).coordinate.quotient_unit x).2
  full_mask j := (R j).mask_eq_univ
  smooth j := (R j).coordinate.physical_smooth
  energy j := (R j).coordinate.physical_energy
  pullback j x hx := by
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using
      ((R j).coordinate.pullback (Complex.equivRealProdCLM.symm x) hx).symm
  projection j x := (R j).physical_eq x
  width j s := (R j).width_le hdense s

 theorem exists_real_subfamily_covering_presentations
    {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {L : Type*} [Countable L]
    (C : L → MaskedCoordinateData d.physicalDomain d.quotientDomain π
      (fun x : d.dust => x.val))
    (hdense : Dense d.quotientDomain)
    (l₀ : L) (h₀ : Nonempty (RealCoordinatePresentation d π (C l₀))) :
    ∃ ι : ℕ → L, Nonempty (RealCoordinateSubfamily C ι) ∧
      ∀ l, Nonempty (RealCoordinatePresentation d π (C l)) → l ∈ range ι := by
  let S : Set L := {l | Nonempty (RealCoordinatePresentation d π (C l))}
  obtain ⟨ι, hι⟩ := (Set.to_countable S).exists_eq_range ⟨l₀, h₀⟩
  have hR (n : ℕ) : Nonempty (RealCoordinatePresentation d π (C (ι n))) := by
    change ι n ∈ S
    rw [hι]
    exact mem_range_self n
  let R (n : ℕ) := Classical.choice (hR n)
  refine ⟨ι, ⟨realSubfamily_of_presentations C ι R hdense⟩, ?_⟩
  intro l hl
  exact hι ▸ hl


 theorem exists_real_subfamily_of_selected_presentations
    (hsch : PlanarSchoenflies)
    {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {L : Type*} [Countable L]
    (C : L → MaskedCoordinateData d.physicalDomain d.quotientDomain π
      (fun x : d.dust => x.val))
    (presentation : ∀ l, SelectedLevelPresentation hsch d π (C l))
    (hdense : Dense d.quotientDomain)
    (l₀ : L) (r₀ : RealCoordinatePresentation d π (C l₀))
    (h₀ : presentation l₀ = Sum.inl r₀) :
    ∃ (ι : ℕ → L) (R : RealCoordinateSubfamily C ι),
      ∀ l (r : RealCoordinatePresentation d π (C l)), presentation l = Sum.inl r →
        ∃ n, ι n = l ∧ R.physical n = r.coordinate.physical ∧
          R.quotient n = r.coordinate.quotient := by
  let S : Set L := {l | ∃ r, presentation l = Sum.inl r}
  obtain ⟨ι, hι⟩ := (Set.to_countable S).exists_eq_range ⟨l₀, r₀, h₀⟩
  have hR (n : ℕ) : ∃ r, presentation (ι n) = Sum.inl r := by
    change ι n ∈ S
    rw [hι]
    exact mem_range_self n
  let r (n : ℕ) := Classical.choose (hR n)
  have hr (n : ℕ) : presentation (ι n) = Sum.inl (r n) := Classical.choose_spec (hR n)
  refine ⟨ι, realSubfamily_of_presentations C ι r hdense, ?_⟩
  intro l q hq
  have hl : l ∈ range ι := hι ▸ (show l ∈ S from ⟨q, hq⟩)
  obtain ⟨n, hn⟩ := hl
  subst l
  have heq : r n = q := Sum.inl.inj ((hr n).symm.trans hq)
  exact ⟨n, rfl, congrArg (fun t => t.coordinate.physical) heq,
    congrArg (fun t => t.coordinate.quotient) heq⟩

end CircleDomainRigidity

end

end OAI
