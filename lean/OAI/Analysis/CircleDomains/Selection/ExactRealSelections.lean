import OAI.Analysis.CircleDomains.Transfer.RealPresentationTransfer
import Mathlib.Basic.Denumerable

namespace OAI

/-! Enumerate the actual real choices without repetition, preserving their chosen lifts and
exact band widths. Infinitely many seed labels provide the required infinite index set. -/

open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

 theorem infinite_real_presentations_of_seed
    {hsch : PlanarSchoenflies} {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {L : Type*}
    (C : L → MaskedCoordinateData d.physicalDomain d.quotientDomain π
      (fun x : d.dust => x.val))
    (presentation : ∀ l, SelectedLevelPresentation hsch d π (C l))
    (seed : ℕ → L) (hinj : Injective seed)
    (hseed : ∀ n, ∃ r, presentation (seed n) = Sum.inl r) :
    {l | ∃ r, presentation l = Sum.inl r}.Infinite := by
  apply (Set.infinite_range_of_injective hinj).mono
  rintro _ ⟨n, rfl⟩
  exact hseed n

 theorem exists_injective_real_presentations
    {hsch : PlanarSchoenflies} {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {L : Type*} [Countable L]
    (C : L → MaskedCoordinateData d.physicalDomain d.quotientDomain π
      (fun x : d.dust => x.val))
    (presentation : ∀ l, SelectedLevelPresentation hsch d π (C l))
    (hinfinite : {l | ∃ r, presentation l = Sum.inl r}.Infinite) :
    ∃ ι : ℕ → L, Injective ι ∧
      ∃ R : ∀ n, RealCoordinatePresentation d π (C (ι n)),
        (∀ n, presentation (ι n) = Sum.inl (R n)) ∧
        ∀ l (r : RealCoordinatePresentation d π (C l)), presentation l = Sum.inl r →
          ∃ n, ι n = l ∧ (R n).coordinate.physical = r.coordinate.physical ∧
            (R n).coordinate.quotient = r.coordinate.quotient := by
  let S : Set L := {l | ∃ r, presentation l = Sum.inl r}
  let : Infinite S := hinfinite.to_subtype
  let : Denumerable S := Classical.choice (nonempty_denumerable S)
  let e : ℕ ≃ S := (Denumerable.eqv S).symm
  let ι : ℕ → L := fun n => (e n).val
  have hR (n : ℕ) : ∃ r, presentation (ι n) = Sum.inl r := (e n).property
  let R (n : ℕ) := Classical.choose (hR n)
  have hp (n : ℕ) : presentation (ι n) = Sum.inl (R n) := Classical.choose_spec (hR n)
  refine ⟨ι, Subtype.val_injective.comp e.injective, R, hp, ?_⟩
  intro l r hr
  obtain ⟨n, hn⟩ := e.surjective ⟨l, r, hr⟩
  have hl : ι n = l := congrArg Subtype.val hn
  subst l
  have heq : R n = r := Sum.inl.inj ((hp n).symm.trans hr)
  exact ⟨n, rfl, congrArg (fun q => q.coordinate.physical) heq,
    congrArg (fun q => q.coordinate.quotient) heq⟩

end CircleDomainRigidity

end

end OAI
