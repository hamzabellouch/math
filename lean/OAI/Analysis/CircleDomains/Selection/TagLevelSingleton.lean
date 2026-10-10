import OAI.Analysis.CircleDomains.Selection.TuplePairCompatibility
import OAI.Analysis.CircleDomains.Topology.TagPairTopology

namespace OAI

/-! At an independent compatible level, a free contact inside an active
tag belongs to a singleton component of that level. This is the first
topological step of the generic-intersection argument. -/

open Set Function
open scoped Topology Classical

noncomputable section
namespace CircleDomainRigidity

def singleLevelTuple (i : ℕ) (θ : UnitAddCircle) : LevelTuple :=
  ⟨0, (fun _ => i), fun _ => θ⟩

theorem active_tag_singleton_at_compatible_level
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (H : ℕ → Set (UnitAddCircle × X)) (hH : ∀ i, IsClosed (H i))
    (Free : Set X) (γ : C(PathTime, X)) (q : TagData)
    (hshape : (γ, Sum.inr q) ∈ validTagShape)
    (hcontain : (γ, Sum.inr q) ∈ tagContainment H)
    (t : PathTime) (hl : tagLeft (Sum.inr q) < t) (hr : t < tagRight (Sum.inr q))
    (hx : γ t ∈ Free)
    (hunique : ∀ i a b, (a, γ t) ∈ H i → (b, γ t) ∈ H i → a = b)
    (i : ℕ) (θ : UnitAddCircle) (hθ : (θ, γ t) ∈ H i)
    (hc : TuplePairCompatible H Free (tagDataTuple q) (singleLevelTuple i θ)) :
    ¬ (connectedComponentIn {x | (θ, x) ∈ H i} (γ t)).Nontrivial := by
  intro hnt
  apply tag_impossible_below_compatible_level H hH γ q hshape hcontain t hl hr i
  · intro k hk
    rcases lt_trichotomy (q.2.1 k) i with hlt | he | hgt
    · exact hlt
    · have heq : q.2.2.1 k = θ := hunique i _ _ (he ▸ hk) hθ
      exact (hc.1 k 0 he heq).elim
    · have hh := hc.2.2 k (Finset.univ : Finset (Fin 1))
        (fun _ _ => hgt) (γ t) hx hk
      apply False.elim
      have hset : (⋃ k ∈ (Finset.univ : Finset (Fin 1)), {y | (θ, y) ∈ H i}) =
          {y | (θ, y) ∈ H i} := by
        ext y
        constructor
        · intro hy
          obtain ⟨_, _, hy⟩ := mem_iUnion₂.mp hy
          exact hy
        · intro hy
          exact mem_iUnion₂.mpr ⟨0, Finset.mem_univ _, hy⟩
      change ¬ (connectedComponentIn
        (⋃ k ∈ (Finset.univ : Finset (Fin 1)), {y | (θ, y) ∈ H i}) (γ t)).Nontrivial at hh
      rw [hset] at hh
      exact hh hnt
  · intro A hA
    exact hc.2.1 0 A hA (γ t) hx hθ

end CircleDomainRigidity

end

end OAI
