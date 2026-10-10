import OAI.Combinatorics.BalancedRyser.Local.LocalSpecificationEncoding
import OAI.Combinatorics.BalancedRyser.Probability.FiniteDependencyRank

namespace OAI

namespace Balanced.Local.ConditionSpec

noncomputable section
open scoped Classical

variable {b κ n : ℕ}

theorem exists_goodSpecification_of_acyclic_fixed
    (u : Position b → Position b) (I T : Finset (Position b))
    (hTI : T ⊆ I) (hcard : T.card = n) (hfix : ∀ v ∈ T, u v = v)
    (code : Position b → Code b κ)
    (hwf : WellFounded (fun x y : {v // v ∈ T} =>
      y.val ∈ underlyingAnchors u (code x.val)))
    (E : Position b → Code b κ → Prop) (hE : ∀ v ∈ T, E v (code v)) :
    ∃ σ : Fin n → Position b × Code b κ,
      GoodSpecification u I σ ∧
      (∀ k, E (σ k).1 (σ k).2) ∧
      Finset.univ.image (fun k => (σ k).1) = T := by
  obtain ⟨rank, hrank⟩ := exists_nat_rank_on_finset T
    (fun v w => w ∈ underlyingAnchors u (code v)) hwf
  apply exists_goodSpecification_of_finset u I T hTI hcard
    (fun v hv w hw h => by simpa only [hfix v hv, hfix w hw] using h)
    code rank _ E hE
  intro v hv w hw hdep
  rw [hfix v hv, hfix w hw]
  exact hrank v hv w hw (by simpa only [underlyingAnchors, hfix w hw] using hdep)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem badCover_zero_reuse_exists_goodSpecification
    (P : EqualityPattern b 0) (a : DirectionAssignment F b 0)
    (bits : Bits b) (p : Point F) (M : MergedPairs F)
    (hb : 3 ≤ b) (ha : Eligible P a)
    (hadm : Admissible P a bits p M) (hbad : BadCover P a bits p M) :
    ∃ σ : Fin 3 → Position b × Code b 0,
      GoodSpecification id Finset.univ σ ∧
      ∀ k, Holds P a bits p M (σ k).1 (σ k).2 := by
  obtain ⟨T, code, hcard, hT, hwf⟩ :=
    badCover_zero_reuse_exists_acyclic_spec P a bits p M hb ha hadm hbad
  obtain ⟨σ, hσ, hE, _⟩ := exists_goodSpecification_of_acyclic_fixed
    id Finset.univ T (Finset.subset_univ _) hcard (fun _ _ => rfl) code
    (by simpa only [underlyingAnchors, Finset.image_id] using hwf)
    (Holds P a bits p M) (fun v hv => (hT v hv).1)
  exact ⟨σ, hσ, hE⟩

theorem badCover_one_reuse_exists_goodSpecification
    (P : EqualityPattern b 1) (a : DirectionAssignment F b 1)
    (bits : Bits b) (p : Point F) (M : MergedPairs F)
    (hb : 3 ≤ b) (ha : Eligible P a)
    (hadm : Admissible P a bits p M) (hbad : BadCover P a bits p M)
    (root child : Fin b) (r s : Fin 4)
    (hshared : P.classOf root r = P.classOf child s) :
    let u := ParentMap.underlying root child r s (bits root r) (bits child s)
    ∃ σ : Fin 2 → Position b × Code b 1,
      GoodSpecification u (Finset.univ \ ParentMap.dependent child s) σ ∧
      ∀ k, Holds P a bits p M (σ k).1 (σ k).2 := by
  dsimp only
  let u := ParentMap.underlying root child r s (bits root r) (bits child s)
  obtain ⟨T, code, hcard, hT, hwf⟩ :=
    badCover_one_reuse_exists_acyclic_spec P a bits p M hb ha hadm hbad
      root child r s hshared
  have hTI : T ⊆ Finset.univ \ ParentMap.dependent child s := by
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (hT v hv).1⟩
  have hfix : ∀ v ∈ T, u v = v := by
    intro v hv
    exact ParentMap.underlying_fixed root child r s (bits root r) (bits child s)
      (hT v hv).1
  obtain ⟨σ, hσ, hE, _⟩ := exists_goodSpecification_of_acyclic_fixed u
    (Finset.univ \ ParentMap.dependent child s) T hTI hcard hfix code hwf
    (Holds P a bits p M) (fun v hv => (hT v hv).2.1)
  exact ⟨σ, hσ, hE⟩

end
end Balanced.Local.ConditionSpec

end OAI
