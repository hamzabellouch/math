import OAI.Combinatorics.Ryser.Construction.AmbientPoolExistence
import OAI.Combinatorics.Ryser.Construction.SelectedHypergraph
import OAI.Combinatorics.Ryser.Construction.PoolThinSelection
import OAI.Combinatorics.Ryser.Construction.DeterministicCover
import OAI.Combinatorics.Ryser.Hypergraph.Infinitude

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F : Type} [Field k] [Field F] [Fintype k] [Fintype F]
  [DecidableEq k] [DecidableEq F]

theorem counterexampleRank_of_goodAmbientPool
    (σ : k →+* F) (u v : k) (huv : u ≠ v) (hu : u ≠ 0) (hv : v ≠ 0)
    (a : GadgetOutcome k) (ha : GoodGadget a)
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (K : ℕ) (pool : AmbientPool σ K)
    (hpool : GoodAmbientPool σ u v huv a ha.1 K pool)
    (hgap : 1 + ambientDeletionDelta (Fintype.card k) K / 10 * Fintype.card F <
      ambientDeletionDelta (Fintype.card k) K * Fintype.card F / 2) :
    CounterexampleRank (Fintype.card F + 1) := by
  classical
  obtain ⟨⟨choiceFin, hchoice⟩, hrigid, hthin⟩ := hpool
  let choice : ConfigurationGroup σ → Fin K := fun i =>
    choiceFin ((Fintype.equivFin (ConfigurationGroup σ)) i)
  let b : ConfigurationGroup σ → Point F := fun i => pool i (choice i)
  let X := ambientSelectedSurvivors σ u v huv a K pool choice
  let data := ambientSelectedConfiguration σ u v huv a K pool choice
  let δ := ambientDeletionDelta (Fintype.card k) K
  have hshift : selectedShifts σ (ambientFlatPoolEquiv σ K pool) choiceFin = b := by
    funext i
    change pool ((Fintype.equivFin (ConfigurationGroup σ)).symm
      ((Fintype.equivFin (ConfigurationGroup σ)) i))
        (choiceFin ((Fintype.equivFin (ConfigurationGroup σ)) i)) =
      pool i (choiceFin ((Fintype.equivFin (ConfigurationGroup σ)) i))
    rw [Equiv.symm_apply_apply]
  have hsep : DeletionSeparated σ (groupPlacement σ u v huv) b a := by
    have h := selectedShifts_deletionSeparated σ u v huv
      (ambientFlatPoolEquiv σ K pool) choiceFin hchoice a
    rw [hshift] at h
    exact h
  obtain ⟨hline, hnear⟩ := ambientPool_goodLineCover_selected
    σ u v huv a ha.1 K pool choice δ (δ / 10) hrigid
  have hnear' : ∀ L : Finset (AffineLine F), L.card ≤ Fintype.card F →
      (∀ x ∈ X, ∃ ell ∈ L, Incidence x ell) →
      ∃ p : ProjectivePoint F,
        (1 - δ / 10) * Fintype.card F ≤ ((L ∩ affinePencil p).card : ℝ) := by
    intro L hL hcover
    have hsub : X ⊆ L.biUnion linePoints := by
      intro x hx
      obtain ⟨ell, hell, hxell⟩ := hcover x hx
      exact Finset.mem_biUnion.mpr ⟨ell, hell, (mem_linePoints x ell).mpr hxell⟩
    obtain ⟨p, hp⟩ := hnear L hL hsub
    refine ⟨p, ?_⟩
    have heq : LineCover.coverPencil L p = L ∩ affinePencil p := by
      ext ell
      simp only [LineCover.mem_coverPencil, Finset.mem_inter, mem_affinePencil]
    rw [heq] at hp
    exact hp
  have hthin' : ∀ p : Point F, OffPencilThin data p := fun p =>
    offPencilThin_of_groupPoolThin σ u v huv pool choice (retainedPoints a) X hthin p
  have hne : (hypergraph data).Nonempty :=
    ambientSelectedHypergraph_nonempty σ u v huv a K pool choice ha
  have hI : Intersecting (hypergraph data) :=
    ambientSelectedHypergraph_intersecting σ u v huv a K pool choice hcop hsep
  have hpart : RPartiteUniform (Fintype.card F + 1) (hypergraph data) :=
    ambientSelectedHypergraph_rPartiteUniform σ u v huv a K pool choice
  apply counterexampleRank_of_no_small_cover (Nat.zero_lt_succ _) hne hpart hI
  intro C hCcard
  have hCq : C.card ≤ Fintype.card F := by omega
  have hnot := not_isCover_actual_group_configuration σ u v huv a b X hu hv hcop ha
    δ (ambientDeletionDelta_pos _ _) hgap hsep hthin' hline hnear' C hCq
  have hdec : instDecidableEqConfigurationGroup σ =
      (inferInstance : DecidableEq (ConfigurationGroup σ)) := Subsingleton.elim _ _
  rw [hdec] at hnot
  exact hnot

end RyserCoveringCounterexample.Construction

end

end OAI
