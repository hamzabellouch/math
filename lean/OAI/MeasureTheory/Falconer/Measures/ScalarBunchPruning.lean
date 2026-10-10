import OAI.MeasureTheory.Falconer.Estimates.ScalarBunchTransfer

namespace OAI

/-! The entire greedy ledger is realized by successive prunings of the
 original finite paths. All losses multiply exactly, and each retained
 bunch keeps its proved separation and branching count. -/
namespace Falconer.Regularization

 theorem scalar_trim_bunch_chain {N top lo : ℕ} {bs : List ScalarBunch}
    (hchain : ScalarBunchChain top lo bs) (d k : ℕ → ℕ) (hd : Monotone d)
    (gap : ScalarBunch → ℝ) :
    ∀ (L : Finset (CellPath 1)) (m : ℕ), L ⊆ cubePaths 1 N → L.Nonempty → d top ≤ N →
    (∀ i < top, ∀ p ∈ L.image (List.take (d i)),
      (prefixChildren L (d i) (d (i+1)) p).card = 2^(k i)) →
    (∀ p ∈ L.image (List.take (d top)), (prefixFiber L (d top) p).card = m) →
    (∀ b ∈ bs, ∀ p ∈ L.image (List.take (d b.start)),
      ∀ u ∈ prefixChildren L (d b.start) (d b.cut) p,
      ∀ v ∈ prefixChildren L (d b.start) (d b.cut) p,
      u ≠ v → gap b ≤ |scalarPathCenter u-scalarPathCenter v|) →
    ∃ Q : Finset (CellPath 1), Q ⊆ L ∧ Q.Nonempty ∧
      L.card = 2^((bs.map (fun b => ∑ i ∈ Finset.Ico b.cut b.stop, k i)).sum)*Q.card ∧
      (∀ c ≤ d lo, Q.image (List.take c) = L.image (List.take c)) ∧
      (∀ c, d top ≤ c → ∀ q ∈ Q, prefixFiber Q c (q.take c) = prefixFiber L c (q.take c)) ∧
      (∀ b ∈ bs, ScalarPathLevel Q (d b.start) (d b.stop)
        (2^(∑ i ∈ Finset.Ico b.start b.cut, k i)) (gap b-2*(1/2:ℝ)^(d b.cut))) := by
  induction hchain with
  | nil n =>
    intro L m hL hne hN hcard hm hg
    refine ⟨L,Finset.Subset.refl _,hne,by simp,?_,?_,by simp⟩
    · intro c hc
      rfl
    · intro c hc q hq
      rfl
  | @cons b lo bs hchain ih =>
    intro L m hL hne hN hcard hm hg
    have hsc : b.start ≤ b.cut := b.start_lt_cut.le
    have hsb : b.start ≤ b.stop := hsc.trans b.cut_le_stop
    obtain ⟨F,hF,hRne,hcost,hlevel,hmR⟩ := scalar_trimmed_uniform_block L hL hne d k hd
      hsc b.cut_le_stop hN hcard hm (gap b) (hg b (by simp))
    let R := scalarPruneLeaves L (d b.cut) (d b.stop) F
    have hRL : R ⊆ L := scalarPruneLeaves_subset L _ _ F
    have hFn : ∀ p ∈ L.image (List.take (d b.cut)),
        (F p).Nonempty ∧ F p ⊆ prefixChildren L (d b.cut) (d b.stop) p := by
      intro p hp
      exact ⟨Finset.card_pos.mp (by rw [(hF p hp).2]; omega),(hF p hp).1⟩
    have hcardR : ∀ i < b.start, ∀ p ∈ R.image (List.take (d i)),
        (prefixChildren R (d i) (d (i+1)) p).card = 2^(k i) := by
      intro i hi p hp
      rw [scalarPruneLeaves_upper_children L (hd (Nat.le_succ i))
        (hd (show i+1 ≤ b.cut by omega)) F hFn]
      exact hcard i (lt_of_lt_of_le hi hsb) p (Finset.image_subset_image hRL hp)
    have hgR : ∀ c ∈ bs, ∀ p ∈ R.image (List.take (d c.start)),
        ∀ u ∈ prefixChildren R (d c.start) (d c.cut) p,
        ∀ v ∈ prefixChildren R (d c.start) (d c.cut) p,
        u ≠ v → gap c ≤ |scalarPathCenter u-scalarPathCenter v| := by
      intro c hc p hp u hu v hv huv
      exact hg c (by simp [hc]) p (Finset.image_subset_image hRL hp)
        u (prefixChildren_mono hRL _ _ _ hu) v (prefixChildren_mono hRL _ _ _ hv) huv
    obtain ⟨Q,hQR,hQne,hcostQ,hupperQ,hfiberQ,hlevelsQ⟩ :=
      ih R ((2^(∑ i ∈ Finset.Ico b.start b.cut, k i))*m) (hRL.trans hL) hRne
        ((hd hsb).trans hN) hcardR hmR hgR
    refine ⟨Q,hQR.trans hRL,hQne,?_,?_,?_,?_⟩
    · rw [hcost,hcostQ]
      simp only [List.map_cons,List.sum_cons,pow_add]
      exact (Nat.mul_assoc _ _ _).symm
    · intro c hc
      rw [hupperQ c hc]
      exact scalarPruneLeaves_upper_prefixes L
        (hc.trans ((hd hchain.start_le).trans (hd hsc))) F hFn
    · intro c hc q hq
      rw [hfiberQ c ((hd hsb).trans hc) q hq]
      exact scalarPruneLeaves_fiber L (hd b.cut_le_stop) hc F (hQR hq)
    · intro c hc
      rcases List.mem_cons.mp hc with heq | hc
      · subst c
        exact hlevel.of_same_fibers hQR (fun q hq => hfiberQ _ le_rfl q hq)
      · exact hlevelsQ c hc

end Falconer.Regularization

end OAI
