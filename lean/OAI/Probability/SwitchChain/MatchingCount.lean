import OAI.Probability.SwitchChain.Definitions

namespace OAI

noncomputable section

namespace Problem315.MatchingCount

abbrev FixedPointFreeInvolution (V : Type*) :=
  {f : V → V // Function.Involutive f ∧ ∀ v, f v ≠ v}

instance {V : Type*} [Fintype V] [DecidableEq V] :
    Fintype (FixedPointFreeInvolution V) := by
  letI : DecidablePred (fun f : V → V => Function.Involutive f ∧ ∀ v, f v ≠ v) :=
    fun f => inferInstanceAs (Decidable ((∀ v, f (f v) = v) ∧ ∀ v, f v ≠ v))
  exact Subtype.fintype _

private theorem involution_fin_four_card :
    Fintype.card (FixedPointFreeInvolution (Fin 4)) = 3 := by
  decide

noncomputable def involutionCongr {V W : Type*} (e : V ≃ W) :
    FixedPointFreeInvolution V ≃ FixedPointFreeInvolution W where
  toFun f := ⟨fun w => e (f.val (e.symm w)), by
    constructor
    · intro w
      simp only [Equiv.symm_apply_apply]
      rw [f.property.1 (e.symm w), Equiv.apply_symm_apply]
    · intro w h
      have h' := congrArg e.symm h
      simp only [Equiv.symm_apply_apply] at h'
      exact f.property.2 (e.symm w) h'⟩
  invFun f := ⟨fun v => e.symm (f.val (e v)), by
    constructor
    · intro v
      simp only [Equiv.apply_symm_apply]
      rw [f.property.1 (e v), Equiv.symm_apply_apply]
    · intro v h
      have h' := congrArg e h
      simp only [Equiv.apply_symm_apply] at h'
      exact f.property.2 (e v) h'⟩
  left_inv f := by ext v; simp
  right_inv f := by ext v; simp

 theorem involution_card_of_card_four {V : Type*} [Fintype V]
    (hV : Fintype.card V = 4) : Nat.card (FixedPointFreeInvolution V) = 3 := by
  classical
  let e : V ≃ Fin 4 := Fintype.equivFinOfCardEq hV
  rw [Nat.card_congr (involutionCongr e), Nat.card_eq_fintype_card]
  exact involution_fin_four_card

variable {n : ℕ} {S : FourSet n}

private theorem matching_neighbor_mem (M : PerfectMatching S)
    {u v : Fin n} (h : M.val.Adj u v) : v ∈ S.val := by
  by_contra hv
  exact ((M.property v).2 hv u) (M.val.symm.symm u v h)

noncomputable def mate (M : PerfectMatching S) (v : S.val) : S.val :=
  ⟨Classical.choose ((M.property v.val).1 v.property).exists,
    matching_neighbor_mem M (Classical.choose_spec ((M.property v.val).1 v.property).exists)⟩

private theorem mate_adj (M : PerfectMatching S) (v : S.val) :
    M.val.Adj v.val (mate M v).val :=
  Classical.choose_spec ((M.property v.val).1 v.property).exists

private theorem mate_unique (M : PerfectMatching S) (v : S.val) {w : Fin n}
    (hw : M.val.Adj v.val w) : w = (mate M v).val :=
  ((M.property v.val).1 v.property).unique hw (mate_adj M v)

noncomputable def matchingToInvolution (M : PerfectMatching S) :
    FixedPointFreeInvolution S.val := ⟨mate M, by
  constructor
  · intro v
    apply Subtype.ext
    exact (mate_unique M (mate M v) (M.val.symm.symm _ _ (mate_adj M v))).symm
  · intro v h
    have hh := mate_adj M v
    rw [h] at hh
    exact M.val.loopless.irrefl _ hh⟩

def involutionGraph (f : FixedPointFreeInvolution S.val) : SimpleGraph (Fin n) where
  Adj u v := ∃ (hu : u ∈ S.val) (hv : v ∈ S.val), f.val ⟨u, hu⟩ = ⟨v, hv⟩
  symm := by
    constructor
    rintro u v ⟨hu, hv, h⟩
    refine ⟨hv, hu, ?_⟩
    rw [← h, f.property.1]
  loopless := by
    constructor
    rintro v ⟨hv, hv', h⟩
    exact f.property.2 ⟨v, hv⟩ h

noncomputable def involutionToMatching (f : FixedPointFreeInvolution S.val) :
    PerfectMatching S := ⟨involutionGraph f, by
  intro v
  constructor
  · intro hv
    refine ⟨(f.val ⟨v, hv⟩).val, ?_, ?_⟩
    · exact ⟨hv, (f.val ⟨v, hv⟩).property, rfl⟩
    · rintro w ⟨hv', hw, h⟩
      exact (congrArg Subtype.val h).symm
  · intro hv w h
    exact hv h.choose⟩

noncomputable def matchingEquivInvolution (S : FourSet n) :
    PerfectMatching S ≃ FixedPointFreeInvolution S.val where
  toFun := matchingToInvolution
  invFun := involutionToMatching
  left_inv M := by
    apply Subtype.ext
    apply SimpleGraph.ext
    funext u v
    apply propext
    constructor
    · rintro ⟨hu, hv, h⟩
      have hh := mate_adj M ⟨u, hu⟩
      change mate M ⟨u, hu⟩ = ⟨v, hv⟩ at h
      rw [h] at hh
      exact hh
    · intro h
      have hu := matching_neighbor_mem M (M.val.symm.symm _ _ h)
      have hv := matching_neighbor_mem M h
      refine ⟨hu, hv, ?_⟩
      apply Subtype.ext
      exact (mate_unique M ⟨u, hu⟩ h).symm
  right_inv f := by
    apply Subtype.ext
    funext v
    apply Subtype.ext
    exact (mate_unique (involutionToMatching f) v
      ⟨v.property, (f.val v).property, rfl⟩).symm

theorem perfectMatching_card (S : FourSet n) : Nat.card (PerfectMatching S) = 3 := by
  rw [Nat.card_congr (matchingEquivInvolution S)]
  apply involution_card_of_card_four
  simpa only [Fintype.card_coe] using S.property

theorem orderedMatchings_card (S : FourSet n) :
    Nat.card {p : PerfectMatching S × PerfectMatching S // p.1 ≠ p.2} = 6 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hfilter : (Finset.univ.filter fun p : PerfectMatching S × PerfectMatching S => p.1 ≠ p.2) =
      (Finset.univ : Finset (PerfectMatching S)).offDiag := by
    ext p
    simp
  rw [hfilter, Finset.offDiag_card, Finset.card_univ]
  have hcard : Fintype.card (PerfectMatching S) = 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact perfectMatching_card S
  rw [hcard]

theorem fourSet_card (n : ℕ) : Nat.card (FourSet n) = n.choose 4 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.univ_filter_card_eq, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

theorem switchProposal_card (n : ℕ) : Nat.card (SwitchProposal n) = 6 * n.choose 4 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  have hcard (S : FourSet n) :
      Fintype.card {p : PerfectMatching S × PerfectMatching S // p.1 ≠ p.2} = 6 := by
    rw [← Nat.card_eq_fintype_card]
    exact orderedMatchings_card S
  simp_rw [hcard]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card,
    fourSet_card, Nat.mul_comm]

theorem allProposals_card (n : ℕ) : (allProposals n).card = 6 * n.choose 4 := by
  classical
  unfold allProposals
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
  exact switchProposal_card n

end Problem315.MatchingCount

end

end OAI
