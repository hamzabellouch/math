import OAI.Analysis.KadisonSimilarity.Tensor.InvariantTensors

namespace OAI

/-!
# Removing centered singleton cycles

A fixed point contributes the trace of its matrix argument. Factorization
of the coordinate contraction shows that vanishing on
centered singleton tails does not require an additional invariant-theory input.
-/

noncomputable section
namespace KadisonSimilarity

open Finset

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

/-- A permutation fixing `i` preserves the complement of `i`. -/
def fixedPointComplement (π : Equiv.Perm ι) (i : ι) (hi : π i = i)
    (j : {j : ι // j ≠ i}) : {j : ι // j ≠ i} :=
  ⟨π j, fun h => j.2 (π.injective (h.trans hi.symm))⟩

/-- The contraction over all slots except a distinguished fixed point. -/
def fixedPointRemainder (π : Equiv.Perm ι) (i : ι) (hi : π i = i)
    (v : ι → Matrix α α ℂ) : ℂ :=
  ∑ g : {j : ι // j ≠ i} → α,
    ∏ j : {j : ι // j ≠ i}, v j (g j) (g (fixedPointComplement π i hi j))

/-- A fixed point contributes precisely an unnormalized trace factor. -/
theorem permutationContraction_fixedPoint (π : Equiv.Perm ι) (i : ι) (hi : π i = i)
    (v : ι → Matrix α α ℂ) :
    permutationContraction π v = Matrix.trace (v i) * fixedPointRemainder π i hi v := by
  classical
  unfold permutationContraction fixedPointRemainder
  rw [Fintype.sum_equiv (Equiv.funSplitAt i α) _
    (fun fg => v i fg.1 fg.1 *
      ∏ j : {j : ι // j ≠ i}, v j (fg.2 j) (fg.2 (fixedPointComplement π i hi j)))]
  · rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul (Finset.univ : Finset α) (fun a => v i a a)
      (∑ g : {j : ι // j ≠ i} → α,
        ∏ j : {j : ι // j ≠ i}, v j (g j) (g (fixedPointComplement π i hi j)))]
    rfl
  · intro f
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
    simp only [hi]
    rfl

/-- Any singleton cycle on a centered variable vanishes identically. -/
theorem permutationContraction_eq_zero_of_fixed_centered
    (π : Equiv.Perm ι) (i : ι) (hi : π i = i)
    (v : ι → Matrix α α ℂ) (hcenter : Matrix.trace (v i) = 0) :
    permutationContraction π v = 0 := by
  rw [permutationContraction_fixedPoint π i hi, hcenter, zero_mul]

/-- The same deletion holds for the normalized cycle forms. -/
theorem normalizedPermutationContraction_eq_zero_of_fixed_centered
    (π : Equiv.Perm ι) (i : ι) (hi : π i = i)
    (v : ι → Matrix α α ℂ) (hcenter : Matrix.trace (v i) = 0) :
    normalizedPermutationContraction π v = 0 := by
  rw [normalizedPermutationContraction,
    permutationContraction_eq_zero_of_fixed_centered π i hi v hcenter, mul_zero]

/-- On centered tail variables, only permutations without a tail fixed point
contribute. The endpoint slot is exempt from centering. -/
theorem invariant_expansion_remove_centered_singletons
    (i₀ : ι) (v : ι → Matrix α α ℂ)
    (hcenter : ∀ i, i ≠ i₀ → Matrix.trace (v i) = 0)
    (c : Equiv.Perm ι → ℂ) :
    (∑ π, c π * normalizedPermutationContraction π v) =
      ∑ π ∈ Finset.univ.filter (fun π => ∀ i, π i = i → i = i₀),
        c π * normalizedPermutationContraction π v := by
  classical
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _) ?_
  intro π _ hπ
  have hex : ∃ i, π i = i ∧ i ≠ i₀ := by
    by_contra hn
    apply hπ
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    intro i hi
    by_contra hne
    exact hn ⟨i, hi, hne⟩
  obtain ⟨i, hi, hne⟩ := hex
  rw [normalizedPermutationContraction_eq_zero_of_fixed_centered π i hi v (hcenter i hne),
    mul_zero]

/-- The finite set of cycles of a permutation, including fixed points. -/
abbrev PermutationCycles (π : Equiv.Perm ι) :=
  Quotient (Equiv.Perm.SameCycle.setoid π)

noncomputable instance permutationCyclesFintype (π : Equiv.Perm ι) :
    Fintype (PermutationCycles π) := Fintype.ofFinite _

noncomputable instance permutationCyclesDecidableEq (π : Equiv.Perm ι) :
    DecidableEq (PermutationCycles π) := Classical.decEq _

/-- The vertices in one cycle. -/
abbrev CycleMembers (π : Equiv.Perm ι) (q : PermutationCycles π) :=
  {i : ι // (⟦i⟧ : PermutationCycles π) = q}

noncomputable instance cycleMembersFintype (π : Equiv.Perm ι) (q : PermutationCycles π) :
    Fintype (CycleMembers π q) := Fintype.ofFinite _

omit [DecidableEq ι] in
/-- Cycle lengths sum to the number of slots. -/
theorem sum_cycleLengths (π : Equiv.Perm ι) :
    (∑ q : PermutationCycles π, Fintype.card (CycleMembers π q)) = Fintype.card ι := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv (fun i : ι =>
    (⟦i⟧ : PermutationCycles π)))

omit [DecidableEq ι] in
theorem card_permutationCycles (π : Equiv.Perm ι) :
    Fintype.card (PermutationCycles π) = permutationCycleCount π := by
  exact (Nat.card_eq_fintype_card).symm

omit [DecidableEq ι] in
theorem cycleLength_pos (π : Equiv.Perm ι) (q : PermutationCycles π) :
    0 < Fintype.card (CycleMembers π q) := by
  obtain ⟨i, hi⟩ := Quotient.exists_rep q
  exact Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩

omit [DecidableEq ι] in
/-- A cycle containing no fixed point has at least two vertices. -/
theorem two_le_cycleLength (π : Equiv.Perm ι) (q : PermutationCycles π)
    (hfixed : ∀ i, (⟦i⟧ : PermutationCycles π) = q → π i ≠ i) :
    2 ≤ Fintype.card (CycleMembers π q) := by
  obtain ⟨i, hi⟩ := Quotient.exists_rep q
  have hπ : (⟦π i⟧ : PermutationCycles π) = q :=
    (Quotient.sound (show π.SameCycle (π i) i from
      (show π.SameCycle i (π i) from ⟨1, by simp⟩).symm)).trans hi
  have hne : (⟨i, hi⟩ : CycleMembers π q) ≠ ⟨π i, hπ⟩ := by
    intro h
    exact hfixed i hi (congrArg Subtype.val h).symm
  exact Fintype.one_lt_card_iff.mpr ⟨⟨i, hi⟩, ⟨π i, hπ⟩, hne⟩

omit [DecidableEq ι] in
/-- A fixed point forms a cycle of length one. -/
theorem cycleLength_fixedPoint (π : Equiv.Perm ι) (i : ι) (hi : π i = i) :
    Fintype.card (CycleMembers π (⟦i⟧ : PermutationCycles π)) = 1 := by
  apply Fintype.card_eq_one_of_forall_eq (i := ⟨i, rfl⟩)
  intro j
  apply Subtype.ext
  exact (Quotient.exact j.2).eq_of_right hi

/-- The cycle threshold forces the distinguished endpoint to be fixed. The
only other assumption is the already justified removal of tail singletons. -/
theorem cycle_threshold_fixes_endpoint (π : Equiv.Perm ι) (i₀ : ι)
    (hfixed : ∀ i, π i = i → i = i₀)
    (hcount : Fintype.card ι + 1 ≤ 2 * permutationCycleCount π) : π i₀ = i₀ := by
  classical
  by_contra h₀
  have hno : ∀ i, π i ≠ i := by
    intro i hi
    have hieq := hfixed i hi
    subst i
    exact h₀ hi
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (f := fun _ : PermutationCycles π => 2)
    (g := fun q => Fintype.card (CycleMembers π q))
    (fun q _ => two_le_cycleLength π q (fun i _ => hno i))
  rw [sum_cycleLengths] at hsum
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul,
    card_permutationCycles] at hsum
  omega

private theorem sum_endpoint_weights {Q : Type*} [Fintype Q] [DecidableEq Q] (q₀ : Q) :
    (∑ q : Q, if q = q₀ then 1 else 2) + 1 = 2 * Fintype.card Q := by
  have hc : Fintype.card {q : Q // q ≠ q₀} + 1 = Fintype.card Q := by
    simpa only [Fintype.card_option] using Fintype.card_congr (Equiv.optionSubtypeNe q₀)
  rw [Fintype.sum_eq_add_sum_subtype_ne _ q₀]
  have hs : (∑ q : {q : Q // q ≠ q₀}, if (q : Q) = q₀ then 1 else 2) =
      Fintype.card {q : Q // q ≠ q₀} * 2 := by
    calc
      _ = ∑ _q : {q : Q // q ≠ q₀}, 2 :=
        Finset.sum_congr rfl (fun q _ => ite_eq_right q.2)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [hs]
  simp only [ite_true]
  omega

omit [DecidableEq ι] in
/-- At the threshold, every nondistinguished cycle has length two. -/
theorem cycle_threshold_lengths (π : Equiv.Perm ι) (i₀ : ι)
    (hfixed : ∀ i, π i = i → i = i₀)
    (hcount : Fintype.card ι + 1 ≤ 2 * permutationCycleCount π) :
    ∀ q : PermutationCycles π,
      Fintype.card (CycleMembers π q) = if q = ⟦i₀⟧ then 1 else 2 := by
  classical
  have hle (q : PermutationCycles π) :
      (if q = ⟦i₀⟧ then 1 else 2) ≤ Fintype.card (CycleMembers π q) := by
    split_ifs with hq
    · exact cycleLength_pos π q
    · apply two_le_cycleLength
      intro i hi hfix
      have hieq := hfixed i hfix
      subst i
      exact hq hi.symm
  have htotal : (∑ q : PermutationCycles π, if q = ⟦i₀⟧ then 1 else 2) =
      Fintype.card ι := by
    have hs := Finset.sum_le_sum (fun q (_ : q ∈ Finset.univ) => hle q)
    rw [sum_cycleLengths] at hs
    have hb := sum_endpoint_weights (⟦i₀⟧ : PermutationCycles π)
    rw [card_permutationCycles] at hb
    exact Nat.le_antisymm hs (Nat.le_of_add_le_add_right (hcount.trans_eq hb.symm))
  intro q
  apply le_antisymm ?_ (hle q)
  by_contra h
  have hlt := Finset.sum_lt_sum
    (fun q (_ : q ∈ Finset.univ) => hle q)
    ⟨q, Finset.mem_univ q, Nat.lt_of_not_ge h⟩
  rw [sum_cycleLengths, htotal] at hlt
  exact (Nat.lt_irrefl _ hlt)

/-- If all permutation cycles have at most two elements, the permutation is
an involution. This follows by putting three successive vertices in one fiber. -/
theorem involutive_of_cycleLengths_le_two (π : Equiv.Perm ι)
    (hsize : ∀ q : PermutationCycles π, Fintype.card (CycleMembers π q) ≤ 2) :
    Function.Involutive π := by
  intro i
  by_contra hbad
  have heq (i : ι) : (⟦π i⟧ : PermutationCycles π) = ⟦i⟧ :=
    Quotient.sound ((show π.SameCycle i (π i) from ⟨1, by simp⟩).symm)
  let a : CycleMembers π (⟦i⟧ : PermutationCycles π) := ⟨i, rfl⟩
  let b : CycleMembers π (⟦i⟧ : PermutationCycles π) := ⟨π i, heq i⟩
  let c : CycleMembers π (⟦i⟧ : PermutationCycles π) :=
    ⟨π (π i), (heq (π i)).trans (heq i)⟩
  have hcollapse (h : i = π i) : π (π i) = i :=
    (congrArg π h.symm).trans h.symm
  have hab : a ≠ b := fun h => hbad (hcollapse (congrArg Subtype.val h))
  have hac : a ≠ c := fun h => hbad (congrArg Subtype.val h).symm
  have hbc : b ≠ c := fun h =>
    hbad (hcollapse (π.injective (congrArg Subtype.val h)))
  have ht : 2 < Fintype.card (CycleMembers π (⟦i⟧ : PermutationCycles π)) := by
    simpa only [Finset.card_univ] using
      (Finset.two_lt_card_iff.mpr ⟨a, b, c, Finset.mem_univ _, Finset.mem_univ _,
        Finset.mem_univ _, hab, hac, hbc⟩ :
        2 < (Finset.univ : Finset (CycleMembers π (⟦i⟧ : PermutationCycles π))).card)
  exact (not_lt_of_ge (hsize _) ht)

/-- The surviving cycle structures are precisely an endpoint singleton and
a fixed-point-free involution on the tail slots. -/
theorem cycle_threshold_pairing (π : Equiv.Perm ι) (i₀ : ι)
    (hfixed : ∀ i, π i = i → i = i₀)
    (hcount : Fintype.card ι + 1 ≤ 2 * permutationCycleCount π) :
    π i₀ = i₀ ∧ Function.Involutive π ∧ ∀ i, i ≠ i₀ → π i ≠ i := by
  refine ⟨cycle_threshold_fixes_endpoint π i₀ hfixed hcount, ?_, ?_⟩
  · apply involutive_of_cycleLengths_le_two
    intro q
    rw [cycle_threshold_lengths π i₀ hfixed hcount]
    split_ifs <;> omega
  · intro i hne hi
    exact hne (hfixed i hi)

/-- The cycle structure remaining after the endpoint and centering estimates. -/
def EndpointPairing (π : Equiv.Perm ι) (i₀ : ι) : Prop :=
  π i₀ = i₀ ∧ Function.Involutive π ∧ ∀ i, π i = i → i = i₀

instance endpointPairingDecidable (π : Equiv.Perm ι) (i₀ : ι) :
    Decidable (EndpointPairing π i₀) := by
  unfold EndpointPairing Function.Involutive
  infer_instance

/-- Combining coefficient decay with centered-singleton deletion reduces the
finite invariant expansion to pairings of all tail slots. The coefficient
vanishing premise is supplied by the proved matrix-test limit theorem. -/
theorem invariant_expansion_reduce_to_pairings
    (i₀ : ι) (v : ι → Matrix α α ℂ)
    (hcenter : ∀ i, i ≠ i₀ → Matrix.trace (v i) = 0)
    (c : Equiv.Perm ι → ℂ)
    (hsmall : ∀ π, 2 * permutationCycleCount π < Fintype.card ι + 1 → c π = 0) :
    (∑ π, c π * normalizedPermutationContraction π v) =
      ∑ π ∈ Finset.univ.filter (fun π => EndpointPairing π i₀),
        c π * normalizedPermutationContraction π v := by
  classical
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _) ?_
  intro π _ hπ
  by_cases htail : ∀ i, π i = i → i = i₀
  · by_cases hcount : Fintype.card ι + 1 ≤ 2 * permutationCycleCount π
    · obtain ⟨hfix, hinv, _⟩ := cycle_threshold_pairing π i₀ htail hcount
      exact False.elim (hπ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfix, hinv, htail⟩))
    · rw [hsmall π (Nat.lt_of_not_ge hcount), zero_mul]
  · have hex : ∃ i, π i = i ∧ i ≠ i₀ := by
      by_contra hn
      apply htail
      intro i hi
      by_contra hne
      exact hn ⟨i, hi, hne⟩
    obtain ⟨i, hi, hne⟩ := hex
    rw [normalizedPermutationContraction_eq_zero_of_fixed_centered π i hi v (hcenter i hne),
      mul_zero]

/-- Every tail pair joins one source slot to one test slot. -/
def IsCrossPairing {k l : ℕ} (π : Equiv.Perm (Fin k ⊕ Fin l)) : Prop :=
  (∀ i, ∃ j, π (Sum.inl i) = Sum.inr j) ∧
    (∀ j, ∃ i, π (Sum.inr j) = Sum.inl i)

/-- A cross pairing determines the bijection indexing its contraction. -/
def crossPairingEquiv {k l : ℕ} (π : Equiv.Perm (Fin k ⊕ Fin l))
    (hπ : Function.Involutive π) (hcross : IsCrossPairing π) : Fin k ≃ Fin l where
  toFun i := (hcross.1 i).choose
  invFun j := (hcross.2 j).choose
  left_inv i := by
    have h := hπ (Sum.inl i)
    rw [(hcross.1 i).choose_spec, (hcross.2 _).choose_spec] at h
    exact Sum.inl.inj h
  right_inv j := by
    have h := hπ (Sum.inr j)
    rw [(hcross.2 j).choose_spec, (hcross.1 _).choose_spec] at h
    exact Sum.inr.inj h

/-- Cross pairings exist only when the source and test degrees coincide. -/
theorem degrees_eq_of_crossPairing {k l : ℕ} (π : Equiv.Perm (Fin k ⊕ Fin l))
    (hπ : Function.Involutive π) (hcross : IsCrossPairing π) : k = l := by
  simpa using Fintype.card_congr (crossPairingEquiv π hπ hcross)

end KadisonSimilarity

end

end OAI
