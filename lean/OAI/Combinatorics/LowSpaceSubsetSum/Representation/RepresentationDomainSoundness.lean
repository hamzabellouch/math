import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationProgram

namespace OAI

/-! # One-sided soundness of the arbitrary-input representation runtime -/

noncomputable section

namespace LowSpaceSubsetSum

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

theorem rawLeaf_background_subset_outside (z : Layout n) (g : Guesses n)
    (f : R.Partitions z) (B : Fin n → Fin 2 × Fin 4) (j : Fin 2) :
    RepresentationUniverse.backgroundDomain (R.rawLeaf z g f B j) ⊆
      Finset.univ \ R.mixerUnion z := by
  change ((R.rawBackground z B j 0 ∪ R.rawBackground z B j 1) ∪
    R.rawBackground z B j 2) ∪ R.rawBackground z B j 3 ⊆ _
  repeat' apply Finset.union_subset
  all_goals exact Finset.filter_subset _ _

theorem rawLeaf_background_color (z : Layout n) (g : Guesses n)
    (f : R.Partitions z) (B : Fin n → Fin 2 × Fin 4) (j : Fin 2) (x : Fin n)
    (hx : x ∈ RepresentationUniverse.backgroundDomain (R.rawLeaf z g f B j)) :
    (B x).1 = j := by
  change x ∈ ((R.rawBackground z B j 0 ∪ R.rawBackground z B j 1) ∪
    R.rawBackground z B j 2) ∪ R.rawBackground z B j 3 at hx
  simp only [Finset.mem_union] at hx
  rcases hx with ((hx | hx) | hx) | hx
  all_goals exact congrArg Prod.fst (Finset.mem_filter.mp hx).2

theorem rawLeaf_background_sides_disjoint (z : Layout n) (g : Guesses n)
    (f : R.Partitions z) (B : Fin n → Fin 2 × Fin 4) :
    Disjoint (RepresentationUniverse.backgroundDomain (R.rawLeaf z g f B 0))
      (RepresentationUniverse.backgroundDomain (R.rawLeaf z g f B 1)) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have h0 := R.rawLeaf_background_color z g f B 0 x hx
  have h1 := R.rawLeaf_background_color z g f B 1 x hy
  have h : (0 : Fin 2) = 1 := h0.symm.trans h1
  exact (by decide : (0 : Fin 2) ≠ 1) h

/-- Only top-domain indices can be shared by the left and right parents. -/
theorem raw_parentDomain_shared (z : Layout n) (g : Guesses n)
    (f : R.Partitions z) (B : Fin n → Fin 2 × Fin 4) :
    RepresentationUniverse.parentDomain (R.rawLeaf z g f B 0) ∩
      RepresentationUniverse.parentDomain (R.rawLeaf z g f B 1) ⊆
        R.orderedMixers z 0 := by
  have hbg := R.rawLeaf_background_sides_disjoint z g f B
  have hb0 := R.rawLeaf_background_subset_outside z g f B 0
  have hb1 := R.rawLeaf_background_subset_outside z g f B 1
  have hm1 := R.mixer_disjoint_rawOutside z 1
  have hm2 := R.mixer_disjoint_rawOutside z 2
  have hm12 := R.orderedMixers_disjoint z (by decide : (1 : Fin 3) ≠ 2)
  intro x hx
  obtain ⟨hx, hy⟩ := Finset.mem_inter.mp hx
  simp only [RepresentationUniverse.parentDomain, R.rawLeaf_topDomain,
    R.rawLeaf_mixerDomain, Finset.mem_union] at hx hy
  rcases hx with (ht | hm) | hb
  · exact ht
  · rcases hy with (ht | hm') | hb'
    · exact ht
    · exact (Finset.disjoint_left.mp hm12 hm hm').elim
    · exact (Finset.disjoint_left.mp hm1 hm (hb1 hb')).elim
  · rcases hy with (ht | hm') | hb'
    · exact ht
    · exact (Finset.disjoint_left.mp hm2 hm' (hb0 hb)).elim
    · exact (Finset.disjoint_left.mp hbg hb hb').elim

end RepresentationSetup

theorem representation_capacity_pair_le (n : ℕ) (hn : 10 ≤ n) :
    compressionDictionaryCapacity n + 1 + (compressionDictionaryCapacity n + 1) ≤ 2 ^ n := by
  have hC : 0 < compressionDictionaryCapacity n := by
    unfold compressionDictionaryCapacity
    positivity
  have hk : 199 * n / 1000 + 2 ≤ n := by omega
  have hp : 4 * compressionDictionaryCapacity n ≤ 2 ^ n := by
    calc
      _ = 2 ^ (199 * n / 1000 + 2) := by
        rw [pow_add]
        unfold compressionDictionaryCapacity
        ring
      _ ≤ _ := Nat.pow_le_pow_right (by decide : 0 < 2) hk
  omega

namespace RepresentationData

variable {n : ℕ} (D : RepresentationData n)

/-- Every accepting random history yields an indexed solution, for an
arbitrary input and without any survival, resource or sampling assumptions. -/
theorem trial_sound (h : D.zeroSetup.PrimeHistory) (r : D.zeroSetup.Residues h.2)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (q : ℕ) (hq : 0 < q) (B : ℕ)
    (families : Fin 4 → Array (Finset (Fin (2 * RepresentationSetup.blockHalf n 0))))
    (hyes : D.trial h r hn hlog q hq B families = true) : Solvable D.input := by
  let R := D.zeroSetup
  let z := h.1.1.1
  let g := h.1.1.2
  let f := h.1.2
  let bg := R.allocatedBackground z g hn hlog
  apply (D.scheduleData h r hn hlog q hq).run_sound B families
      (fun j => (R.rawLeaf_topDomain z g f bg j).trans (R.topCoordinates_domain z f).symm)
      (fun j => (R.rawLeaf_domains_disjoint z g f bg j).1)
      (fun j => (R.rawLeaf_domains_disjoint z g f bg j).2.1)
      (fun j => (R.rawLeaf_domains_disjoint z g f bg j).2.2)
      ?_ (representation_capacity_pair_le n (by omega)) hyes
  change RepresentationUniverse.parentDomain (R.rawLeaf z g f bg 0) ∩
    RepresentationUniverse.parentDomain (R.rawLeaf z g f bg 1) ⊆
      (R.topCoordinates z f).domain
  rw [R.topCoordinates_domain]
  exact R.raw_parentDomain_shared z g f bg

end RepresentationData
end LowSpaceSubsetSum

end

end OAI
