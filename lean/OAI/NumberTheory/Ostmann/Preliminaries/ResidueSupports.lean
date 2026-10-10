import OAI.NumberTheory.Ostmann.Setup

namespace OAI

namespace Ostmann.Decomposition

noncomputable def residueSupport (d : Decomposition) (p : ℕ) [NeZero p] :
    Finset (ZMod p) := by
  classical
  exact Finset.univ.filter (fun x => ∃ a ∈ d.A, p + d.cutoff < a ∧ (a : ZMod p) = x)

noncomputable def negResidueSupport (d : Decomposition) (p : ℕ) [NeZero p] :
    Finset (ZMod p) := by
  classical
  exact Finset.univ.filter (fun x => ∃ b ∈ d.B, p + d.cutoff < b ∧ -(b : ZMod p) = x)

@[simp] theorem mem_residueSupport (d : Decomposition) (p : ℕ) [NeZero p]
    (x : ZMod p) : x ∈ d.residueSupport p ↔
    ∃ a ∈ d.A, p + d.cutoff < a ∧ (a : ZMod p) = x := by
  classical
  simp [residueSupport]

@[simp] theorem mem_negResidueSupport (d : Decomposition) (p : ℕ) [NeZero p]
    (x : ZMod p) : x ∈ d.negResidueSupport p ↔
    ∃ b ∈ d.B, p + d.cutoff < b ∧ -(b : ZMod p) = x := by
  classical
  simp [negResidueSupport]

theorem residue_ne_neg (d : Decomposition) {p a b : ℕ} (hp : p.Prime)
    (ha : a ∈ d.A) (hb : b ∈ d.B) (hlarge : p + d.cutoff < a) :
    (a : ZMod p) ≠ -(b : ZMod p) := by
  intro heq
  have hsum := d.sum_prime ha hb (by omega)
  have hzero : ((a + b : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_add, heq, neg_add_cancel]
  have hdvd := (ZMod.natCast_eq_zero_iff (a + b) p).mp hzero
  have hpeq := (Nat.prime_dvd_prime_iff_eq hp hsum).mp hdvd
  omega

theorem residueSupport_disjoint (d : Decomposition) (p : ℕ) [NeZero p]
    (hp : p.Prime) : Disjoint (d.residueSupport p) (d.negResidueSupport p) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨a, ha, hlarge, hax⟩ := (d.mem_residueSupport p x).mp hx
  obtain ⟨b, hb, _, hbx⟩ := (d.mem_negResidueSupport p x).mp hy
  exact d.residue_ne_neg hp ha hb hlarge (hax.trans hbx.symm)

theorem residueSupport_nonempty (d : Decomposition) (p : ℕ) [NeZero p] :
    (d.residueSupport p).Nonempty := by
  obtain ⟨a, ha, hlarge⟩ := d.infinite_A.exists_gt (p + d.cutoff)
  exact ⟨(a : ZMod p), (d.mem_residueSupport p _).mpr ⟨a, ha, hlarge, rfl⟩⟩

theorem negResidueSupport_nonempty (d : Decomposition) (p : ℕ) [NeZero p] :
    (d.negResidueSupport p).Nonempty := by
  obtain ⟨b, hb, hlarge⟩ := d.infinite_B.exists_gt (p + d.cutoff)
  exact ⟨-(b : ZMod p), (d.mem_negResidueSupport p _).mpr ⟨b, hb, hlarge, rfl⟩⟩

theorem negResidueSupport_subset_compl (d : Decomposition) (p : ℕ) [NeZero p]
    (hp : p.Prime) : d.negResidueSupport p ⊆ (d.residueSupport p)ᶜ := by
  classical
  intro x hx
  exact Finset.mem_compl.mpr (fun ha => Finset.disjoint_left.mp
    (d.residueSupport_disjoint p hp) ha hx)

theorem residueSupport_compl_nonempty (d : Decomposition) (p : ℕ) [NeZero p]
    (hp : p.Prime) : ((d.residueSupport p)ᶜ).Nonempty :=
  (d.negResidueSupport_nonempty p).mono (d.negResidueSupport_subset_compl p hp)

noncomputable def residueDensity (d : Decomposition) (p : ℕ) [NeZero p] : ℝ :=
  (d.residueSupport p).card / (p : ℝ)

theorem residueSupport_card_pos (d : Decomposition) (p : ℕ) [NeZero p] :
    0 < (d.residueSupport p).card := Finset.card_pos.mpr (d.residueSupport_nonempty p)

theorem residueSupport_card_lt (d : Decomposition) (p : ℕ) [NeZero p]
    (hp : p.Prime) : (d.residueSupport p).card < p := by
  have hpos := Finset.card_pos.mpr (d.residueSupport_compl_nonempty p hp)
  have hcard := Finset.card_add_card_compl (d.residueSupport p)
  rw [ZMod.card p] at hcard
  omega

theorem residueDensity_pos (d : Decomposition) (p : ℕ) [NeZero p]
    (hp : p.Prime) : 0 < d.residueDensity p := by
  exact div_pos (by exact_mod_cast d.residueSupport_card_pos p) (by exact_mod_cast hp.pos)

theorem residueDensity_lt_one (d : Decomposition) (p : ℕ) [NeZero p]
    (hp : p.Prime) : d.residueDensity p < 1 := by
  rw [residueDensity, div_lt_one (by exact_mod_cast hp.pos : (0 : ℝ) < p)]
  exact_mod_cast d.residueSupport_card_lt p hp

end Ostmann.Decomposition

end OAI
