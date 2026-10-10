import OAI.NumberTheory.Ostmann.Preliminaries.PrimeBlockFourier
import OAI.NumberTheory.Ostmann.Preliminaries.ResidueSupports

namespace OAI

namespace Ostmann.Preliminaries
open scoped BigOperators

noncomputable def allResidues (S : Set ℕ) (p : ℕ) [NeZero p] : Finset (ZMod p) := by
  classical
  exact Finset.univ.filter (fun r => ∃ n ∈ S, (n : ZMod p) = r)

@[simp] theorem mem_allResidues (S : Set ℕ) (p : ℕ) [NeZero p] (r : ZMod p) :
    r ∈ allResidues S p ↔ ∃ n ∈ S, (n : ZMod p) = r := by
  classical
  simp [allResidues]

noncomputable def allResidueCount (S : Set ℕ) (p : ℕ) : ℕ :=
  Nat.card {r : ZMod p // ∃ n ∈ S, (n : ZMod p) = r}

theorem allResidueCount_eq_card (S : Set ℕ) (p : ℕ) [NeZero p] :
    allResidueCount S p = (allResidues S p).card := by
  classical
  simp only [allResidueCount, Nat.card_eq_fintype_card, allResidues]
  exact Fintype.card_subtype _

theorem allResidueCount_pos (S : Set ℕ) (hS : S.Nonempty) (p : ℕ) [NeZero p] :
    0 < allResidueCount S p := by
  rw [allResidueCount_eq_card]
  apply Finset.card_pos.mpr
  obtain ⟨n, hn⟩ := hS
  exact ⟨(n : ZMod p), (mem_allResidues S p _).mpr ⟨n, hn, rfl⟩⟩

noncomputable def residueReciprocalSum (S : Set ℕ) (Q : ℕ) : ℝ :=
  ∑ p ∈ Q.primesLE, Real.log p / allResidueCount S p

theorem avoids_all_neg_residues (d : Decomposition) (p a : ℕ) [NeZero p]
    (hp : p.Prime) (ha : a ∈ d.A) (hlarge : p + d.cutoff < a) :
    (a : ZMod p) ∈ ((allResidues d.B p).image Neg.neg)ᶜ := by
  classical
  apply Finset.mem_compl.mpr
  intro h
  obtain ⟨r, hr, heq⟩ := Finset.mem_image.mp h
  obtain ⟨b, hb, hbr⟩ := (mem_allResidues d.B p r).mp hr
  exact d.residue_ne_neg hp ha hb hlarge (heq.symm.trans (congrArg Neg.neg hbr.symm))

theorem actual_prime_nonzero_energy_lower (d : Decomposition) (U : Finset ℕ)
    (hU : U.Nonempty) (p : ℕ) [NeZero p] (hp : p.Prime)
    (hA : ∀ a ∈ U, a ∈ d.A) (hlarge : ∀ a ∈ U, p + d.cutoff < a) :
    (allResidueCount d.B p : ℝ) / p ≤
      ∑ a ∈ (Finset.univ : Finset (ZMod p)).erase 0,
        ‖Ostmann.normalizedExpSum U ((a.val : ℝ) / p)‖ ^ 2 := by
  classical
  let S : Finset (ZMod p) := ((allResidues d.B p).image Neg.neg)ᶜ
  have hmem : ∀ a : U, (a.val : ZMod p) ∈ S := fun a =>
    avoids_all_neg_residues d p a.val hp (hA a.val a.property) (hlarge a.val a.property)
  have hS : S.Nonempty := by
    obtain ⟨a, ha⟩ := hU
    exact ⟨(a : ZMod p), hmem ⟨a, ha⟩⟩
  have hsupp : ∀ r ∉ S, uniformResidueMass U p r = 0 := by
    intro r hr
    exact projectedMass_eq_zero _ _ S (fun a _ => hmem a) hr
  have hc : (p : ℝ) - S.card = allResidueCount d.B p := by
    have h := Finset.card_add_card_compl ((allResidues d.B p).image Neg.neg)
    rw [Finset.card_image_of_injective _ neg_injective, ZMod.card p,
      ← allResidueCount_eq_card] at h
    have hr : (allResidueCount d.B p : ℝ) + S.card = p := by exact_mod_cast h
    linarith
  have h := nonzero_energy_ge_forbidden p S hS (uniformResidueMass U p)
    (uniformResidueMass_sum U hU p) hsupp
  rw [hc] at h
  simpa only [dft_uniformResidueMass] using h

end Ostmann.Preliminaries

end OAI
