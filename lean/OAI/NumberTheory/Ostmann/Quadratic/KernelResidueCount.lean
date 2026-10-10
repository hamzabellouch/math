import OAI.NumberTheory.Ostmann.Quadratic.KernelUnitResidues
import OAI.NumberTheory.Ostmann.Quadratic.RootPopulations

namespace OAI

/-! # Few occupied residues for a fixed quadratic kernel -/

namespace Ostmann

open scoped Classical

theorem unit_square_residue_card_le (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) :
    ((Finset.univ : Finset (ZMod q)).filter
      (fun x => IsUnit x ∧ x ^ 2 = (a : ZMod q))).card ≤
        2 ^ (q.primeFactors.card + 1) := by
  let F := {x : ZMod q // IsUnit x ∧ x ^ 2 = (a : ZMod q)}
  let f : F → {x : (ZMod q)ˣ // x ^ 2 = a} := fun x =>
    ⟨x.property.1.unit, by
      apply Units.ext
      simpa only [Units.val_pow_eq_pow_val, IsUnit.unit_spec] using x.property.2⟩
  have hinj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    have hv := congrArg (fun z : {x : (ZMod q)ˣ // x ^ 2 = a} => (z.val : ZMod q)) h
    simpa only [f, IsUnit.unit_spec] using hv
  have hc := Fintype.card_le_of_injective f hinj
  have hb := unit_square_fiber_card_le q a
  rw [Nat.card_eq_fintype_card] at hb
  exact (show _ ≤ Fintype.card F from by simp [F, Fintype.card_subtype]).trans (hc.trans hb)

theorem kernel_root_residues_card_le (S : Finset ℤ) (root : ℤ → ℕ)
    (m : ℕ) [NeZero m] (h u : ℤ) (hred : h.natAbs.Coprime m)
    (hroot : ∀ x ∈ S, u * (root x : ℤ) ^ 2 = (m : ℤ) * x - h) :
    ((kernelRootPopulation S root).image (fun t : ℕ => (t : ZMod m))).card ≤
      2 ^ (m.primeFactors.card + 1) := by
  by_cases hS : S.Nonempty
  · obtain ⟨a, ha⟩ := kernel_square_residues S root m h u hred hS hroot
    apply (Finset.card_le_card (t := (Finset.univ : Finset (ZMod m)).filter
      (fun r => IsUnit r ∧ r ^ 2 = (a : ZMod m))) ?_).trans (unit_square_residue_card_le m a)
    intro r hr
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (ZMod.isUnit_iff_coprime _ _).mpr (ha x hx).1, (ha x hx).2⟩
  · simp [Finset.not_nonempty_iff_eq_empty.mp hS, kernelRootPopulation]

end Ostmann

end OAI
