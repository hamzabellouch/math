import OAI.NumberTheory.Ostmann.Construction.PrimeGridSupport

namespace OAI

/-! # All unit residues preserve the original selected prime cells -/

namespace Ostmann
open scoped Classical

theorem mem_unitPrimeCellSupport_iff {C : Type*} [Fintype C]
    (q : ℕ) [NeZero q] (u v : C → ℝ) (p : ℕ) :
    p ∈ primeCellSupport q (fun c : C × (ZMod q)ˣ => c.2.val.val)
        (fun c => u c.1) (fun c => v c.1) ↔
      p.Prime ∧ p.Coprime q ∧ ∃ c, Real.log (p : ℝ) ∈ Set.Ioc (u c) (v c) := by
  constructor
  · intro hp
    obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨hprime, hres, hlo, hhi⟩ := mem_primeLogCellSet_iff.mp hc
    have heq := (ZMod.natCast_eq_natCast_iff p c.2.val.val q).mpr hres
    simp only [ZMod.natCast_zmod_val] at heq
    have hcop : p.Coprime q := (ZMod.isUnit_iff_coprime p q).mp (by
      rw [heq]
      exact c.2.isUnit)
    exact ⟨hprime, hcop, c.1, hlo, hhi⟩
  · rintro ⟨hprime, hcop, c, hlog⟩
    let z := ZMod.unitOfCoprime p hcop
    apply Finset.mem_biUnion.mpr
    refine ⟨(c, z), Finset.mem_univ _, mem_primeLogCellSet_iff.mpr ⟨hprime, ?_, hlog⟩⟩
    apply (ZMod.natCast_eq_natCast_iff p z.val.val q).mp
    simp [z]

/-- A modulus below every lower endpoint removes no original prime atom. -/
theorem unitPrimeCellSupport_eq {C : Type*} [Fintype C]
    (q : ℕ) [NeZero q] (u v : C → ℝ) (hq : ∀ c, (q : ℝ) ≤ Real.exp (u c)) :
    primeCellSupport q (fun c : C × (ZMod q)ˣ => c.2.val.val)
      (fun c => u c.1) (fun c => v c.1) = primeCellSupport 1 (fun _ : C => 0) u v := by
  ext p
  rw [mem_unitPrimeCellSupport_iff]
  constructor
  · rintro ⟨hp, _, c, hlog⟩
    exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _,
      mem_primeLogCellSet_iff.mpr ⟨hp, by simp only [Nat.ModEq, Nat.mod_one], hlog⟩⟩
  · intro hp
    obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨hp, _, hlog⟩ := mem_primeLogCellSet_iff.mp hc
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hqp : q < p := by
      exact_mod_cast (hq c).trans_lt ((Real.lt_log_iff_exp_lt hp0).mp hlog.1)
    exact ⟨hp, hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (NeZero.pos q) hqp), c, hlog⟩

theorem unitPrimeCellLabel_lift {C : Type*} [Fintype C]
    (q : ℕ) [NeZero q] (u v : C → ℝ) (c₀ : C × (ZMod q)ˣ) (p : ℕ)
    (hp : p ∈ primeCellSupport q (fun c : C × (ZMod q)ˣ => c.2.val.val)
      (fun c => u c.1) (fun c => v c.1)) :
    (p : ZMod q) = ((primeCellLabel q (fun c : C × (ZMod q)ˣ => c.2.val.val)
      (fun c => u c.1) (fun c => v c.1) c₀ p).2 : ZMod q) := by
  have hc := primeCellLabel_mem q (fun c : C × (ZMod q)ˣ => c.2.val.val)
    (fun c => u c.1) (fun c => v c.1) c₀ p hp
  have he := (ZMod.natCast_eq_natCast_iff _ _ q).mpr (mem_primeLogCellSet_iff.mp hc).2.1
  simpa only [ZMod.natCast_zmod_val] using he

/-- Disjoint real cells and distinct unit residues give the required actual
prime partition, independently of prime-distribution estimates. -/
theorem unitPrimeCells_separated {C : Type*} [Fintype C]
    (q : ℕ) [NeZero q] (u v : C → ℝ)
    (hsep : ∀ c d, c ≠ d → v c ≤ u d ∨ v d ≤ u c) :
    ∀ c d : C × (ZMod q)ˣ, c ≠ d →
      ¬Nat.ModEq q c.2.val.val d.2.val.val ∨ v c.1 ≤ u d.1 ∨ v d.1 ≤ u c.1 := by
  intro c d hcd
  by_cases hfirst : c.1 = d.1
  · left
    intro hres
    apply hcd
    apply Prod.ext hfirst
    apply Units.ext
    have he := (ZMod.natCast_eq_natCast_iff _ _ q).mpr hres
    simpa only [ZMod.natCast_zmod_val] using he
  · exact Or.inr (hsep c.1 d.1 hfirst)

end Ostmann

end OAI
