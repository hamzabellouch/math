import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesTests

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedResidues
open Construction HistorySignedDecode HistorySignedSupportReduction

theorem integralGuard_iff_of_congruent {N : ℤ} {l : ℕ} {h k : SignedHistory l}
    (hc : Congruent N h k) (hn : Covers N h) : h.IntegralGuard ↔ k.IntegralGuard := by
  induction h with
  | leaf a => cases k; rfl
  | node a p u hp hm left right il ir =>
    cases k with
    | node b q v kp km left' right' =>
      rcases hc with ⟨hab,hpq,rfl,rfl,rfl,hl,hr⟩
      have hnum : reversalNumerator left.root.frequency right.root.frequency
          (a.giantPlus*((hp.map SmallSlot.value).prod:ℤ))
          (a.giantMinus*((hm.map SmallSlot.value).prod:ℤ)) ≡
          reversalNumerator left.root.frequency right.root.frequency
          (b.giantPlus*((hp.map SmallSlot.value).prod:ℤ))
          (b.giantMinus*((hm.map SmallSlot.value).prod:ℤ)) [ZMOD N] :=
        ((hab.2.2.2.mul_right _).mul_left _).sub ((hab.2.2.1.mul_right _).mul_left _)
      simp only [SignedHistory.IntegralGuard,←hab.1,←hl.root.1,←hr.root.1]
      exact and_congr Iff.rfl (and_congr ((hnum.of_dvd hn.2.2.1).dvd_iff)
        (and_congr (il hl hn.2.2.2.2.1) (ir hr hn.2.2.2.2.2)))

theorem arithmeticGuards_iff_of_congruent {N : ℤ} {l : ℕ}
    (V : ℕ → ℕ) (outside : List ℕ) (hout : ∀q∈outside,(q:ℤ) ∣ N)
    {h k : SignedHistory l} (hc : Congruent N h k) (hn : Covers N h) :
    ArithmeticGuards V outside h ↔ ArithmeticGuards V outside k := by
  induction h with
  | leaf a =>
    cases k
    simpa only [ArithmeticGuards,and_true] using rootArithmetic_iff_of_congruent V hc hn
  | node a p u hp hm left right il ir =>
    cases k with
    | node b q v kp km left' right' =>
      have hroot := rootArithmetic_iff_of_congruent V hc hn
      rcases hc with ⟨hab,hpq,rfl,rfl,rfl,hl,hr⟩
      rw [ArithmeticGuards,ArithmeticGuards]
      apply and_congr hroot
      have hlocal := localArithmetic_iff_of_congruent outside hout a b p q u hp hm
        left.root.frequency right.root.frequency hab hpq hn.2.2.2.1
      have hlocal' : LocalArithmetic outside a p u hp hm left.root.frequency right.root.frequency ↔
          LocalArithmetic outside b q u hp hm left'.root.frequency right'.root.frequency := by
        simpa only [←hl.root.1,←hr.root.1] using hlocal
      exact and_congr hlocal' (and_congr (il hl hn.2.2.2.2.1) (ir hr hn.2.2.2.2.2))

theorem residueRootCoprime_iff_of_congruent {N : ℤ} (outside : List ℕ)
    (hout : ∀q∈outside,(q:ℤ) ∣ N) (a b : SignedState) (hc : StateCongruent N a b)
    (hsmall : ∀q∈a.small,(q.value:ℤ) ∣ N) :
    ResidueRootCoprime outside a ↔ ResidueRootCoprime outside b := by
  simp only [ResidueRootCoprime,←hc.2.1]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro q
  apply forall_congr'
  intro hq
  have hd : (q:ℤ) ∣ N := by
    rcases List.mem_append.mp hq with hq | hq
    · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq
      exact hsmall r hr
    · exact hout q hq
  exact and_congr (nat_coprime_iff_of_modEq (hc.2.2.1.of_dvd hd))
    (nat_coprime_iff_of_modEq (hc.2.2.2.of_dvd hd))

theorem residueGuarded_iff_of_congruent {N : ℤ} {l : ℕ}
    (V : ℕ → ℕ) (outside : List ℕ) (hout : ∀q∈outside,(q:ℤ) ∣ N)
    {h k : SignedHistory l} (hc : Congruent N h k) (hn : Covers N h) :
    ResidueGuarded V outside h ↔ ResidueGuarded V outside k := by
  have hsmall : ∀q∈h.root.small,(q.value:ℤ) ∣ N := by cases h <;> exact hn.2.1
  exact and_congr (residueRootCoprime_iff_of_congruent outside hout _ _ hc.root hsmall)
    (and_congr (integralGuard_iff_of_congruent hc hn)
      (arithmeticGuards_iff_of_congruent V outside hout hc hn))

end Ostmann.Arithmetic.HistorySignedResidues

end

end OAI
