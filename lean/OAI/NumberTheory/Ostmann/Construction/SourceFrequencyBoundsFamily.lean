import OAI.NumberTheory.Ostmann.Construction.InitialSourceChoice

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction

def PrimeSource.AboveFrequency (S : PrimeSource) (V : ℕ) : Prop :=
  ∀p : S.Sample,S.law.mass p≠0 → V<(p:ℕ)

theorem initialSourceFamily_aboveFrequency (b k : ℕ) (bulk : PrimeSource)
    (top : Fin 3 → PrimeSource) (comp : Fin k → Fin 2 → PrimeSource) (V : ℕ)
    (hb : bulk.AboveFrequency V) (ht : ∀i,(top i).AboveFrequency V)
    (hc : ∀j i,(comp j i).AboveFrequency V) :
    ∀origin,(initialSourceFamily b k bulk top comp origin).AboveFrequency V := by
  intro origin
  unfold initialSourceFamily initialSourceValue
  split_ifs
  · exact hb
  · exact ht _
  · exact hc _ _
  · exact hb

theorem InitialSourceChoice.sources_aboveFrequency {d : Decomposition} {Bs BD Bz : ℝ}
    {k : ℕ} {L : ℝ} {E : Finset ℕ} (C : InitialSourceChoice d Bs BD Bz k L E) (V : ℕ)
    (hb : C.bulk.AboveFrequency V) (ha : ∀i,(C.auxiliary i).AboveFrequency V) :
    ∀origin,(C.sources origin).AboveFrequency V := by
  apply initialSourceFamily_aboveFrequency
  · exact hb
  · intro i
    exact ha (.inl i)
  · intro j i
    exact ha (.inr (j,i))

theorem sourceMass_value_gt {sources : SourceFamily} {V : ℕ}
    (h : ∀origin,(sources origin).AboveFrequency V) {q : SmallSlot}
    (hq : sourceMass sources q≠0) : V<q.value := by
  unfold sourceMass at hq
  split_ifs at hq with hmem
  · exact h q.origin ⟨q.value,hmem⟩ hq
  · exact (hq rfl).elim

end Ostmann.Construction

end

end OAI
