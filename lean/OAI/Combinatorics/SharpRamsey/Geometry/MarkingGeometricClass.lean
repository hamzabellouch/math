import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.MarkingClassSelection
import OAI.Combinatorics.SharpRamsey.Marking.MarkingFiniteClasses

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset
open scoped BigOperators Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] [Finite K]
  {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

omit [Finite K] in

lemma cheapBoth_nonempty_of_mass {N : ℕ}
    (p : Selection.Law Ω) (C : Ω→Γ) (F : Ω→Fin N→ProjectivePair (K:=K) (V:=V))
    (hcons : ∀ x,p.mass x≠0→ScanConsistent ((List.ofFn (F x)).map toScan))
    (hinc : ∀ x,p.mass x≠0→∀ i,Incidence.Incident (F x i).1 (F x i).2)
    (z : TwoMessage (K:=K) (V:=V) Γ N)
    (hz : (p.map (sourceMessage C F)).mass z≠0) (i : Fin N)
    (hi : i∉bothExpensive z.2.2) : (cheapBoth z i).Nonempty := by
  obtain ⟨x,hx,rfl⟩ := p.map_support (sourceMessage C F) z hz
  exact ⟨F x i,cheapBoth_mem C F x (hcons x hx) (hinc x hx) i hi⟩

theorem actual_geometric_class {N n : ℕ} (hdim : Module.finrank K V=n+3)
    {gap : ℝ} (hgap : 0≤gap)
    (p : Selection.Law Ω) (C : Ω→Γ) (F : Ω→Fin N→ProjectivePair (K:=K) (V:=V))
    (D : Γ→Fin N→Finset (ProjectivePair (K:=K) (V:=V))) (Jprev : ℝ)
    (hcons : ∀ x,p.mass x≠0→ScanConsistent ((List.ofFn (F x)).map toScan))
    (hinc : ∀ x,p.mass x≠0→∀ i,Incidence.Incident (F x i).1 (F x i).2)
    (hD : ∀ x,p.mass x≠0→∀ i,F x i∈D (C x) i)
    (hprev : ∀ c i,Real.log (D c i).card≤Jprev)
    (m : ℕ)
    (hm : ((2*(n+3)+(n+3)^2)*m:ℕ)+expensiveBudget K V+
      expensiveBudget K (Module.Dual K V)≤(N:ℝ)) :
    ∃ (c : SlotClass (n+2)) (E : Finset (TwoMessage (K:=K) (V:=V) Γ N))
      (hE : 0<(p.map (sourceMessage C F)).event E)
      (S : TwoMessage (K:=K) (V:=V) Γ N→Finset (Fin N)),
      1/((2*(n+3)+(n+3)^2:ℕ):ℝ)≤(p.map (sourceMessage C F)).event E ∧
      (∀ z,Disjoint (S z) (bothExpensive z.2.2)) ∧
      (∀ z∈E,(S z).card=m) ∧
      (∀ x,p.mass x≠0→sourceMessage C F x∈E→∀ i∈S (sourceMessage C F x),
        F x i∈cheapBoth (sourceMessage C F x) i ∧
        ValidSlotClass (n+2) gap (cheapBoth (sourceMessage C F x) i) c) ∧
      conditionedDeficit p C F E hE S (jointJ K (n+2)) ≤
        excessCost p C F Jprev (jointJ K (n+2))/(p.map (sourceMessage C F)).event E := by
  have hcard : Fintype.card (SlotClass (n+2))=2*(n+3)+(n+3)^2 := by
    simpa only [Nat.add_assoc] using slotClass_card (n+2)
  obtain ⟨c,E,hE,S,hprob,hS,hslots,hdef⟩ :=
    actual_common_class hdim p C F D Jprev hcons hinc hD hprev
      (messageClass hdim hgap) m (by simpa only [hcard] using hm)
  refine ⟨c,E,hE,S,?_,hS,(fun z hz=>(hslots z hz).1),?_,hdef⟩
  · simpa only [hcard] using hprob
  · intro x hx he i hi
    have hm := cheapBoth_mem C F x (hcons x hx) (hinc x hx) i
      (disjoint_left.mp (hS (sourceMessage C F x)) hi)
    refine ⟨hm,?_⟩
    have hc := messageClass_valid hdim hgap (sourceMessage C F x) i ⟨F x i,hm⟩
    rwa [(hslots _ he).2 i hi] at hc

end
end SharpLogRamsey.Marking

end

end OAI
