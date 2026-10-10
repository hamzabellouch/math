import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.OrderedClassLaw

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Selection
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] [Finite K]
  {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem actual_ordered_class {N n : ℕ} (hdim : Module.finrank K V=n+3)
    {gap : ℝ} (hgap : 0≤gap)
    (p : Law Ω) (C : Ω→Γ) (F : Ω→Fin N→ProjectivePair (K:=K) (V:=V))
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
      (S : TwoMessage (K:=K) (V:=V) Γ N→Finset (Fin N)) (hmn : m≤N),
      let θ:=sourceMessage C F
      let p':=p.onContextEvent θ E hE
      let e:=chosenOrder S hmn
      let G:=orderedTuple S hmn θ F
      1/((2*(n+3)+(n+3)^2:ℕ):ℝ)≤(p.map θ).event E ∧
      (∀ z,(p'.map θ).mass z≠0→(S z).card=m) ∧
      (∀ x,p'.mass x≠0→ScanConsistent ((List.ofFn (G x)).map toScan)) ∧
      (∀ x,p'.mass x≠0→∀ i,Incidence.Incident (G x i).1 (G x i).2) ∧
      (∀ x,p'.mass x≠0→∀ i,
        G x i∈cheapBoth (θ x) (e (θ x) i) ∧
        ValidSlotClass (n+2) gap (cheapBoth (θ x) (e (θ x) i)) c) ∧
      (∑ z,(p'.map θ).mass z*((m:ℝ)*jointJ K (n+2)-entropy ((p'.cond θ z).map G)))≤
        excessCost p C F Jprev (jointJ K (n+2))/(p.map θ).event E := by
  obtain ⟨c,E,hE,S,hprob,hdis,hcard,hgeom,hdef⟩ :=
    actual_geometric_class hdim hgap p C F D Jprev hcons hinc hD hprev m hm
  have hEn : E.Nonempty := by
    by_contra he
    rw [not_nonempty_iff_eq_empty.mp he] at hE
    simp only [Law.event,sum_empty,lt_self_iff_false] at hE
  obtain ⟨z,hz⟩ := hEn
  have hmn : m≤N := by
    have hh:=card_le_univ (S z)
    simpa only [Fintype.card_fin,hcard z hz] using hh
  let θ:=sourceMessage C F
  let p':=p.onContextEvent θ E hE
  have hcard' z (hz : (p'.map θ).mass z≠0) : (S z).card=m := by
    apply hcard z
    by_contra hn
    have he:=p.onContextEvent_map_mass θ E hE z
    rw [ite_eq_right hn] at he
    exact hz he
  refine ⟨c,E,hE,S,hmn,hprob,hcard',?_,?_,?_,?_⟩
  · intro x hx
    exact scanConsistent_ordered (F x)
      (hcons x ((p.onContextEvent_support θ E hE x hx).1)) (chosenOrder S hmn (θ x))
  · intro x hx i
    exact hinc x ((p.onContextEvent_support θ E hE x hx).1) _
  · intro x hx i
    obtain ⟨hx,he⟩:=p.onContextEvent_support θ E hE x hx
    exact hgeom x hx he _ (chosenOrder_mem S hmn (θ x) (hcard _ he) i)
  · calc
      _ = selectedDeficit p' θ F S (jointJ K (n+2)) :=
        ordered_deficit p' θ F S hmn hcard' _
      _ ≤ _ := hdef

end
end SharpLogRamsey.Marking

end

end OAI
