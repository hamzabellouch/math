import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.ClassSelection

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

def expensiveBudget (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype (Projectivization K V)] : ℝ :=
  32*(Module.finrank K V+1)^2*(Nat.card K:ℝ)*
    Real.log (Fintype.card (Points (K:=K) (V:=V))+1:ℝ)

omit [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma two_expensive_bound {N : ℕ} (F : Fin N→ProjectivePair (K:=K) (V:=V)) :
    ((bothExpensive (twoMask (Nat.card K) F)).card:ℝ)≤
      expensiveBudget K V+expensiveBudget K (Module.Dual K V) := by
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
  have h₁ := scan_expensive_bound (Nat.card K:ℝ) hq (fun _=>⊥) ((List.ofFn F).map toScan)
  have h₂ := scan_expensive_bound (Nat.card K:ℝ) hq (fun _=>⊥)
    ((List.ofFn (reversedPairs F)).map toScan)
  have h := bothExpensive_card (Nat.card K) F
  have h' : ((bothExpensive (twoMask (Nat.card K) F)).card:ℝ)≤
      (expensiveMask (tupleMask (Nat.card K) F)).card+
      (expensiveMask (tupleMask (Nat.card K) (reversedPairs F))).card := by exact_mod_cast h
  rw [expensiveMask_card,expensiveMask_card] at h'
  exact h'.trans (add_le_add h₁ h₂)

variable {Ω Γ κ : Type*} [Fintype Ω] [Fintype Γ] [Fintype κ] [Nonempty κ]

omit [Fintype κ] [Nonempty κ] in
lemma twoScan_subset_pointwise {N n : ℕ} (hdim : Module.finrank K V=n+3)
    (p : Selection.Law Ω) (C : Ω→Γ) (F : Ω→Fin N→ProjectivePair (K:=K) (V:=V))
    (hcons : ∀ x,p.mass x≠0→ScanConsistent ((List.ofFn (F x)).map toScan))
    (hinc : ∀ x,p.mass x≠0→∀ i,Incidence.Incident (F x i).1 (F x i).2)
    (z : TwoMessage (K:=K) (V:=V) Γ N)
    (hz : (p.map (sourceMessage C F)).mass z≠0)
    (S : Finset (Fin N)) (hS : Disjoint S (bothExpensive z.2.2)) :
    0≤S.card*jointJ K (n+2)-Selection.entropy
      (((p.cond (sourceMessage C F) z).map F).restrict S) := by
  let θ := sourceMessage C F
  let ν := (p.cond θ z).map F
  have hcoord (i : S) : Selection.entropy ((ν.restrict S).marginal i) ≤ jointJ K (n+2) := by
    rw [Selection.Law.marginal_restrict]
    have hs : Selection.entropy (ν.marginal (i:Fin N)) ≤
        Real.log (cheapBoth z i).card := by
      change Selection.entropy (((p.cond θ z).map F).map (fun f=>f i)) ≤ _
      rw [Selection.Law.map_map]
      apply Selection.entropy_mapped_support
      intro x hx
      obtain ⟨hx,he⟩ := p.cond_support θ z hz x hx
      have hi : (i:Fin N)∉bothExpensive (twoMask (Nat.card K) (F x)) := by
        have he' : twoMask (Nat.card K) (F x)=z.2.2 := congrArg (fun z=>z.2.2) he
        rw [he']
        exact disjoint_left.mp hS i.property
      have hh := cheapBoth_mem C F x (hcons x hx) (hinc x hx) i hi
      simpa only [Function.comp_apply,←he,θ,sourceMessage] using hh
    exact hs.trans (cheapBoth_log_card hdim z i)
  have hh := (Selection.entropy_subadditive_pi (ν.restrict S)).trans
    (sum_le_sum (fun i _=>hcoord i))
  have he : (∑ _ : S,jointJ K (n+2))=S.card*jointJ K (n+2) := by simp
  rw [he] at hh
  exact sub_nonneg.mpr hh

omit [Fintype κ] [Nonempty κ] in

def conditionedDeficit {N : ℕ} (p : Selection.Law Ω) (C : Ω→Γ)
    (F : Ω→Fin N→ProjectivePair (K:=K) (V:=V))
    (E : Finset (TwoMessage (K:=K) (V:=V) Γ N))
    (hE : 0<(p.map (sourceMessage C F)).event E)
    (S : TwoMessage (K:=K) (V:=V) Γ N→Finset (Fin N)) (J : ℝ) : ℝ :=
  Selection.selectedDeficit (p.onContextEvent (sourceMessage C F) E hE)
    (sourceMessage C F) F S J

omit [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
theorem actual_common_class_slots {N : ℕ}
    (p : Selection.Law Ω) (C : Ω→Γ) (F : Ω→Fin N→ProjectivePair (K:=K) (V:=V))
    (colour : TwoMessage (K:=K) (V:=V) Γ N→Fin N→κ) (m : ℕ)
    (hm : (Fintype.card κ*m:ℕ)+expensiveBudget K V+
      expensiveBudget K (Module.Dual K V)≤(N:ℝ)) :
    ∃ (c : κ) (E : Finset (TwoMessage (K:=K) (V:=V) Γ N))
      (_hE : 0<(p.map (sourceMessage C F)).event E)
      (S : TwoMessage (K:=K) (V:=V) Γ N→Finset (Fin N)),
      1/(Fintype.card κ:ℝ)≤(p.map (sourceMessage C F)).event E ∧
      (∀ z,Disjoint (S z) (bothExpensive z.2.2)) ∧
      (∀ z∈E,(S z).card=m ∧ ∀ i∈S z,colour z i=c) := by

  let θ:=sourceMessage C F
  let U:=fun z : TwoMessage (K:=K) (V:=V) Γ N=>(bothExpensive z.2.2)ᶜ
  have hcount x (_hx : p.mass x≠0) : Fintype.card κ*m≤(U (θ x)).card := by
    have hb := two_expensive_bound (F x)
    have hc : ((U (θ x)).card:ℝ)=(N:ℝ)-(bothExpensive (twoMask (Nat.card K) (F x))).card := by
      simp only [U,θ,sourceMessage,Selection.markingMessage,card_compl,
        Fintype.card_fin]
      rw [Nat.cast_sub (by simpa only [Fintype.card_fin] using
        (card_le_univ (bothExpensive (twoMask (Nat.card K) (F x)))))]
    have hh : (Fintype.card κ*m:ℕ)≤((U (θ x)).card:ℝ) := by rw [hc]; linarith
    exact_mod_cast hh
  obtain ⟨c,E,S,hprob,hslots⟩ := Selection.common_class_extraction p θ U colour m hcount
  have hp : 0<(p.map θ).event E := lt_of_lt_of_le (one_div_pos.mpr (by
    exact_mod_cast (Fintype.card_pos (α:=κ)))) hprob
  let S' := fun z=>if z∈E then S z else ∅
  have hS z : Disjoint (S' z) (bothExpensive z.2.2) := by
    by_cases hz : z∈E
    · simp only [S',ite_eq_left hz]
      apply disjoint_left.mpr
      intro i hi hie
      exact (mem_compl.mp ((hslots z hz).2.1 hi)) hie
    · simp [S',hz]
  refine ⟨c,E,hp,S',hprob,hS,?_⟩
  intro z hz
  simpa only [S',ite_eq_left hz] using ⟨(hslots z hz).1,(hslots z hz).2.2⟩

omit [Fintype κ] [Nonempty κ] in

theorem twoScan_conditioned_deficit {N n : ℕ} (hdim : Module.finrank K V=n+3)
    (p : Selection.Law Ω) (C : Ω→Γ) (F : Ω→Fin N→ProjectivePair (K:=K) (V:=V))
    (D : Γ→Fin N→Finset (ProjectivePair (K:=K) (V:=V))) (Jprev : ℝ)
    (hcons : ∀ x,p.mass x≠0→ScanConsistent ((List.ofFn (F x)).map toScan))
    (hinc : ∀ x,p.mass x≠0→∀ i,Incidence.Incident (F x i).1 (F x i).2)
    (hD : ∀ x,p.mass x≠0→∀ i,F x i∈D (C x) i)
    (hprev : ∀ c i,Real.log (D c i).card≤Jprev)
    (E : Finset (TwoMessage (K:=K) (V:=V) Γ N))
    (hp : 0<(p.map (sourceMessage C F)).event E)
    (S : TwoMessage (K:=K) (V:=V) Γ N→Finset (Fin N))
    (hS : ∀ z,Disjoint (S z) (bothExpensive z.2.2)) :
    conditionedDeficit p C F E hp S (jointJ K (n+2)) ≤
      excessCost p C F Jprev (jointJ K (n+2))/(p.map (sourceMessage C F)).event E := by
  unfold conditionedDeficit
  apply Selection.selectedDeficit_onContextEvent_le
  · intro z hz
    convert twoScan_subset_pointwise hdim p C F hcons hinc z hz (S z) (hS z) using 1; congr!
  · exact (twoScan_subset_deficit hdim p C F D Jprev hcons hinc hD hprev S hS).2

theorem actual_common_class {N n : ℕ} (hdim : Module.finrank K V=n+3)
    (p : Selection.Law Ω) (C : Ω→Γ) (F : Ω→Fin N→ProjectivePair (K:=K) (V:=V))
    (D : Γ→Fin N→Finset (ProjectivePair (K:=K) (V:=V))) (Jprev : ℝ)
    (hcons : ∀ x,p.mass x≠0→ScanConsistent ((List.ofFn (F x)).map toScan))
    (hinc : ∀ x,p.mass x≠0→∀ i,Incidence.Incident (F x i).1 (F x i).2)
    (hD : ∀ x,p.mass x≠0→∀ i,F x i∈D (C x) i)
    (hprev : ∀ c i,Real.log (D c i).card≤Jprev)
    (colour : TwoMessage (K:=K) (V:=V) Γ N→Fin N→κ) (m : ℕ)
    (hm : (Fintype.card κ*m:ℕ)+expensiveBudget K V+
      expensiveBudget K (Module.Dual K V)≤(N:ℝ)) :
    ∃ (c : κ) (E : Finset (TwoMessage (K:=K) (V:=V) Γ N))
      (hE : 0<(p.map (sourceMessage C F)).event E)
      (S : TwoMessage (K:=K) (V:=V) Γ N→Finset (Fin N)),
      1/(Fintype.card κ:ℝ)≤(p.map (sourceMessage C F)).event E ∧
      (∀ z,Disjoint (S z) (bothExpensive z.2.2)) ∧
      (∀ z∈E,(S z).card=m ∧ ∀ i∈S z,colour z i=c) ∧
      conditionedDeficit p C F E hE S (jointJ K (n+2)) ≤
        excessCost p C F Jprev (jointJ K (n+2))/(p.map (sourceMessage C F)).event E := by
  obtain ⟨c,E,hp,S,hprob,hS,hslots⟩ := actual_common_class_slots p C F colour m hm
  exact ⟨c,E,hp,S,hprob,hS,hslots,
    twoScan_conditioned_deficit hdim p C F D Jprev hcons hinc hD hprev E hp S hS⟩

end
end SharpLogRamsey.Marking

end

end OAI
