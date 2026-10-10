import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.MarkingActual

namespace OAI

section
namespace SharpLogRamsey
open scoped Classical BigOperators
open Finset
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

 def flagPair (f : Flag K V) : Marking.ProjectivePair (K:=K) (V:=V) :=
  (f.point,f.dualPoint)

lemma flagPair_injective : Function.Injective (flagPair (K:=K) (V:=V)) := by
  intro a b h
  cases a; cases b
  cases h
  rfl

 def flagPairEquiv : Flag K V ≃
    {f : Marking.ProjectivePair (K:=K) (V:=V) // Incidence.Incident f.1 f.2} where
  toFun f := ⟨flagPair f,f.incident⟩
  invFun f := ⟨f.1.1,f.1.2,f.2⟩
  left_inv f := by cases f; rfl
  right_inv f := by cases f; rfl

variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
instance flagFintype : Fintype (Flag K V) := Fintype.ofEquiv _ flagPairEquiv.symm

variable [FiniteDimensional K V] [Finite K]
lemma actualFlag_card {d : ℕ} (hdim : Module.finrank K V=d+1) :
    Fintype.card (Flag K V) =
      (∑ i ∈ range (d+1),Nat.card K^i)*(∑ i ∈ range d,Nat.card K^i) := by
  let e : Flag K V ≃ Σ b : Projectivization K (Module.Dual K V),
      {a : Projectivization K V // Incidence.Incident a b} :=
    { toFun := fun f=>⟨f.dualPoint,f.point,f.incident⟩
      invFun := fun f=>⟨f.2.1,f.1,f.2.2⟩
      left_inv := fun f=>by cases f; rfl
      right_inv := fun f=>by cases f; rfl }
  rw [←Nat.card_eq_fintype_card,Nat.card_congr e,Nat.card_sigma]
  simp_rw [Incidence.card_incident_points hdim]
  simp only [sum_const,card_univ,smul_eq_mul]
  rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K (Module.Dual K V)
    (Subspace.dual_finrank_eq.trans hdim)]

 def reversedFlagPairs {N : ℕ} (F : Fin N→Flag K V) :
    Fin N→Marking.ProjectivePair (K:=K) (V:=V) := fun i=>flagPair (F i.rev)

omit [FiniteDimensional K V] [Finite K]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))] in
lemma reversedFlagPairs_injective {N : ℕ} :
    Function.Injective (reversedFlagPairs (K:=K) (V:=V) (N:=N)) := by
  intro F G h
  funext i
  apply flagPair_injective
  simpa only [reversedFlagPairs,Fin.rev_rev] using congrFun h i.rev

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem source_marking_upper {N n : ℕ} (hdim : Module.finrank K V=n+3)
    (p : Selection.Law Ω) (C : Ω→Γ) (F : Ω→Fin N→Flag K V)
    (D : Γ→Fin N→Finset (Flag K V)) (Δ Λ : ℝ) (hΔ : 0≤Δ)
    (hcons : ∀ x,p.mass x≠0→ Consistent (F x))
    (hD : ∀ x,p.mass x≠0→∀ i,F x i∈D (C x) i)
    (hprev : ∀ c i,Real.log (D c i).card≤Real.log (64*(Nat.card K:ℝ)^(n+2))+Δ)
    (hC : Selection.entropy (p.map C)≤Λ) :
    Selection.entropy (p.map F) ≤ Λ+
      N*Real.log ((Module.finrank K V+1)*3:ℝ)+N*Real.log (64*(Nat.card K:ℝ)^(n+2))+
      (32*(Module.finrank K V+1)^2*(Nat.card K:ℝ)*
        Real.log (Fintype.card (Marking.Points (K:=K) (V:=V))+1:ℝ))*Δ := by
  let e : Flag K V ↪ Marking.ProjectivePair (K:=K) (V:=V) :=
    ⟨flagPair,flagPair_injective⟩
  let F' := fun x=>reversedFlagPairs (F x)
  let D' := fun (c : Γ) (i : Fin N)=>(D c i.rev).map e
  have hc (x : Ω) (hx : p.mass x≠0) :
      Marking.ScanConsistent ((List.ofFn (F' x)).map Marking.toScan) := by
    have h := Marking.backwardScan_consistent (F x) (hcons x hx)
    simpa only [List.map_ofFn,F',reversedFlagPairs,flagPair,Marking.toScan,
      Marking.backwardScan,Function.comp_def] using h
  have hi (x : Ω) (_hx : p.mass x≠0) (i : Fin N) :
      Incidence.Incident (F' x i).1 (F' x i).2 := (F x i.rev).incident
  have hd (x : Ω) (hx : p.mass x≠0) (i : Fin N) : F' x i∈D' (C x) i :=
    mem_map.mpr ⟨F x i.rev,hD x hx i.rev,rfl⟩
  have hp (c : Γ) (i : Fin N) : Real.log (D' c i).card≤
      Real.log (64*(Nat.card K:ℝ)^(n+2))+Δ := by
    simpa only [D',card_map] using hprev c i.rev
  have H := Marking.actual_entropy_upper hdim p C F' D'
    (Real.log (64*(Nat.card K:ℝ)^(n+2))+Δ) hc hi hd hp
  have HE := Marking.expected_expensive_bound p F'
  have he : Selection.entropy (p.map F')=Selection.entropy (p.map F) := by
    rw [show p.map F'=(p.map F).map reversedFlagPairs from
      (Selection.Law.map_map p F reversedFlagPairs).symm]
    exact Selection.entropy_map_eq_of_injective _ _ reversedFlagPairs_injective
  rw [he] at H
  have ht := mul_le_mul_of_nonneg_right HE hΔ
  linarith

theorem described_selection_bound [Nonempty (Flag K V)] {N ℓ n : ℕ}
    (hdim : Module.finrank K V=n+3) (hℓ : ℓ≤N)
    (p : Selection.Law ((Fin N→Flag K V)×(Fin ℓ→Flag K V)))
    (reverse : (Fin ℓ→Flag K V)→(Fin ℓ→Flag K V))
    (C : ((Fin N→Flag K V)×(Fin ℓ→Flag K V))→Γ)
    (D : Γ→Fin ℓ→Finset (Flag K V)) (Δ Λ dom : ℝ) (hΔ : 0≤Δ) (hdom0 : 0<dom)
    (hdom : ∀ g,p.fst.mass g≤dom/(Fintype.card (Flag K V):ℝ)^N)
    (hselect : ∀ g f,p.mass (g,f)≠0→Selection.Occurs f g ∨ Selection.Occurs (reverse f) g)
    (hcons : ∀ x,p.mass x≠0→ Consistent x.2)
    (hD : ∀ x,p.mass x≠0→∀ i,x.2 i∈D (C x) i)
    (hprev : ∀ c i,Real.log (D c i).card≤Real.log (64*(Nat.card K:ℝ)^(n+2))+Δ)
    (hC : Selection.entropy (p.map C)≤Λ) :
    (ℓ:ℝ)*(Real.log (Fintype.card (Flag K V))-Real.log (64*(Nat.card K:ℝ)^(n+2))-
      Real.log ((Module.finrank K V+1)*3:ℝ)) ≤
      Real.log (2*dom*N.choose ℓ)+Λ+
      (32*(Module.finrank K V+1)^2*(Nat.card K:ℝ)*
        Real.log (Fintype.card (Marking.Points (K:=K) (V:=V))+1:ℝ))*Δ := by
  have hl := Selection.selected_entropy_bound hℓ p reverse hdom0 hdom hselect
  have hu := source_marking_upper hdim p C Prod.snd D Δ Λ hΔ hcons hD hprev hC
  rw [Selection.Law.map_snd] at hu
  linarith

end
end SharpLogRamsey

end

end OAI
