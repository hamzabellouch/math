import Mathlib
import OAI.Combinatorics.SharpRamsey.Exposure.StreamTransport

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real
open scoped Classical BigOperators
noncomputable section

structure ContextOutput {Ω F : Type} [Fintype Ω] [Fintype F] {ℓ : ℕ}
    (p : Law Ω) (G : Ω→Fin ℓ→F) (m : ℕ) (B C L : ℝ) where
  X : Type
  Γ : Type
  finiteX : Fintype X
  finiteΓ : Fintype Γ
  μ : @Law X finiteX
  source : X→Ω
  msg : X→Γ
  chosen : X→Fin m↪o Fin ℓ
  domains : Γ→Fin m→Finset F
  supported : ∀ x,p.mass (source x)≠0
  hit : ∀ x i,G (source x) (chosen x i)∈domains (msg x) i
  size : ∀ c i,((domains c i).card:ℝ)≤B
  dominated : letI:=finiteX; ∀ a,(μ.map source).mass a≤L*p.mass a
  cost : letI:=finiteX; letI:=finiteΓ; entropy (μ.map msg)≤C
attribute [instance] ContextOutput.finiteX ContextOutput.finiteΓ

variable {Ω F X Γ : Type} [Fintype Ω] [Fintype F] [Fintype X] [Fintype Γ]
  {ℓ m : ℕ} {B C L : ℝ}

theorem contextOutput_of_lists (p : Law Ω) (G : Ω→Fin ℓ→F) (μ : Law X)
    (source : X→Ω) (msg : X→Γ) (out : X→List F) (domains : Γ→List (Finset F))
    (hB : 0≤B)
    (hlen : ∀ x,μ.mass x≠0→(out x).length=m)
    (hsub : ∀ x,μ.mass x≠0→(out x).Sublist (List.ofFn (G (source x))))
    (hhit : ∀ x,μ.mass x≠0→List.Forall₂ (fun f D=>f∈D) (out x) (domains (msg x)))
    (hsize : ∀ c D,D∈domains c→(D.card:ℝ)≤B)
    (hdom : ∀ a,(μ.map source).mass a≤L*p.mass a)
    (hcost : entropy (μ.map msg)≤C) : Nonempty (ContextOutput p G m B C L) := by
  let Y:={x // μ.mass x≠0}
  have he : ∀ x : Y,∃ e : Fin m↪o Fin ℓ,∀ i,
      G (source x.val) (e i)=(out x.val).get ⟨i.val,by rw [hlen x.val x.property];exact i.isLt⟩ := by
    intro x
    obtain ⟨e,he⟩:=List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp (hsub x.val x.property)
    let f : Fin m↪o Fin ℓ:=
      (Fin.castOrderIso (hlen x.val x.property).symm).toOrderEmbedding.trans
        (e.trans (Fin.castOrderIso (List.length_ofFn (f:=G (source x.val)))).toOrderEmbedding)
    refine ⟨f,?_⟩
    intro i
    have hh:=he ((Fin.castOrderIso (hlen x.val x.property).symm) i)
    rw [List.get_ofFn] at hh
    exact hh.symm
  choose e he using he
  refine ⟨⟨Y,Γ,inferInstance,inferInstance,μ.nullFree,(fun x=>source x.val),
    (fun x=>msg x.val),e,(fun c i=>(domains c).getD i.val ∅),?_,?_,?_,?_,?_⟩⟩
  · intro x hz
    have ha:=hdom (source x.val)
    rw [hz,mul_zero] at ha
    have hh:=(μ.le_map source x.val).trans ha
    exact x.property (le_antisymm hh (μ.nonneg x.val))
  · intro x i
    rw [he]
    have hdlen : (domains (msg x.val)).length=m := by
      rw [←(hhit x.val x.property).length_eq,hlen x.val x.property]
    rw [List.getD_eq_getElem _ _ (by rw [hdlen];exact i.isLt)]
    exact (hhit x.val x.property).get (by rw [hlen x.val x.property];exact i.isLt)
      (by rw [hdlen];exact i.isLt)
  · intro c i
    by_cases hi : i.val<(domains c).length
    · rw [List.getD_eq_getElem _ _ hi]
      exact hsize c _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]
      simpa using hB
  · intro a
    rw [Law.nullFree_map]
    exact hdom a
  · rw [Law.nullFree_map]
    exact hcost
end
end SharpLogRamsey.Selection

end

end OAI
