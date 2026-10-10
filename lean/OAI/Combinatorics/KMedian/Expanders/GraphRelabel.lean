import Mathlib
import OAI.Combinatorics.KMedian.Expanders.SpectralWalk

namespace OAI

section Inline_PCPGraphRelabel

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

lemma energy_comp_equiv {V W : Type} [Fintype V] [Fintype W] (e : V ≃ W) (f : W → ℝ) :
    energy (f ∘ e)=energy f := by
  unfold energy
  exact Fintype.expect_equiv e _ _ (fun _ => rfl)

namespace PortGraph
variable {V D W E : Type}

def relabel (G : PortGraph V D) (e : V ≃ W) (d : D ≃ E) : PortGraph W E where
  rotate := ((Equiv.prodCongr e d).symm.trans G.rotate).trans (Equiv.prodCongr e d)
  involutive p := by
    change (Equiv.prodCongr e d) (G.rotate ((Equiv.prodCongr e d).symm
      ((Equiv.prodCongr e d) (G.rotate ((Equiv.prodCongr e d).symm p)))))=p
    rw [Equiv.symm_apply_apply,G.involutive,Equiv.apply_symm_apply]

@[simp] lemma relabel_step (G : PortGraph V D) (e : V ≃ W) (d : D ≃ E) (v : W) (s : E) :
    (G.relabel e d).step v s=e (G.step (e.symm v) (d.symm s)) := rfl

variable [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]
  [Fintype W] [Nonempty W] [Fintype E] [Nonempty E]

omit [Fintype V] [Nonempty V] [Nonempty D] [Fintype W] [Nonempty W] [Nonempty E] in
lemma relabel_adjacency (G : PortGraph V D) (e : V ≃ W) (d : D ≃ E) (f : W → ℝ) :
    ((G.relabel e d).adjacency f) ∘ e=G.adjacency (f ∘ e) := by
  funext v
  unfold adjacency
  simp only [Function.comp_apply,relabel_step,Equiv.symm_apply_apply]
  exact (Fintype.expect_equiv d (fun s : D => f (e (G.step v s)))
    (fun s : E => f (e (G.step v (d.symm s)))) (by intro s; rw [Equiv.symm_apply_apply])).symm

omit [Nonempty V] [Nonempty D] [Nonempty W] [Nonempty E] in
theorem relabel_contracts (G : PortGraph V D) (e : V ≃ W) (d : D ≃ E) {ρ : ℝ}
    (hG : G.Contracts ρ) : (G.relabel e d).Contracts ρ := by
  intro f hf
  have hm : (𝔼 v, (f ∘ e) v)=0 :=
    (Fintype.expect_equiv e (f ∘ e) f (fun _ => rfl)).trans hf
  have h := hG (f ∘ e) hm
  rw [energy_comp_equiv e f] at h
  rw [← energy_comp_equiv e ((G.relabel e d).adjacency f),relabel_adjacency]
  exact h

end PortGraph
end MetricKMedian.PCP

end Inline_PCPGraphRelabel

end OAI
