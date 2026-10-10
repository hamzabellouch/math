import Mathlib
import OAI.Combinatorics.KMedian.Amplification.PoweringObjects

namespace OAI

section Inline_PCPGraphExtend

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

lemma extend_involutive {U W : Type} [Fintype U] [DecidableEq W]
    (p : U ≃ U) (hp : Function.Involutive p) (e : U ↪ W) :
    Function.Involutive (Equiv.Perm.viaFintypeEmbedding p e) := by
  intro w
  by_cases h : w ∈ Set.range e
  · obtain ⟨u,rfl⟩ := h
    simp only [Equiv.Perm.viaFintypeEmbedding_apply_image]
    exact congrArg e (hp u)
  · rw [Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ h,
      Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ h]

namespace PortGraph
variable {V W D : Type} [Fintype V] [Fintype D] [DecidableEq W] [DecidableEq D]
variable (G : PortGraph V D) (e : V ↪ W)

def portEmbed : V × D ↪ W × D := e.prodMap (Function.Embedding.refl D)

def extend : PortGraph W D where
  rotate := Equiv.Perm.viaFintypeEmbedding G.rotate (portEmbed e)
  involutive := extend_involutive _ G.involutive _

@[simp] lemma extend_rotate_image (p : V × D) :
    (G.extend e).rotate (e p.1,p.2)=(e (G.rotate p).1,(G.rotate p).2) :=
  Equiv.Perm.viaFintypeEmbedding_apply_image _ _ p

@[simp] lemma extend_step_image (v : V) (d : D) :
    (G.extend e).step (e v) d=e (G.step v d) :=
  congrArg Prod.fst (G.extend_rotate_image e (v,d))

omit [Fintype V] [Fintype D] [DecidableEq W] [DecidableEq D] in
lemma portEmbed_range (p : W × D) : p ∈ Set.range (portEmbed e) ↔ p.1 ∈ Set.range e := by
  constructor
  · rintro ⟨⟨v,d⟩,h⟩
    exact ⟨v,congrArg Prod.fst h⟩
  · rintro ⟨v,h⟩
    exact ⟨(v,p.2),Prod.ext h rfl⟩

lemma extend_rotate_outside (p : W × D) (hp : p.1 ∉ Set.range e) : (G.extend e).rotate p=p :=
  Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ (fun h => hp ((portEmbed_range e p).mp h))

end PortGraph

namespace PortCSP
variable {V W D A : Type} [Fintype V] [Fintype D] [DecidableEq W] [DecidableEq D]
  [Fintype A] [DecidableEq A]
variable {G : PortGraph V D} (C : PortCSP G A) (e : V ↪ W)

noncomputable def extendedAllowed (p : W × D) : Finset (A × A) :=
  if h : p ∈ Set.range (PortGraph.portEmbed e) then
    C.allowed ((PortGraph.portEmbed e).toEquivRange.symm ⟨p,h⟩) else univ

omit [DecidableEq A] in
@[simp] lemma extendedAllowed_image (p : V × D) :
    C.extendedAllowed e (e p.1,p.2)=C.allowed p := by
  change C.extendedAllowed e (PortGraph.portEmbed e p)=_
  simp only [extendedAllowed,Set.mem_range_self,dite_eq_left,
    Function.Embedding.toEquivRange_symm_apply_self]

omit [DecidableEq A] in
lemma extendedAllowed_outside (p : W × D) (hp : p.1 ∉ Set.range e) :
    C.extendedAllowed e p=univ := by
  rw [extendedAllowed,dite_eq_right (fun h => hp ((PortGraph.portEmbed_range e p).mp h))]

noncomputable def extend : PortCSP (G.extend e) A where
  allowed := C.extendedAllowed e
  symmetric := by
    intro p a b
    by_cases hp : p.1 ∈ Set.range e
    · obtain ⟨v,hv⟩ := hp
      have he : p=(e v,p.2) := Prod.ext hv.symm rfl
      rw [he,G.extend_rotate_image e (v,p.2),C.extendedAllowed_image e (G.rotate (v,p.2)),
        C.extendedAllowed_image e (v,p.2)]
      exact C.symmetric (v,p.2) a b
    · rw [G.extend_rotate_outside e p hp,C.extendedAllowed_outside e p hp]
      simp

omit [DecidableEq A] in
@[simp] lemma extend_bad_image (a : W → A) (p : V × D) :
    (C.extend e).Bad a (e p.1,p.2) ↔ C.Bad (a ∘ e) p := by
  unfold Bad
  rw [G.extend_step_image]
  change (a (e p.1),a (e (G.step p.1 p.2))) ∉ C.extendedAllowed e (e p.1,p.2) ↔ _
  rw [extendedAllowed_image]
  rfl

omit [DecidableEq A] in
lemma extend_complete [Inhabited A] (a : V → A) (ha : C.Satisfies a) :
    ∃ b, (C.extend e).Satisfies b := by
  let b : W → A := fun w => if h : w ∈ Set.range e then a (e.toEquivRange.symm ⟨w,h⟩) else default
  have hb (v : V) : b (e v)=a v := by simp [b]
  refine ⟨b,?_⟩
  intro w d
  by_cases h : w ∈ Set.range e
  · obtain ⟨v,rfl⟩ := h
    change _ ∈ C.extendedAllowed e (e v,d)
    rw [G.extend_step_image,C.extendedAllowed_image e (v,d),hb,hb]
    exact ha v d
  · change _ ∈ C.extendedAllowed e (w,d)
    rw [C.extendedAllowed_outside e (w,d) h]
    exact mem_univ _

end PortCSP
end MetricKMedian.PCP

end Inline_PCPGraphExtend

end OAI
