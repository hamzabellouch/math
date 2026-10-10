import Mathlib
import OAI.Combinatorics.UniformKServer.RoundingChain

namespace OAI

                                 
section

/-! A finite ranked rooted tree is enumerated in increasing rank and converted
to the ordered finite shapes used by the allocator and rounding proofs. -/
noncomputable section
namespace UniformKServer.RankedTree
open TreeRounding TreeAncestry
open scoped Classical

structure Data (V : Type*) where
  root : V
  parent : V → V
  level : V → ℕ
  level_root : level root=0
  level_zero : ∀ v, level v=0 → v=root
  step : ∀ v, v ≠ root → level (parent v)+1=level v

variable {V : Type*} [Fintype V]

def size (_T : Data V) : ℕ := Fintype.card V-1

theorem size_card (T : Data V) : Fintype.card V=size T+1 := by
  have : Nonempty V := ⟨T.root⟩
  have hp := Fintype.card_pos_iff.mpr this
  unfold size
  omega

def orderKey (T : Data V) (v : V) : Lex (ℕ × ℕ) := toLex (T.level v,(Fintype.equivFin V v).val)

theorem orderKey_injective (T : Data V) : Function.Injective (orderKey T) := by
  intro u v he
  have hh : (Fintype.equivFin V u).val=(Fintype.equivFin V v).val := congrArg (fun p => (ofLex p).2) he
  exact (Fintype.equivFin V).injective (Fin.ext hh)

abbrev order (T : Data V) : LinearOrder V := LinearOrder.lift' (orderKey T) (orderKey_injective T)

def chart (T : Data V) : Vertex (size T) ≃ V :=
  letI := order T
  (Fintype.orderIsoFinOfCardEq V (size_card T)).toEquiv

theorem key_less (T : Data V) (u v : V) (h : T.level u < T.level v) : orderKey T u < orderKey T v :=
  Prod.Lex.left _ _ h

theorem vertex_less (T : Data V) (u v : V) (h : T.level u < T.level v) :
    (chart T).symm u < (chart T).symm v := by
  let := order T
  exact (Fintype.orderIsoFinOfCardEq V (size_card T)).symm.strictMono (key_less T u v h)

theorem chart_zero (T : Data V) : chart T 0=T.root := by
  by_contra h
  have hp : 0 < T.level (chart T 0) := by
    by_contra hp
    exact h (T.level_zero _ (by omega))
  have hh := vertex_less T T.root (chart T 0) (by rw [T.level_root]; exact hp)
  simp only [Equiv.symm_apply_apply] at hh
  exact (Nat.not_lt_zero _ hh).elim

theorem root_vertex (T : Data V) : (chart T).symm T.root=0 := by rw [←chart_zero T]; exact (chart T).symm_apply_apply 0

def shape (T : Data V) : Shape (size T) where
  parent := fun v => if v=0 then 0 else (chart T).symm (T.parent (chart T v))
  earlier := by
    intro v hv
    simp only [ite_eq_right hv]
    have hn : chart T v ≠ T.root := by
      intro hh
      have he := congrArg (chart T).symm hh
      exact hv (by simpa only [Equiv.symm_apply_apply,root_vertex] using he)
    have hs := vertex_less T (T.parent (chart T v)) (chart T v) (by have hh := T.step _ hn; omega)
    simpa only [Fin.lt_def, Equiv.symm_apply_apply] using hs

theorem shape_parent (T : Data V) (v : Vertex (size T)) (hv : v ≠ 0) :
    (shape T).parent v=(chart T).symm (T.parent (chart T v)) := ite_eq_right hv

theorem depth_eq (T : Data V) (v : Vertex (size T)) : depth (shape T) v=T.level (chart T v) := by
  induction v using WellFounded.induction (measure Fin.val).wf with
  | h v ih =>
    by_cases hv : v=0
    · subst v
      rw [depth_root,chart_zero,T.level_root]
    · have hn : chart T v ≠ T.root := by
        intro hh
        exact hv (by simpa only [Equiv.symm_apply_apply,root_vertex] using congrArg (chart T).symm hh)
      rw [depth_child v hv,ih _ ((shape T).earlier v hv),shape_parent T v hv,Equiv.apply_symm_apply]
      exact T.step _ hn

end UniformKServer.RankedTree

end


end

end OAI
