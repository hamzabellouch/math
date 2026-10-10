import Mathlib

namespace OAI

section


/-!
Integral chains for a polygon incidence system, with all lifted edges independent.
This is the algebraic cellular boundary needed for the source's cycle producer.
It does not identify these chains with a topological homology theory.
-/
noncomputable section
namespace HyperbolicObstruction
namespace IntegralIncidence

variable {E V G C : Type*} [Group G]

/-- Formal dart reversal. Loop edges and parallel indexed edges remain distinct. -/
def reverse (e : E × Bool) : E × Bool := (e.1, !e.2)

@[simp] theorem reverse_reverse (e : E × Bool) : reverse (reverse e) = e := by
  rcases e with ⟨e,b⟩; cases b <;> rfl

variable (start : E × Bool → V) (voltage : E × Bool → G)

def liftedStart (e : G × (E × Bool)) : G × V := (e.1, start e.2)
def liftedReverse (e : G × (E × Bool)) : G × (E × Bool) :=
  (e.1 * voltage e.2, reverse e.2)

variable (hv : ∀ e, voltage (reverse e) = (voltage e)⁻¹)

include hv in
@[simp] theorem liftedReverse_reverse (e : G × (E × Bool)) :
    liftedReverse voltage (liftedReverse voltage e) = e := by
  apply Prod.ext
  · simp [liftedReverse, hv]
  · exact reverse_reverse e.2

/-- Signed contribution of a lifted dart to the free integral edge module.
A negative dart is indexed at the start of its *positive* reverse. -/
def edgeChain (e : G × (E × Bool)) : (G × E) →₀ ℤ :=
  if e.2.2 then Finsupp.single (e.1,e.2.1) 1
  else -Finsupp.single (e.1 * voltage e.2,e.2.1) 1

include hv in
@[simp] theorem edgeChain_reverse (e : G × (E × Bool)) :
    edgeChain voltage (liftedReverse voltage e) = -edgeChain voltage e := by
  rcases e with ⟨g,e,b⟩
  have ht : voltage (e,false) = (voltage (e,true))⁻¹ := hv (e,true)
  cases b <;> simp [edgeChain,liftedReverse,reverse,ht]

/-- The boundary of a positive lifted edge. -/
def edgeBoundary (e : G × E) : (G × V) →₀ ℤ :=
  Finsupp.single (e.1 * voltage (e.2,true),start (e.2,false)) 1 -
    Finsupp.single (e.1,start (e.2,true)) 1

def d₁ : ((G × E) →₀ ℤ) →ₗ[ℤ] ((G × V) →₀ ℤ) :=
  Finsupp.linearCombination ℤ (edgeBoundary start voltage)

include hv in
lemma boundary_edgeChain (e : G × (E × Bool)) :
    d₁ start voltage (edgeChain voltage e) =
      Finsupp.single (liftedStart start (liftedReverse voltage e)) 1 -
        Finsupp.single (liftedStart start e) 1 := by
  rcases e with ⟨g,e,b⟩
  have hf : voltage (e,true) = (voltage (e,false))⁻¹ := hv (e,false)
  cases b <;>
    simp [d₁,edgeChain,edgeBoundary,liftedStart,liftedReverse,reverse,hf]

/-- An indexed polygonal attaching system, before topological realization. -/
structure Polygons (E V C : Type*) where
  start : E × Bool → V
  size : C → ℕ
  positive : ∀ c, 0 < size c
  side : (c : C) → Fin (size c) → E × Bool
  closed : ∀ c i, start (side c (finRotate _ i)) = start (reverse (side c i))

lemma group_prefix_rotate {G : Type*} [Group G] {m : ℕ} (p : Fin m → G)
    (hp : (List.ofFn p).prod = 1) (i : Fin m) :
    ((List.ofFn p).take ((finRotate m i).val)).prod =
      ((List.ofFn p).take i.val).prod * p i := by
  cases m with
  | zero => exact Fin.elim0 i
  | succ m =>
    have hs := List.prod_take_succ (List.ofFn p) i.val (by simpa only [List.length_ofFn] using i.isLt)
    have he : (List.ofFn p)[i.val] = p i := List.getElem_ofFn (by simpa only [List.length_ofFn] using i.isLt)
    rw [he] at hs
    by_cases hi : i = Fin.last m
    · subst i
      rw [finRotate_apply,Fin.val_add_one,ite_eq_left rfl]
      have hlen : (Fin.last m).val + 1 = (List.ofFn p).length := by simp only [Fin.val_last,List.length_ofFn]
      rw [hlen,List.take_length,hp] at hs
      simpa only [List.take_zero,List.prod_nil] using hs
    · rw [finRotate_apply,Fin.val_add_one,ite_eq_right hi]
      exact hs


end IntegralIncidence
end HyperbolicObstruction
end
end

end OAI
