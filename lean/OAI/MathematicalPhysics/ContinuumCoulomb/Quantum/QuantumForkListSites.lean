import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListOrdinal
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListGraph

namespace OAI

/-! Actual fork sites obtained from the ordered port arrays. Their bounds and
injectivity are the geometric hypotheses of the parallel perturbation theorem. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList

structure ValidPorts (n : ℕ) (gs : Groups) : Prop where
  centers : gs.length ≤ n
  bounded : ∀ (i : Fin gs.length) (j : Fin (groupAt gs i.val).length),
    (portAt (groupAt gs i.val) j.val).1 < n
  disjoint : ∀ (i k : Fin gs.length) (j : Fin (groupAt gs k.val).length),
    i.val ≠ (portAt (groupAt gs k.val) j.val).1
  injective : ∀ (i k : Fin gs.length) (j : Fin (groupAt gs i.val).length)
    (l : Fin (groupAt gs k.val).length),
    (portAt (groupAt gs i.val) j.val).1=(portAt (groupAt gs k.val) l.val).1 →
      i=k ∧ j.val=l.val

def localPair (gs : Groups) (e : Fin (pairCount gs)) : LocalPair gs :=
  (pairEquiv gs).symm e

def localFirst (gs : Groups) (e : Fin (pairCount gs)) :
    Fin (groupAt gs (localPair gs e).1.val).length :=
  ⟨2*(localPair gs e).2.val,by have := (localPair gs e).2.isLt; omega⟩

def localSecond (gs : Groups) (e : Fin (pairCount gs)) :
    Fin (groupAt gs (localPair gs e).1.val).length :=
  ⟨2*(localPair gs e).2.val+1,by have := (localPair gs e).2.isLt; omega⟩

def actualSite {n : ℕ} {gs : Groups} (h : ValidPorts n gs) (e : Fin (pairCount gs)) :
    Fin 3 → Fin n :=
  ![⟨(localPair gs e).1.val,lt_of_lt_of_le (localPair gs e).1.isLt h.centers⟩,
    ⟨(portAt (groupAt gs (localPair gs e).1.val) (localFirst gs e).val).1,
      h.bounded (localPair gs e).1 (localFirst gs e)⟩,
    ⟨(portAt (groupAt gs (localPair gs e).1.val) (localSecond gs e).val).1,
      h.bounded (localPair gs e).1 (localSecond gs e)⟩]

def actualJ (gs : Groups) (e : Fin (pairCount gs)) : ℚ :=
  (portAt (groupAt gs (localPair gs e).1.val) (localFirst gs e).val).2

def actualK (gs : Groups) (e : Fin (pairCount gs)) : ℚ :=
  (portAt (groupAt gs (localPair gs e).1.val) (localSecond gs e).val).2

theorem actualSite_injective {n : ℕ} {gs : Groups} (h : ValidPorts n gs)
    (e : Fin (pairCount gs)) : Function.Injective (actualSite h e) := by
  intro a b hab
  have hh := congrArg Fin.val hab
  fin_cases a <;> fin_cases b <;> simp only [actualSite] at hh ⊢
  · exact (h.disjoint (localPair gs e).1 (localPair gs e).1 (localFirst gs e) hh).elim
  · exact (h.disjoint (localPair gs e).1 (localPair gs e).1 (localSecond gs e) hh).elim
  · exact (h.disjoint (localPair gs e).1 (localPair gs e).1 (localFirst gs e) hh.symm).elim
  · have hp := (h.injective (localPair gs e).1 (localPair gs e).1
      (localFirst gs e) (localSecond gs e) hh).2
    simp only [localFirst,localSecond] at hp
    omega
  · exact (h.disjoint (localPair gs e).1 (localPair gs e).1 (localSecond gs e) hh.symm).elim
  · have hp := (h.injective (localPair gs e).1 (localPair gs e).1
      (localSecond gs e) (localFirst gs e) hh).2
    simp only [localFirst,localSecond] at hp
    omega

theorem catalog_actualSite {n : ℕ} {gs : Groups} (h : ValidPorts n gs)
    (e : Fin (pairCount gs)) :
    ((catalog gs).drop e.val).headD (0,((0,0),(0,0))) =
      ((actualSite h e 0).val,((actualSite h e 1).val,actualJ gs e),
        ((actualSite h e 2).val,actualK gs e)) := by
  have hc := catalog_pairEquiv gs (localPair gs e)
  rw [show pairEquiv gs (localPair gs e)=e from (pairEquiv gs).apply_symm_apply e] at hc
  exact hc

end ContinuumCoulomb.QuantumForkList

end

end OAI
