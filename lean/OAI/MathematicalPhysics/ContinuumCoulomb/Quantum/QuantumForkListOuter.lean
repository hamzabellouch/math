import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListDegree

namespace OAI

/-! Paired outer ports form an injective family. The explicit local-pair
numbering therefore meets the simultaneous-fork degree hypotheses. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open scoped Classical

def outerPort (gs : Groups) (p : Fin (pairCount gs) × Fin 2) :
    Σ i : Fin gs.length, Fin (groupAt gs i.val).length :=
  ⟨(localPair gs p.1).1,
   ⟨2*(localPair gs p.1).2.val+p.2.val,by
      have := (localPair gs p.1).2.isLt
      have := p.2.isLt
      omega⟩⟩

theorem outerPort_injective (gs : Groups) : Function.Injective (outerPort gs) := by
  rintro ⟨e,b⟩ ⟨f,c⟩ h
  have hi : (localPair gs e).1=(localPair gs f).1 := congrArg (fun q : (Σ i : Fin gs.length, Fin (groupAt gs i.val).length) => q.1) h
  have hj : 2*(localPair gs e).2.val+b.val=2*(localPair gs f).2.val+c.val :=
    congrArg (fun p => p.2.val) h
  have hb := b.isLt
  have hc := c.isLt
  have heq : localPair gs e=localPair gs f := by
    apply Sigma.ext hi
    exact (Fin.heq_ext_iff (congrArg (fun i : Fin gs.length => (groupAt gs i.val).length/2) hi)).2 (by omega)
  have hef : e=f := (pairEquiv gs).symm.injective heq
  have hbc : b=c := Fin.ext (by omega)
  exact Prod.ext hef hbc

theorem actual_outer_eq {n : ℕ} {gs : Groups} (h : ValidPorts n gs)
    (p : Fin (pairCount gs) × Fin 2) :
    (qmaForkOuter (actualSite h) p).val=
      (portAt (groupAt gs (outerPort gs p).1.val) (outerPort gs p).2.val).1 := by
  rcases p with ⟨e,b⟩
  fin_cases b <;> rfl

theorem actual_outer_injective {n : ℕ} {gs : Groups} (h : ValidPorts n gs) :
    Function.Injective (qmaForkOuter (actualSite h)) := by
  intro p q hpq
  have hv := congrArg Fin.val hpq
  rw [actual_outer_eq,actual_outer_eq] at hv
  have he := h.injective (outerPort gs p).1 (outerPort gs q).1
    (outerPort gs p).2 (outerPort gs q).2 hv
  apply outerPort_injective gs
  apply Sigma.ext he.1
  exact (Fin.heq_ext_iff (congrArg (fun i : Fin gs.length => (groupAt gs i.val).length) he.1)).2 he.2

theorem outerPort_index_lt (gs : Groups) (p : Fin (pairCount gs) × Fin 2) :
    (outerPort gs p).2.val < 2*((groupAt gs (outerPort gs p).1.val).length/2) := by
  have hp := (localPair gs p.1).2.isLt
  have hb := p.2.isLt
  dsimp only [outerPort]
  omega

theorem actual_outer_away_retained {n : ℕ} {gs : Groups} (h : ValidPorts n gs)
    (i : Fin gs.length) (j : Fin (groupAt gs i.val).length)
    (hj : 2*((groupAt gs i.val).length/2) ≤ j.val)
    (p : Fin (pairCount gs) × Fin 2) :
    qmaForkOuter (actualSite h) p ≠
      ⟨(portAt (groupAt gs i.val) j.val).1,h.bounded i j⟩ := by
  intro he
  have hv := congrArg Fin.val he
  rw [actual_outer_eq] at hv
  have hh := h.injective (outerPort gs p).1 i (outerPort gs p).2 j hv
  have hl := outerPort_index_lt gs p
  have hlen := congrArg (fun i : Fin gs.length => 2*((groupAt gs i.val).length/2)) hh.1
  rw [hlen] at hl
  omega

theorem actual_outer_away_center {n : ℕ} {gs : Groups} (h : ValidPorts n gs)
    (i : Fin gs.length) (e : Fin (pairCount gs)) :
    actualSite h e 1 ≠ ⟨i.val,lt_of_lt_of_le i.isLt h.centers⟩ ∧
      actualSite h e 2 ≠ ⟨i.val,lt_of_lt_of_le i.isLt h.centers⟩ := by
  constructor
  · intro he
    exact h.disjoint i (localPair gs e).1 (localFirst gs e) (congrArg Fin.val he).symm
  · intro he
    exact h.disjoint i (localPair gs e).1 (localSecond gs e) (congrArg Fin.val he).symm

end ContinuumCoulomb.QuantumForkList

end

end OAI
