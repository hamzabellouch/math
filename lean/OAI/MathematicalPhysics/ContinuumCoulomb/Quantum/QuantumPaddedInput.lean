import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumWireState

namespace OAI

/-! The lifted circuit starts with exactly the original witness and zero fresh wires. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

abbrev qmaPaddedCircuit (c : QMACircuit) (extra : ℕ) : QMACircuit :=
  ⟨c.work+extra,c.witness,
    c.gates.map (qmaMapGate c.work (c.work+extra) (qmaPaddedLeft c.work extra))⟩

theorem qmaPaddedCircuit_wellFormed (c : QMACircuit) (hc : c.WellFormed) (extra : ℕ) :
    (qmaPaddedCircuit c extra).WellFormed := by
  refine ⟨hc.1.trans (Nat.le_add_right _ _),?_⟩
  intro g hg
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hg
  exact qmaMapGate_wellFormed c.work (c.work+extra) _
    (qmaPaddedLeft_injective c.work extra) f (hc.2 f hf)

@[simp] theorem qmaPaddedLeft_val (work extra : ℕ) (i : Fin (work+1)) :
    (qmaPaddedLeft work extra i).val = i.val := rfl

@[simp] theorem qmaPaddedRight_val (work extra : ℕ) (i : Fin extra) :
    (qmaPaddedRight work extra i).val = work+1+i.val := rfl

theorem qmaPaddedAncillaZero (c : QMACircuit) (hc : c.WellFormed) (extra : ℕ)
    (s : SourceSpinBasis (c.work+extra+1)) :
    QMAAncillaZero (qmaPaddedCircuit c extra) s ↔
      QMAAncillaZero c (qmaPaddedBasis c.work extra s).1 ∧
        (qmaPaddedBasis c.work extra s).2 = 0 := by
  constructor
  · intro h
    constructor
    · intro i hi
      exact h (qmaPaddedLeft c.work extra i) hi
    · funext j
      apply h (qmaPaddedRight c.work extra j)
      change c.witness ≤ c.work+1+j.val
      have hc' : c.witness ≤ c.work := hc.1
      omega
  · rintro ⟨hl,hr⟩ k hk
    suffices h : ∀ a : Fin ((c.work+1)+extra),
        c.witness ≤ (qmaPaddedIndex c.work extra a).val →
        s (qmaPaddedIndex c.work extra a) = 0 by
      have hm := h ((qmaPaddedIndex c.work extra).symm k)
      have he := (qmaPaddedIndex c.work extra).apply_symm_apply k
      rw [he] at hm
      exact hm hk
    intro a
    refine Fin.addCases (fun i => ?_) (fun j => ?_) a
    · intro hi
      exact hl i hi
    · intro _
      exact congrFun hr j

theorem qmaPaddedWitnessRestrict (c : QMACircuit) (hc : c.WellFormed) (extra : ℕ)
    (s : SourceSpinBasis (c.work+extra+1)) :
    qmaWitnessRestrict (qmaPaddedCircuit c extra) (qmaPaddedCircuit_wellFormed c hc extra) s =
      qmaWitnessRestrict c hc (qmaPaddedBasis c.work extra s).1 := by
  funext i
  change s ⟨i.val,_⟩ = (qmaPaddedBasis c.work extra s).1 ⟨i.val,_⟩
  rw [qmaPaddedBasis_left]
  congr 1

theorem qmaInitialState_padded (c : QMACircuit) (hc : c.WellFormed) (extra : ℕ)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness))
    (s : SourceSpinBasis (c.work+extra+1)) :
    qmaInitialState (qmaPaddedCircuit c extra) (qmaPaddedCircuit_wellFormed c hc extra) psi s =
      qmaInitialState c hc psi (qmaPaddedBasis c.work extra s).1 *
        if (qmaPaddedBasis c.work extra s).2 = 0 then 1 else 0 := by
  by_cases hs : QMAAncillaZero (qmaPaddedCircuit c extra) s
  · have hs' : ∀ i : Fin (c.work+extra+1), c.witness ≤ i.val → s i = 0 := hs
    obtain ⟨hl,hr⟩ := (qmaPaddedAncillaZero c hc extra s).mp hs
    have hl' : ∀ i : Fin (c.work+1), c.witness ≤ i.val →
        (qmaPaddedBasis c.work extra s).1 i = 0 := hl
    simp only [qmaInitialState,ite_eq_left hs',ite_eq_left hl',ite_eq_left hr,mul_one]
    exact congrArg (fun v => psi v) (qmaPaddedWitnessRestrict c hc extra s)
  · have hs' : ¬∀ i : Fin (c.work+extra+1), c.witness ≤ i.val → s i = 0 := hs
    by_cases hl : QMAAncillaZero c (qmaPaddedBasis c.work extra s).1
    · have hr : (qmaPaddedBasis c.work extra s).2 ≠ 0 :=
        fun h => hs ((qmaPaddedAncillaZero c hc extra s).mpr ⟨hl,h⟩)
      have hl' : ∀ i : Fin (c.work+1), c.witness ≤ i.val →
          (qmaPaddedBasis c.work extra s).1 i = 0 := hl
      simp only [qmaInitialState,ite_eq_right hs',ite_eq_left hl',ite_eq_right hr,mul_zero]
    · have hl' : ¬∀ i : Fin (c.work+1), c.witness ≤ i.val →
          (qmaPaddedBasis c.work extra s).1 i = 0 := hl
      simp only [qmaInitialState,ite_eq_right hs',ite_eq_right hl',zero_mul]

end ContinuumCoulomb

end

end OAI
