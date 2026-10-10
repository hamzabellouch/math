import OAI.Combinatorics.Crossing.GenericPointExtension
import OAI.Combinatorics.Crossing.TriangleOrientations

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem exists_generic_point_family {κ ν : Type*} [Fintype κ] [Fintype ν]
    (q : ν → Plane) (a v : κ → Plane) (hv : ∀ k, v k ≠ 0)
    (n : ℕ) (z : Fin n → Plane) (ε : Fin n → ℝ) (hε : ∀ i, 0 < ε i) :
    ∃ p : Fin n → Plane, (∀ i, dist (p i) (z i) < ε i) ∧ Function.Injective p ∧
      (∀ i j, q j ≠ p i) ∧
      (∀ i k, det2 (p i-a k) (v k) ≠ 0) ∧
      (∀ i j, i ≠ j → ∀ k, det2 (p j-p i) (v k) ≠ 0) ∧
      (∀ i j, i ≠ j → ∀ l, orient2 (p i) (p j) (q l) ≠ 0) := by
  induction n with
  | zero =>
    refine ⟨Fin.elim0,?_,?_,?_,?_,?_,?_⟩ <;> intro i <;> exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨p,hp,hinj,hpq,hline,hpar,hcorn⟩ :=
      ih (fun i => z i.succ) (fun i => ε i.succ) (fun i => hε i.succ)
    obtain ⟨x,hx,hxp,hxq,hxl,hxpar,hxcorn⟩ :=
      exists_generic_point_extension p q a v hv hpq (z 0) (ε 0) (hε 0)
    refine ⟨Fin.cons x p,?_,?_,?_,?_,?_,?_⟩
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · exact hx
      · exact hp i
    · apply Fin.cons_injective_of_injective _ hinj
      rintro ⟨i,hi⟩
      exact hxp i hi.symm
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · exact hxq
      · exact hpq i
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · exact hxl
      · exact hline i
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · intro h
          exact False.elim (h rfl)
        · intro _ k
          change det2 (p j-x) (v k) ≠ 0
          have hh : det2 (p j-x) (v k) = -det2 (x-p j) (v k) := by
            dsimp [det2]
            ring
          rw [hh]
          exact neg_ne_zero.mpr (hxpar j k)
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · intro _ k
          exact hxpar i k
        · intro hij k
          exact hpar i j (fun h => hij (congrArg Fin.succ h)) k
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · intro h
          exact False.elim (h rfl)
        · intro _ l
          change orient2 x (p j) (q l) ≠ 0
          rw [orient2_reverse_edge]
          exact neg_ne_zero.mpr (hxcorn j l)
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · intro _ l
          exact hxcorn i l
        · intro hij l
          exact hcorn i j (fun h => hij (congrArg Fin.succ h)) l

end Zarankiewicz

end

end OAI
