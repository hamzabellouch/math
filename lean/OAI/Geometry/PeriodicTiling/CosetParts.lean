import OAI.Geometry.PeriodicTiling.PlaneLattices
import OAI.Geometry.PeriodicTiling.FiniteMasks
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Tactic.LinearCombination

namespace OAI

noncomputable section

namespace PeriodicTilingThree

open scoped BigOperators

theorem integerCombination_injective {e H : Plane} (hdet : planeDet e H ≠ 0) :
    Function.Injective (integerCombination e H) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ he
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  change a * e.1 + b * H.1 = c * e.1 + d * H.1 at hx
  change a * e.2 + b * H.2 = c * e.2 + d * H.2 at hy
  apply Prod.ext
  · have hz : planeDet e H * (a - c) = 0 := by
      dsimp [planeDet]
      linear_combination H.2 * hx - H.1 * hy
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hdet)
  · have hz : planeDet e H * (b - d) = 0 := by
      dsimp [planeDet]
      linear_combination e.1 * hy - e.2 * hx
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hdet)

def cosetPart (P : AddSubgroup Plane) (A : Set Plane) (c : Plane ⧸ P) : Set Plane :=
  {x | x ∈ A ∧ (x : Plane ⧸ P) = c}

theorem sum_cosetPart_indicator (P : AddSubgroup Plane) [Fintype (Plane ⧸ P)]
    (A : Set Plane) (x : Plane) :
    (∑ c : Plane ⧸ P, tileIndicator ℝ (cosetPart P A c) x) = tileIndicator ℝ A x := by
  classical
  by_cases hx : x ∈ A <;> simp [tileIndicator, cosetPart, hx]

private theorem mem_iff_of_tileIndicator_eq (A : Set Plane) (x y : Plane)
    (h : tileIndicator ℝ A x = tileIndicator ℝ A y) : x ∈ A ↔ y ∈ A := by
  classical
  by_cases hx : x ∈ A <;> by_cases hy : y ∈ A <;> simp_all [tileIndicator]

theorem cosetPart_period_of_coordinate_period (A : Set Plane) (e H x v : Plane)
    (hper : Function.Periodic
      (fun st : Plane => tileIndicator ℝ A (x + st.1 • e + st.2 • H)) v) :
    Period (cosetPart (integerSpan2 e H) A (x : Plane ⧸ integerSpan2 e H))
      (integerCombination e H v) := by
  classical
  let P := integerSpan2 e H
  let L := integerCombination e H
  have hvP : L v ∈ P := ⟨v, rfl⟩
  intro y
  have hclass : ((y + L v : Plane) : Plane ⧸ P) = (y : Plane ⧸ P) :=
    QuotientAddGroup.mk_add_of_mem y hvP
  change ((y + L v ∈ A) ∧ ((y + L v : Plane) : Plane ⧸ P) = (x : Plane ⧸ P)) ↔
    (y ∈ A ∧ (y : Plane ⧸ P) = (x : Plane ⧸ P))
  rw [hclass]
  by_cases hyclass : (y : Plane ⧸ P) = (x : Plane ⧸ P)
  · simp only [hyclass, and_true]
    have hdiff : y - x ∈ P := QuotientAddGroup.eq_iff_sub_mem.mp hyclass
    obtain ⟨st, hst⟩ := hdiff
    have hyrep : y = x + L st := by
      rw [hst]
      abel
    have hyshift : y + L v = x + L (st + v) := by
      rw [hyrep, map_add]
      abel
    apply mem_iff_of_tileIndicator_eq
    rw [hyshift, hyrep]
    simpa only [L, integerCombination, AddMonoidHom.coe_mk, ZeroHom.coe_mk, add_assoc] using hper st
  · simp only [hyclass, and_false]

theorem finite_periodic_parts_of_coset_periods {A : Set Plane}
    (e H : Plane) (hdet : planeDet e H ≠ 0)
    (hlocal : ∀ x : Plane, ∃ v : Plane, v ≠ 0 ∧ Function.Periodic
      (fun st : Plane => tileIndicator ℝ A (x + st.1 • e + st.2 • H)) v) :
    ∃ m : ℕ, ∃ parts : Fin m → Set Plane, ∃ w : Fin m → Plane,
      (∀ x, (∑ j, tileIndicator ℝ (parts j) x) = tileIndicator ℝ A x) ∧
      ∀ j, w j ≠ 0 ∧ Period (parts j) (w j) := by
  classical
  let P := integerSpan2 e H
  let : P.FiniteIndex := integerSpan2_finiteIndex e H hdet
  let : Fintype (Plane ⧸ P) := P.fintypeQuotientOfFiniteIndex
  have hex : ∀ c : Plane ⧸ P, ∃ w : Plane, w ≠ 0 ∧ Period (cosetPart P A c) w := by
    intro c
    let x : Plane := Quotient.out c
    have hx : (x : Plane ⧸ P) = c := Quotient.out_eq' c
    obtain ⟨v, hv, hper⟩ := hlocal x
    refine ⟨integerCombination e H v, ?_, ?_⟩
    · intro hz
      apply hv
      apply integerCombination_injective hdet
      simpa only [map_zero] using hz
    · rw [← hx]
      exact cosetPart_period_of_coordinate_period A e H x v hper
  choose w hw0 hwper using hex
  let eqv : Fin (Fintype.card (Plane ⧸ P)) ≃ (Plane ⧸ P) :=
    (Fintype.equivFin (Plane ⧸ P)).symm
  refine ⟨Fintype.card (Plane ⧸ P), (fun j => cosetPart P A (eqv j)),
    (fun j => w (eqv j)), ?_, ?_⟩
  · intro x
    rw [eqv.sum_comp (fun c => tileIndicator ℝ (cosetPart P A c) x)]
    exact sum_cosetPart_indicator P A x
  · intro j
    exact ⟨hw0 (eqv j), hwper (eqv j)⟩

end PeriodicTilingThree

end

end OAI
