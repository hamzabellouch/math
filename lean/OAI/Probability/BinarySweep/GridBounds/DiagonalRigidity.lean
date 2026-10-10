import Mathlib
import OAI.Probability.BinarySweep.YoungTheory.YoungSpecht

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young

lemma diagonal_rigidity_aux {X : Type*} [Fintype X] (A B : X → ℝ)
    (r c : Equiv.Perm X) (hr : ∀ x, A (r x) = A x)
    (hc : ∀ x, B (c x) = B x)
    (hd : ∀ x, A ((r*c) x) + B ((r*c) x) = A x + B x) :
    ∀ x, A (c x) = A x := by
  have hq (x : X) : B ((r*c) x) = A x + B x - A (c x) := by
    have he := hd x
    change A (r (c x)) + _ = _ at he
    rw [hr] at he
    linarith
  have hxc : ∑ x, A (c x) * B x = ∑ x, A x * B x := by
    simpa only [hc] using Equiv.sum_comp c (fun x => A x * B x)
  have hxx : ∑ x, (A (c x))^2 = ∑ x, (A x)^2 :=
    Equiv.sum_comp c (fun x => (A x)^2)
  have hprod : ∑ x, (A (c x) * A x + A (c x) * B x - (A (c x))^2) =
      ∑ x, A x * B x := by
    calc
      _ = ∑ x, A ((r*c) x) * B ((r*c) x) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hq]
        change _ = A (r (c x)) * _
        rw [hr]
        ring
      _ = _ := Equiv.sum_comp (r*c) (fun x => A x * B x)
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hxc] at hprod
  have hcross : ∑ x, A (c x) * A x = ∑ x, (A (c x))^2 := by linarith
  have hzero : ∑ x, (A (c x) - A x)^2 = 0 := by
    calc
      _ = (∑ x, (A (c x))^2) - 2 * (∑ x, A (c x)*A x) + ∑ x, (A x)^2 := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = 0 := by rw [hcross, hxx]; ring
  intro x
  have hx : (A (c x) - A x)^2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => sq_nonneg (A (c x) - A x))).mp hzero x
      (Finset.mem_univ x)
  nlinarith [sq_nonneg (A (c x) - A x)]

def diagonal (μ : YoungDiagram) (x : Cell μ) : ℕ := row x + col x
abbrev diagonalStabilizer (μ : YoungDiagram) := fiberStabilizer (diagonal μ)
instance diagonalStabilizer_fintype (μ : YoungDiagram) : Fintype (diagonalStabilizer μ) :=
  Fintype.ofFinite _

lemma diagonal_row_column (μ : YoungDiagram) (r : rowStabilizer μ) (c : C μ)
    (hd : r.val*c.val ∈ diagonalStabilizer μ) : r = 1 ∧ c = 1 := by
  have he := diagonal_rigidity_aux (fun x : Cell μ => (row x : ℝ))
    (fun x => (col x : ℝ)) r.val c.val
    (fun x => congrArg Nat.cast (r.property x)) (fun x => congrArg Nat.cast (c.property x))
    (fun x => by exact_mod_cast hd x)
  have hc : c.val ∈ rowStabilizer μ := fun x => by exact_mod_cast he x
  have hi : c.val ∈ rowStabilizer μ ⊓ colStabilizer μ := ⟨hc,c.property⟩
  rw [row_col_intersection] at hi
  have hc1 : c = 1 := Subtype.ext hi
  have hr1 : r = 1 := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    apply Subtype.ext
    apply Prod.ext (r.property x)
    have hh := hd x
    rw [hc1] at hh
    change row (r.val x) + col (r.val x) = row x + col x at hh
    rw [r.property] at hh
    exact Nat.add_left_cancel hh
  exact ⟨hr1,hc1⟩

lemma diagonal_column_row (μ : YoungDiagram) (c : C μ) (r : rowStabilizer μ)
    (hd : c.val*r.val ∈ diagonalStabilizer μ) : c = 1 ∧ r = 1 := by
  have hi := (diagonalStabilizer μ).inv_mem hd
  have he : (r⁻¹).val * (c⁻¹).val ∈ diagonalStabilizer μ := by simpa using hi
  obtain ⟨hr,hc⟩ := diagonal_row_column μ r⁻¹ c⁻¹ he
  exact ⟨inv_eq_one.mp hc, inv_eq_one.mp hr⟩

variable (μ : YoungDiagram)

lemma diagonal_tabloid_eq (g h : diagonalStabilizer μ) (c : C μ) :
    tabloidOfPerm μ (g.val*c.val) = tabloidOfPerm μ h.val ↔ g = h ∧ c = 1 := by
  constructor
  · intro he
    let r : rowStabilizer μ := ⟨(g.val*c.val)⁻¹*h.val,
      (tabloidOfPerm_eq_iff μ _ _).mp he⟩
    have hr : c.val*r.val = g.val⁻¹*h.val := by dsimp only [r]; group
    have hd : c.val*r.val ∈ diagonalStabilizer μ := by
      rw [hr]
      exact (diagonalStabilizer μ).mul_mem ((diagonalStabilizer μ).inv_mem g.property) h.property
    obtain ⟨hc,hr1⟩ := diagonal_column_row μ c r hd
    refine ⟨?_,hc⟩
    rw [hc,hr1] at hr
    have hg : g.val = h.val := inv_mul_eq_one.mp (by simpa using hr.symm)
    exact Subtype.ext hg
  · rintro ⟨rfl,rfl⟩
    simp

lemma diagonal_poly_coefficient (g h : diagonalStabilizer μ) :
    tabloidRepresentation μ g.val (polytabloid μ) (tabloidOfPerm μ h.val) =
      if g = h then (1 : ℂ) else 0 := by
  rw [polytabloid, columnAnti_apply]
  simp_rw [rep_basis, smul_tabloidOfPerm, mul_one]
  rw [map_sum]
  simp_rw [map_smul, rep_basis, smul_tabloidOfPerm]
  simp only [Finset.sum_apply, Pi.smul_apply, tabloidBasis, Pi.single_apply]
  have he (c : C μ) : tabloidOfPerm μ h.val = tabloidOfPerm μ (g.val*c.val) ↔
      g = h ∧ c = 1 := (eq_comm).trans (diagonal_tabloid_eq μ g h c)
  simp only [he]
  by_cases hgh : g = h
  · simp [hgh]
  · simp [hgh]

theorem diagonal_polytabloids_independent : LinearIndependent ℂ
    (fun g : diagonalStabilizer μ => spechtRep μ g.val (spechtPoly μ)) := by
  apply LinearIndependent.of_comp (f := spechtInclude μ)
  rw [Fintype.linearIndependent_iff]
  intro a ha g
  have he := congrFun ha (tabloidOfPerm μ g.val)
  simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, Pi.zero_apply] at he
  simp_rw [spechtInclude_rep, spechtInclude_poly, diagonal_poly_coefficient] at he
  simpa using he

theorem diagonal_card_le_dimension : Fintype.card (diagonalStabilizer μ) ≤
    Module.finrank ℂ (SpechtSpace μ) := by
  let : Module.Finite ℂ (SpechtSpace μ) :=
    inferInstanceAs (FiniteDimensional ℂ (SpechtSpace μ))
  exact (diagonal_polytabloids_independent μ).fintype_card_le_finrank

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
variable {X Y : Type*} [Fintype X] [Fintype Y]

def fiberQuotientLabel (f : X → Y) :
    (Equiv.Perm X ⧸ fiberStabilizer f) → (X → Y) :=
  Quotient.lift (fun (g : Equiv.Perm X) => fun x => f (g⁻¹ x)) (by
    intro g h he
    have he' := (QuotientGroup.leftRel_apply.mp he : g⁻¹*h ∈ fiberStabilizer f)
    funext x
    have hh := he' (h⁻¹ x)
    simpa using hh)

omit [Fintype X] [Fintype Y] in
lemma fiberQuotientLabel_injective (f : X → Y) :
    Function.Injective (fiberQuotientLabel f) := by
  intro a b
  induction a using Quotient.inductionOn with | h g =>
    induction b using Quotient.inductionOn with | h h =>
      intro he
      apply Quotient.sound
      apply QuotientGroup.leftRel_apply.mpr
      intro x
      have hh := congrFun he (h x)
      simpa [fiberQuotientLabel] using hh

theorem factorial_le_colorings_mul_stabilizer (f : X → Y) :
    (Fintype.card X).factorial ≤
      (Fintype.card Y)^(Fintype.card X) * Nat.card (fiberStabilizer f) := by
  have hi : Nat.card (Equiv.Perm X ⧸ fiberStabilizer f) ≤ Nat.card (X → Y) :=
    Nat.card_le_card_of_injective (fiberQuotientLabel f) (fiberQuotientLabel_injective f)
  have he := Subgroup.card_eq_card_quotient_mul_card_subgroup (fiberStabilizer f)
  rw [Nat.card_eq_fintype_card, Fintype.card_perm] at he
  simp only [Nat.card_eq_fintype_card, Fintype.card_fun] at hi
  simp only [Nat.card_eq_fintype_card] at he ⊢
  rw [he]
  exact Nat.mul_le_mul_right _ hi

end BinaryCoordinateSweeps.Young

end

end OAI
