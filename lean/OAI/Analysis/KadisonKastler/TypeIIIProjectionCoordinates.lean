import OAI.Analysis.KadisonKastler.TypeIIIProjectionComparison
import OAI.Analysis.KadisonKastler.CuntzMatrices

namespace OAI

/-! # Two-by-two coordinates for a nontrivial type III projection -/

namespace KadisonKastler

noncomputable section

open Generator.Tracial

variable {A : Type*} [CStarAlgebra A]

theorem isometry_cross_eq_zero (v w : A) (hv : star v * v = 1)
    (hw : star w * w = 1) (horth : (v * star v) * (w * star w) = 0) :
    star v * w = 0 := by
  calc
    star v * w = (star v * v) * (star v * w) * (star w * w) := by rw [hv, hw]; simp
    _ = star v * ((v * star v) * (w * star w)) * w := by noncomm_ring
    _ = 0 := by rw [horth, mul_zero, zero_mul]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {N : VonNeumannAlgebra H}

theorem TypeIIIFactor.exists_projection_coordinates_of_projection_countability
    (hN : TypeIIIFactor N) (hFamilies : HasCountableProjectionFamilies N)
    (p : AlgebraProjection N) (hp : p.val ≠ 0) (hq : p.val ≠ 1) :
    ∃ S : CuntzFamily (Fin 2) H, (∀ i, S.entry i ∈ N) ∧
      S.entry 0 * star (S.entry 0) = p.val.val ∧
      S.entry 1 * star (S.entry 1) = 1 - p.val.val := by
  obtain ⟨v, hv, hvp⟩ :=
    hN.exists_isometry_onto_projection_of_projection_countability hFamilies p.val p.property hp
  have hq0 : 1 - p.val ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  obtain ⟨w, hw, hwq⟩ := hN.exists_isometry_onto_projection_of_projection_countability
    hFamilies (1 - p.val) p.property.one_sub hq0
  have hvw : star v * w = 0 := isometry_cross_eq_zero v w hv hw (by
    rw [hvp, hwq]; exact p.property.mul_one_sub_self)
  have hwv : star w * v = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hvw
  let e : Fin 2 → Algebra N := ![v, w]
  have he (i j : Fin 2) : star (e i) * e j = if i = j then 1 else 0 := by
    fin_cases i <;> fin_cases j <;> simp [e, hv, hw, hvw, hwv]
  let S : CuntzFamily (Fin 2) H := {
    entry i := (e i).val
    orthogonal i j := by
      have hh := congrArg Subtype.val (he i j)
      split_ifs with hij
      · simpa only [ite_eq_left hij, MulMemClass.coe_mul, StarMemClass.coe_star,
          OneMemClass.coe_one] using hh
      · simpa only [ite_eq_right hij, MulMemClass.coe_mul, StarMemClass.coe_star,
          ZeroMemClass.coe_zero] using hh
    total := by
      have hh : v * star v + w * star w = 1 := by rw [hvp, hwq]; abel
      simpa only [Fin.sum_univ_two, e, Matrix.cons_val_zero, Matrix.cons_val_one,
        AddMemClass.coe_add, MulMemClass.coe_mul, StarMemClass.coe_star, OneMemClass.coe_one]
        using congrArg Subtype.val hh }
  refine ⟨S, fun i => (e i).property, ?_, ?_⟩
  · exact congrArg Subtype.val hvp
  · exact congrArg Subtype.val hwq

theorem TypeIIIFactor.exists_projection_coordinates [TopologicalSpace.SeparableSpace H]
    (hN : TypeIIIFactor N) (p : AlgebraProjection N) (hp : p.val ≠ 0) (hq : p.val ≠ 1) :
    ∃ S : CuntzFamily (Fin 2) H, (∀ i, S.entry i ∈ N) ∧
      S.entry 0 * star (S.entry 0) = p.val.val ∧
      S.entry 1 * star (S.entry 1) = 1 - p.val.val :=
  hN.exists_projection_coordinates_of_projection_countability
    (fun _ p hp ho => countable_of_orthogonal_nonzero_projections p hp ho) p hp hq

end

end KadisonKastler

end OAI
