import OAI.NumberTheory.DukePrimeDegree.Dynamics.ConjugationOrbit

namespace OAI

/-!
# Changing the basepoint of a lattice orbit

Left translation on the orbit group induces the expected homeomorphism
between the two actual stabilizer quotients. It intertwines their right
actions and transports finite invariant measures without new hypotheses.
-/

noncomputable section
open Matrix Set MeasureTheory
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

def latticeOrbitBasepointHomeomorph {n : ℕ} (g : G n) (H : Subgroup (G n)) (h : H) :
    LatticeOrbitQuotient (g * h.val) H ≃ₜ LatticeOrbitQuotient g H where
  toFun := Quotient.map (fun a : H => h * a) (by
    intro a b hab
    change QuotientGroup.rightRel (pointOrbitStabilizer (g * h.val) H) a b at hab
    change QuotientGroup.rightRel (pointOrbitStabilizer g H) (h * a) (h * b)
    rw [QuotientGroup.rightRel_apply] at hab ⊢
    change (g * h.val) * (b.val * a.val⁻¹) * (g * h.val)⁻¹ ∈ integralGroup n at hab
    change g * ((h * b).val * (h * a).val⁻¹) * g⁻¹ ∈ integralGroup n
    simpa only [Subgroup.coe_mul, _root_.mul_inv_rev, mul_assoc] using hab)
  invFun := Quotient.map (fun a : H => h⁻¹ * a) (by
    intro a b hab
    change QuotientGroup.rightRel (pointOrbitStabilizer g H) a b at hab
    change QuotientGroup.rightRel (pointOrbitStabilizer (g * h.val) H) (h⁻¹ * a) (h⁻¹ * b)
    rw [QuotientGroup.rightRel_apply] at hab ⊢
    change g * (b.val * a.val⁻¹) * g⁻¹ ∈ integralGroup n at hab
    change (g * h.val) * ((h⁻¹ * b).val * (h⁻¹ * a).val⁻¹) *
      (g * h.val)⁻¹ ∈ integralGroup n
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, _root_.mul_inv_rev, inv_inv,
      mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left] using hab)
  left_inv := by
    intro x
    induction x using Quotient.inductionOn with
    | h a =>
      change Quotient.mk _ (h⁻¹ * (h * a)) = Quotient.mk _ a
      rw [inv_mul_cancel_left]
  right_inv := by
    intro x
    induction x using Quotient.inductionOn with
    | h a =>
      change Quotient.mk _ (h * (h⁻¹ * a)) = Quotient.mk _ a
      rw [mul_inv_cancel_left]
  continuous_toFun := by
    apply continuous_quot_lift
    exact continuous_quotient_mk'.comp (continuous_const.mul continuous_id)
  continuous_invFun := by
    apply continuous_quot_lift
    exact continuous_quotient_mk'.comp (continuous_const.mul continuous_id)

lemma latticeOrbitBasepointHomeomorph_rightAction {n : ℕ}
    (g : G n) (H : Subgroup (G n)) (h : H)
    (x : LatticeOrbitQuotient (g * h.val) H) (k : H) :
    latticeOrbitBasepointHomeomorph g H h (latticeOrbitRightAction (g * h.val) H x k) =
      latticeOrbitRightAction g H (latticeOrbitBasepointHomeomorph g H h x) k := by
  induction x using Quotient.inductionOn with
  | h a =>
    change Quotient.mk _ (h * (a * k)) = Quotient.mk _ ((h * a) * k)
    rw [mul_assoc]

lemma latticeOrbitBasepointHomeomorph_symm_rightAction {n : ℕ}
    (g : G n) (H : Subgroup (G n)) (h : H)
    (x : LatticeOrbitQuotient g H) (k : H) :
    (latticeOrbitBasepointHomeomorph g H h).symm (latticeOrbitRightAction g H x k) =
      latticeOrbitRightAction (g * h.val) H ((latticeOrbitBasepointHomeomorph g H h).symm x) k := by
  apply (latticeOrbitBasepointHomeomorph g H h).injective
  rw [Homeomorph.apply_symm_apply, latticeOrbitBasepointHomeomorph_rightAction,
    Homeomorph.apply_symm_apply]

/-- The transported measure has exactly the same right invariances. -/
theorem latticeOrbitBasepoint_measure_invariant {n : ℕ}
    (g : G n) (H : Subgroup (G n)) (h : H)
    (μ : Measure (LatticeOrbitQuotient g H))
    (hinv : ∀ k : H, μ.map (fun x => latticeOrbitRightAction g H x k) = μ) (k : H) :
    (μ.map (latticeOrbitBasepointHomeomorph g H h).symm).map
      (fun x => latticeOrbitRightAction (g * h.val) H x k) =
        μ.map (latticeOrbitBasepointHomeomorph g H h).symm := by
  let E := latticeOrbitBasepointHomeomorph g H h
  calc
    _ = μ.map ((fun x => latticeOrbitRightAction (g * h.val) H x k) ∘ E.symm) :=
      Measure.map_map (continuous_latticeOrbitRightAction _ H k).measurable E.symm.continuous.measurable
    _ = μ.map (E.symm ∘ fun x => latticeOrbitRightAction g H x k) := by
      congr 1
      funext x
      exact (latticeOrbitBasepointHomeomorph_symm_rightAction g H h x k).symm
    _ = (μ.map (fun x => latticeOrbitRightAction g H x k)).map E.symm :=
      (Measure.map_map E.symm.continuous.measurable
        (continuous_latticeOrbitRightAction g H k).measurable).symm
    _ = μ.map E.symm := by rw [hinv k]

end DukePrimeDegree

end

end OAI
