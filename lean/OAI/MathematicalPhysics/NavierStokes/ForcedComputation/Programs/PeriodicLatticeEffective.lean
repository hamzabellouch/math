import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.PeriodicLatticeTransform

namespace OAI

/-! Explicit derivative budgets and terminating programs for the transformed
periodic lattice field. Only rational coordinate and output arithmetic is added. -/

namespace PeriodicLattice.RapidTorus
local instance {n : ℕ} {A : Type*} [Encodable A] : Encodable (Fin n → A) := Encodable.finArrow
noncomputable section
open Quantitative TorusCalculus EffectiveFields CertifiedReal RecursiveArithmetic
open scoped ContDiff
local instance : Primcodable ℚ := ratPrimcodable
local instance : DecidablePred Input.WellFormed := Classical.decPred _
local instance : Primcodable ValidInput := Primcodable.subtype inputWellFormed

noncomputable def transformedCertificate {F : Input → VectorField} (h : FieldCertificate F) :
    FieldCertificate (fun d => transformedField (F d)) where
  budget p := 3 * h.budget p
  recursive := Primrec.nat_mul.comp (Primrec.const 3) h.recursive
  smooth d := transformedField_smooth (h.smooth d)
  estimate d hd w n J hn t ht q := by
    rw [transformedField_word (h.smooth d)]
    change (1 + t)^J * ‖transverseLinear (fieldWord w (F d) t (shift q))‖ ≤ _
    calc
      _ ≤ (1 + t)^J * (3 * ‖fieldWord w (F d) t (shift q)‖) :=
        mul_le_mul_of_nonneg_left (transverseLinear_bound _) (by positivity)
      _ = 3 * ((1 + t)^J * ‖fieldWord w (F d) t (shift q)‖) := by ring
      _ ≤ 3 * (h.budget (d,n,J) : ℝ) := by
        gcongr
        exact h.estimate d hd w n J hn t ht (shift q)
      _ = _ := by norm_num

def rationalShift (p : RationalPoint) : RationalPoint :=
  (p.1, fun i => p.2 i + if i = 1 then 1 / 4 else 0)

@[fun_prop] theorem rationalShift_computable : Computable rationalShift := by
  have hc (i : Fin 3) : Primrec (fun p : RationalPoint =>
      p.2 i + if i = 1 then (1 / 4 : ℚ) else 0) :=
    rat_add.comp ((Primrec.fin_app.comp Primrec.snd (Primrec.const i)).pair
      (Primrec.const (if i = 1 then (1 / 4 : ℚ) else 0)))
  have hcoords : Primrec (fun p : RationalPoint => fun i : Fin 3 =>
      p.2 i + if i = 1 then (1 / 4 : ℚ) else 0) :=
    Primrec.fin_curry.mpr (Primrec.fin_curry₁.mpr hc).swap
  exact (Primrec.fst.pair hcoords).to_comp

theorem rationalShift_vector (p : RationalPoint) :
    rationalVector (rationalShift p).2 = rationalVector p.2 + shiftVector := by
  ext i
  fin_cases i <;> simp [rationalShift, rationalVector, shiftVector, PiLp.add_apply]

theorem fieldValue_shifted {F : ScalarField} (p : RationalPoint) :
    fieldValue (shiftedField F) p = fieldValue F (rationalShift p) := by
  simp only [fieldValue, shiftedField, shift, rationalShift_vector, mk_add]
  rfl

theorem componentsEffective_transformed {F : Input → VectorField} (hF : ComponentsEffective F) :
    ComponentsEffective (fun d => transformedField (F d)) := by
  intro j
  have hshift : Effective (fun p : ValidInput × RationalPoint =>
      fieldValue (fun t q => F p.1.1 t q j) (rationalShift p.2)) :=
    (hF j).comp (Computable.fst.pair (rationalShift_computable.comp Computable.snd))
  have hscale := (constant (A := ValidInput × RationalPoint)
    (if j = 0 then -(1 / 2 : ℚ) else 1)).mul hshift
  apply hscale.congr
  intro p
  simp only [fieldValue, transformedField, transverseLinear_apply, shiftedField,
    shift, rationalShift_vector, mk_add]
  split_ifs <;> norm_num [rationalShift]

noncomputable def corollaryConstants (ν : ℝ) (N : ℕ) (hν : ‖ν‖ ≤ N)
    (d : Input) (r : ℕ) (α : MultiIndex) (J : ℕ) : ℕ :=
  (transformedCertificate velocityCertificate).mixedBudget d r α J +
    (transformedCertificate (forceCertificate ν N hν)).mixedBudget d r α J +
    (transformedCertificate (solenoidalForceCertificate ν N hν)).mixedBudget d r α J

theorem corollaryConstants_effective (ν : ℝ) (N : ℕ) (hν : ‖ν‖ ≤ N) :
    EffectiveConstants (corollaryConstants ν N hν) := by
  have hc : Primrec (fun p : Input × ℕ × MultiIndex × ℕ =>
      corollaryConstants ν N hν p.1 p.2.1 p.2.2.1 p.2.2.2) :=
    Primrec.nat_add.comp
      (Primrec.nat_add.comp (transformedCertificate velocityCertificate).mixedBudget_recursive
        (transformedCertificate (forceCertificate ν N hν)).mixedBudget_recursive)
      (transformedCertificate (solenoidalForceCertificate ν N hν)).mixedBudget_recursive
  obtain ⟨P,hP⟩ := program_of_computable hc.to_comp
  exact ⟨P,fun d _ r α J => hP (d,r,α,J)⟩

theorem corollaryConstants_bounds (ν : ℝ) (N : ℕ) (hν : ‖ν‖ ≤ N)
    (d : Input) (hd : d.WellFormed) :
    RapidPair (transformedField (FluidLift.velocity d))
      (transformedField (FluidLift.force ν d)) (corollaryConstants ν N hν d) ∧
    RapidPair (transformedField (FluidLift.velocity d))
      (transformedField (FluidLift.solenoidalForce ν d)) (corollaryConstants ν N hν d) := by
  have hpair {F G : Input → VectorField} (hf : FieldCertificate F) (hg : FieldCertificate G)
      {C : ℕ → MultiIndex → ℕ → ℕ}
      (hc : ∀ r α J, hf.mixedBudget d r α J + hg.mixedBudget d r α J ≤ C r α J) :
      RapidPair (F d) (G d) C := by
    intro r J α t ht
    calc
      _ ≤ (hf.mixedBudget d r α J : ℝ) / (1+t)^J +
          (hg.mixedBudget d r α J : ℝ) / (1+t)^J :=
        add_le_add (hf.sup_estimate d hd r α J ht) (hg.sup_estimate d hd r α J ht)
      _ = ((hf.mixedBudget d r α J + hg.mixedBudget d r α J : ℕ) : ℝ) / (1+t)^J := by
        rw [Nat.cast_add, add_div]
      _ ≤ _ := div_le_div_of_nonneg_right (Nat.cast_le.mpr (hc r α J)) (by positivity)
  constructor
  · exact hpair (transformedCertificate velocityCertificate)
      (transformedCertificate (forceCertificate ν N hν)) (fun _ _ _ => Nat.le_add_right _ _)
  · apply hpair (transformedCertificate velocityCertificate)
      (transformedCertificate (solenoidalForceCertificate ν N hν))
    intro r α J
    exact Nat.add_le_add_right (Nat.le_add_right _ _) _

end
end PeriodicLattice.RapidTorus

end OAI
