import OAI.NumberTheory.Ostmann.Tree.AffineEnergy

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {F : Type*} [Field F] [Fintype F]
variable [DecidableEq F]

def affineUnitPair (r s : Fˣ) : Fˣ × F :=
  ((s/r)^2, (s:F)-(s:F)^2/(r:F))

omit [Fintype F] [DecidableEq F] in
theorem affineUnitPair_coe (r s : Fˣ) :
    (((affineUnitPair r s).1:F), (affineUnitPair r s).2) = affinePair r s := by
  simp only [affineUnitPair, affinePair, Units.val_pow_eq_pow_val, Units.val_div_eq_div_val]

def affineUnitCoefficient (G : Fˣ → ℂ) (u : Fˣ) (b : F) : ℂ :=
  ∑ rs : Fˣ × Fˣ with affineUnitPair rs.1 rs.2 = (u,b), conj (G rs.1)*G rs.2

theorem affineUnitCoefficient_eq (G : Fˣ → ℂ) (u : Fˣ) (b : F) :
    affineUnitCoefficient G u b = affineCoefficient G ((u:F),b) := by
  unfold affineUnitCoefficient affineCoefficient
  apply Finset.sum_congr
  · apply Finset.filter_congr
    intro rs _
    constructor
    · intro h
      exact (affineUnitPair_coe rs.1 rs.2).symm.trans (congrArg (fun z : Fˣ × F => ((z.1:F),z.2)) h)
    · intro h
      apply Prod.ext
      · apply Units.ext
        exact congrArg Prod.fst ((affineUnitPair_coe rs.1 rs.2).trans h)
      · exact congrArg (fun z : F × F => z.2) ((affineUnitPair_coe rs.1 rs.2).trans h)
  · intro _ _
    rfl

theorem affineUnitCoefficient_energy (G : Fˣ → ℂ) :
    ∑ u : Fˣ, ∑ b : F, ‖affineUnitCoefficient G u b‖^2 ≤
      3*(∑ r : Fˣ, ‖G r‖^2)^2 := by
  simp only [affineUnitCoefficient_eq]
  rw [← Fintype.sum_prod_type (f := fun z : Fˣ × F => ‖affineCoefficient G ((z.1:F),z.2)‖^2)]
  apply le_trans _ (affineCoefficient_energy G)
  apply Finset.sum_le_sum_of_injOn (fun z : Fˣ × F => ((z.1:F),z.2))
  · intro x _ y _ h
    exact Prod.ext (Units.ext (congrArg Prod.fst h)) (congrArg (fun z : F × F => z.2) h)
  · exact Finset.subset_univ _
  · intro _ _
    exact le_rfl
  · intro _ _ _
    exact sq_nonneg _

theorem affineUnitCoefficient_action (G : Fˣ → ℂ) (f : F → ℂ) (t : F) :
    (∑ u : Fˣ, ∑ b : F, affineUnitCoefficient G u b * f ((u:F)*t+b)) =
      ∑ r : Fˣ, ∑ s : Fˣ, conj (G r)*G s *
        f (affineUnitSubstitution s (inverseAffineUnitSubstitution r t)) := by
  rw [← Fintype.sum_prod_type (f := fun z : Fˣ × F => affineUnitCoefficient G z.1 z.2 * f ((z.1:F)*t+z.2))]
  simp only [affineUnitCoefficient, Finset.sum_mul, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp only [ite_mul, zero_mul]
  have hsum (rs : Fˣ × Fˣ) :
      (∑ z : Fˣ × F, if affineUnitPair rs.1 rs.2=z then
        conj (G rs.1)*G rs.2 * f ((z.1:F)*t+z.2) else 0) =
      conj (G rs.1)*G rs.2 *
        f (affineUnitSubstitution rs.2 (inverseAffineUnitSubstitution rs.1 t)) := by
    rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _), affineUnitSubstitution_composition]
    have h := affineUnitPair_coe rs.1 rs.2
    rw [← congrArg Prod.fst h, ← congrArg Prod.snd h]
  simp_rw [hsum]
  rw [Fintype.sum_prod_type]

end
end Ostmann.FiniteField

end OAI
