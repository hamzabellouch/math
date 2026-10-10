import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction
namespace ThreeParameters

variable (k : Type*) [Field k]

abbrev Poly := MvPolynomial (Fin 3) k

def squareIdeal : Ideal (Poly k) :=
  Ideal.span (Set.range fun i : Fin 3 => (MvPolynomial.X i : Poly k) ^ 2)

abbrev Ring := Poly k ⧸ squareIdeal k

def s (i : Fin 3) : Ring k := Ideal.Quotient.mk _ (MvPolynomial.X i)

def w : Ring k := s k 0 * s k 1 * s k 2

@[simp] theorem s_sq (i : Fin 3) : s k i ^ 2 = 0 := by
  rw [s, ← map_pow]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span ⟨i, rfl⟩

def topExponent : Fin 3 →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => 1)

@[simp] theorem topExponent_apply (i : Fin 3) : topExponent i = 1 := by
  simp [topExponent]

theorem topCoeff_ideal (p : Poly k) (hp : p ∈ squareIdeal k) :
    p.coeff topExponent = 0 := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hp
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_mul_monomial']
  have hi : ¬ Finsupp.single i 2 ≤ topExponent := by
    intro h
    have := h i
    simp only [Finsupp.single_eq_same, topExponent_apply] at this
    omega
  rw [ite_eq_right hi]

theorem w_ne_zero : w k ≠ 0 := by
  intro hw
  have hmem : (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 : Poly k)
      ∈ squareIdeal k := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_mul, s, w] using hw
  have hc := topCoeff_ideal k _ hmem
  have he : Finsupp.single (0 : Fin 3) 1 + Finsupp.single 1 1 +
      Finsupp.single 2 1 = topExponent := by
    ext i
    fin_cases i <;> norm_num [Finsupp.single_apply]
  have hprod : (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 : Poly k) =
      MvPolynomial.monomial topExponent 1 := by
    simp only [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul, he]
  rw [hprod, MvPolynomial.coeff_monomial, ite_eq_left rfl] at hc
  exact one_ne_zero hc

                                                                                
def augmentation : Ring k →+* k :=
  Ideal.Quotient.lift _ MvPolynomial.constantCoeff (by
    intro p hp
    obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hp
    simp)

@[simp] theorem augmentation_mk (p : Poly k) :
    augmentation k (Ideal.Quotient.mk _ p) = MvPolynomial.constantCoeff p := rfl

@[simp] theorem w_mul_s (i : Fin 3) : w k * s k i = 0 := by
  fin_cases i
  · calc
      w k * s k 0 = s k 0 ^ 2 * s k 1 * s k 2 := by dsimp [w]; ring
      _ = 0 := by simp
  · calc
      w k * s k 1 = s k 0 * s k 1 ^ 2 * s k 2 := by dsimp [w]; ring
      _ = 0 := by simp
  · calc
      w k * s k 2 = s k 0 * s k 1 * s k 2 ^ 2 := by dsimp [w]; ring
      _ = 0 := by simp

                                                                    
theorem w_mul (b : Ring k) : w k * b = augmentation k b • w k := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  induction p using MvPolynomial.induction_on with
  | C c =>
    simp only [augmentation_mk, MvPolynomial.constantCoeff_C]
    change w k * algebraMap k (Ring k) c = c • w k
    simpa only [mul_comm] using (Algebra.smul_def c (w k)).symm
  | add p q hp hq =>
    simp only [map_add, mul_add, augmentation_mk, hp, hq, add_smul]
  | mul_X p i hp =>
    simp only [map_mul, augmentation_mk, MvPolynomial.constantCoeff_X, mul_zero, zero_smul]
    change w k * (Ideal.Quotient.mk _ p * s k i) = 0
    rw [← mul_assoc, mul_right_comm, w_mul_s, zero_mul]

                                                                            
                                                                        
theorem residue_contradiction (b : Ring k) (hb : augmentation k b ≠ 0)
    (hwb : w k * b = 0) : False := by
  rw [w_mul] at hwb
  exact w_ne_zero k ((smul_eq_zero.mp hwb).resolve_left hb)

end ThreeParameters
end BoundaryOnly.FormalObstruction

namespace BoundaryOnly.FormalObstruction.ThreeParameters
variable (k : Type*) [Field k]

@[simp] theorem augmentation_s (i : Fin 3) : augmentation k (s k i) = 0 := by
  simp [s]

@[simp] theorem augmentation_algebraMap (a : k) :
    augmentation k (algebraMap k (Ring k) a) = a := by
  change MvPolynomial.constantCoeff (MvPolynomial.C a) = a
  simp

                                                                                 
theorem nilpotent_sub_augmentation (b : Ring k) :
    IsNilpotent (b - algebraMap k (Ring k) (augmentation k b)) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [augmentation_mk, MvPolynomial.constantCoeff_C]
    change IsNilpotent (algebraMap k (Ring k) c - algebraMap k (Ring k) c)
    simp
  | add p q hp hq =>
    simp only [map_add]
    rw [show (Ideal.Quotient.mk _ p + Ideal.Quotient.mk _ q) -
        (algebraMap k (Ring k) (augmentation k (Ideal.Quotient.mk _ p)) +
         algebraMap k (Ring k) (augmentation k (Ideal.Quotient.mk _ q))) =
        (Ideal.Quotient.mk _ p - algebraMap k (Ring k) (augmentation k (Ideal.Quotient.mk _ p))) +
        (Ideal.Quotient.mk _ q - algebraMap k (Ring k) (augmentation k (Ideal.Quotient.mk _ q))) by ring]
    exact (Commute.all _ _).isNilpotent_add hp hq
  | mul_X p i hp =>
    simp only [map_mul, augmentation_mk, MvPolynomial.constantCoeff_X, mul_zero, map_zero,
      sub_zero]
    exact (Commute.all _ _).isNilpotent_mul_left ⟨2, s_sq k i⟩

                                                              
theorem isUnit_of_augmentation_ne_zero (b : Ring k) (hb : augmentation k b ≠ 0) :
    IsUnit b := by
  have hunit : IsUnit (algebraMap k (Ring k) (augmentation k b)) :=
    (isUnit_iff_ne_zero.mpr hb).map _
  have hnil := nilpotent_sub_augmentation k b
  have h := hnil.isUnit_add_left_of_commute hunit (Commute.all _ _)
  simpa only [add_sub_cancel] using h

end BoundaryOnly.FormalObstruction.ThreeParameters

end

end OAI
