import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.RepulsionCross
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.NuclearRounding

namespace OAI

/-! The unit-nucleus field maps the full weak-H1 domain to L2. This also
justifies mixed singular nuclear forms after quadrature and rounding. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def pointChargePotential {m n : ℕ} (R : Fin m → Position) (x : Configuration n) : ℝ :=
  ∑ p : Fin n × Fin m, Coulomb.coulombKernel (Coulomb.position x p.1-R p.2)

theorem pointChargePotential_measurable {m n : ℕ} (R : Fin m → Position) :
    Measurable (@pointChargePotential m n R) := by
  apply Finset.measurable_sum
  intro p _
  have h := Coulomb.measurable_hardyCoulomb p.1 (Coulomb.nuclearHardyCoordinates p.1 (R p.2))
  change Measurable (fun x => Coulomb.hardyCoulomb p.1
    (Coulomb.nuclearHardyCoordinates p.1 (R p.2)) x) at h
  simpa only [Coulomb.hardyCoulomb_nuclear] using h

theorem pointChargePotential_square_bound {m n : ℕ} (R : Fin m → Position)
    (x : Configuration n) :
    pointChargePotential R x^2 ≤ ((n:ℝ)*m)*
      ∑ p : Fin n × Fin m, Coulomb.coulombKernel (Coulomb.position x p.1-R p.2)^2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n × Fin m))
    (fun p => Coulomb.coulombKernel (Coulomb.position x p.1-R p.2)) (fun _ => (1:ℝ))
  simp only [mul_one,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_prod,
    Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul] at h
  simpa only [pointChargePotential,mul_comm] using h

theorem pointChargePotential_spin_L2_bound {m n : ℕ} (R : Fin m → Position)
    (u : Coulomb.H1Vector n) (s : SpinConfiguration n) :
    Integrable (fun x => pointChargePotential R x^2*‖u.value s x‖^2) ∧
    (∫ x, pointChargePotential R x^2*‖u.value s x‖^2) ≤
      4*(n:ℝ)*(m:ℝ)^2*∑ i, ∑ k : Fin 3, ∫ x, ‖u.gradient s (i,k) x‖^2 := by
  let T (p : Fin n × Fin m) (x : Configuration n) :=
    Coulomb.coulombKernel (Coulomb.position x p.1-R p.2)^2*‖u.value s x‖^2
  have ht (p : Fin n × Fin m) := nuclear_hardy_square u s p.1 (R p.2)
  let F (x : Configuration n) := ((n:ℝ)*m)*∑ p, T p x
  have hF : Integrable F := (integrable_finsetSum _ (fun p _ => (ht p).1)).const_mul _
  have hdom (x : Configuration n) : pointChargePotential R x^2*‖u.value s x‖^2 ≤ F x := by
    have h := mul_le_mul_of_nonneg_right (pointChargePotential_square_bound R x) (sq_nonneg ‖u.value s x‖)
    simpa only [F,T,Finset.sum_mul,mul_assoc] using h
  have hmeas : AEStronglyMeasurable
      (fun x => pointChargePotential R x^2*‖u.value s x‖^2) volume :=
    ((pointChargePotential_measurable R).pow_const 2).aestronglyMeasurable.mul
      ((u.value_L2 s).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)).aestronglyMeasurable
  have hI : Integrable (fun x => pointChargePotential R x^2*‖u.value s x‖^2) := by
    apply hF.mono' hmeas
    exact Filter.Eventually.of_forall (fun x => by
      change |pointChargePotential R x^2*‖u.value s x‖^2| ≤ F x
      rw [abs_of_nonneg (by positivity)]
      exact hdom x)
  refine ⟨hI,(integral_mono hI hF hdom).trans ?_⟩
  change (∫ x, ((n:ℝ)*m)*∑ p, T p x) ≤ _
  rw [integral_const_mul,integral_finsetSum _ (fun p _ => (ht p).1)]
  calc
    _ ≤ ((n:ℝ)*m)*∑ p : Fin n × Fin m,
        4*∑ k : Fin 3, ∫ x, ‖u.gradient s (p.1,k) x‖^2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun p _ => (ht p).2)) (by positivity)
    _ = _ := by
      simp only [Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
        nsmul_eq_mul,← Finset.mul_sum]
      ring

theorem pointChargePotential_mul_memLp {m n : ℕ} (R : Fin m → Position)
    (u : Coulomb.H1Vector n) (s : SpinConfiguration n) :
    MemLp (fun x => (pointChargePotential R x:ℂ)*u.value s x) 2 := by
  apply (memLp_two_iff_integrable_sq_norm
    ((pointChargePotential_measurable R).complex_ofReal.aestronglyMeasurable.mul
      (u.value_L2 s).aestronglyMeasurable)).2
  simpa only [Pi.mul_apply,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs] using
    (pointChargePotential_spin_L2_bound R u s).1

theorem pointChargePotential_mul_norm_bound {m n : ℕ} (R : Fin m → Position)
    (u : Coulomb.H1Vector n) :
    (∑ s, ∫ x, ‖(pointChargePotential R x:ℂ)*u.value s x‖^2) ≤
      8*(n:ℝ)*(m:ℝ)^2*Coulomb.kinetic u := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun s _ =>
    (pointChargePotential_spin_L2_bound R u s).2)
  simp only [Coulomb.kinetic,Fintype.sum_prod_type,← Finset.mul_sum] at *
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
  convert h using 1
  ring

end ContinuumCoulomb

end

end OAI
