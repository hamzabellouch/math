import Mathlib
import OAI.Probability.SKBarriers.Interpolation.QuenchedEndpoint
import OAI.Probability.SKBarriers.Replicas.MatrixCovarianceAlgebra

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def matrixSKObservables {S : Type} (N d : ℕ) (β : ℝ) (e : S → Fin N → Config d) :
    Fin (Fintype.card (Edge N)) → S → ℝ := fun u s =>
  (β/Real.sqrt (N:ℝ))*∑ a,
    spin (e s ((Fintype.equivFin (Edge N)).symm u).val.1 a)*
      spin (e s ((Fintype.equivFin (Edge N)).symm u).val.2 a)

theorem matrixSKObservables_covariance {S : Type} {N d : ℕ} (hN : 0<N) (β : ℝ)
    (e : S → Fin N → Config d) (s t : S) :
    (∑ u, matrixSKObservables N d β e u s*matrixSKObservables N d β e u t)=
      ((N:ℝ)*β^2/2)*(∑ a, ∑ b,
        (replicaCrossOverlap N d (fun i a => spin (e s i a)) (fun i a => spin (e t i a)) a b)^2)-
          β^2*(d:ℝ)^2/2 := by
  have hNr : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr hN.ne'
  have hb : (β/Real.sqrt (N:ℝ))^2=β^2/(N:ℝ) := by
    rw [div_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
  have hp (a b : Fin d) :
      (∑ p : Edge N, (spin (e s p.val.1 a)*spin (e s p.val.2 a))*
        (spin (e t p.val.1 b)*spin (e t p.val.2 b)))=
      ((∑ i, spin (e s i a)*spin (e t i b))^2-(N:ℝ))/2 := by
    have H := sum_sq_eq_edges (fun i => spin (e s i a)*spin (e t i b))
    simp only [mul_pow,spin_sq,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at H
    have he (p : Edge N) :
        (spin (e s p.val.1 a)*spin (e t p.val.1 b))*(spin (e s p.val.2 a)*spin (e t p.val.2 b))=
        (spin (e s p.val.1 a)*spin (e s p.val.2 a))*(spin (e t p.val.1 b)*spin (e t p.val.2 b)) := by ring
    simp_rw [he] at H
    linarith
  simp only [matrixSKObservables]
  rw [← (Fintype.equivFin (Edge N)).sum_comp]
  simp only [Equiv.symm_apply_apply]
  have he (p : Edge N) :
    (β/Real.sqrt (N:ℝ)*(∑ a, spin (e s p.val.1 a)*spin (e s p.val.2 a)))*
      (β/Real.sqrt (N:ℝ)*(∑ b, spin (e t p.val.1 b)*spin (e t p.val.2 b)))=
        (β^2/(N:ℝ))*((∑ a, spin (e s p.val.1 a)*spin (e s p.val.2 a))*
          (∑ b, spin (e t p.val.1 b)*spin (e t p.val.2 b))) := by rw [← hb]; ring
  simp_rw [he,← Finset.mul_sum,Fintype.sum_mul_sum]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ) (f:=fun (p : Edge N) (b : Fin d) => _)]
  simp_rw [hp,sub_div,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  simp only [replicaCrossOverlap,div_pow,← Finset.sum_div]
  field_simp

attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem matrixSKObservables_exponent {S : Type} (N d : ℕ) (β : ℝ)
    (e : S → Fin N → Config d) (s : S) (z : ParameterSpace (Fintype.card (Edge N))) :
    coordinateLinear (Fintype.card (Edge N)) (fun u => matrixSKObservables N d β e u s) z=
      β*∑ a, hamiltonian (enumeratedDisorder N z) (fun i => e s i a) := by
  simp only [coordinateLinear_apply,matrixSKObservables,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  convert spinExponent_sk_eq N β (fun i => e s i a) z using 1
  simp only [spinExponent,coordinateLinear_apply,spinMonomial_skInteraction]

end SK.Analytic

end
end

end OAI
