import Mathlib
import OAI.Probability.SKBarriers.Interpolation.SKFiniteEndpoint
import OAI.Probability.SKBarriers.Scalar.ScalarCompression
import OAI.Probability.SKBarriers.Scalar.ScalarSpinRecursion
import OAI.Probability.SKBarriers.Interpolation.QuenchedEndpoint

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def quantileMass (k : ℕ) (j : Fin (k+1)) : ℝ := (j.val:ℝ)/((k+1:ℕ):ℝ)

theorem fieldIndex_strictMono (D N k : ℕ) (i : Fin N) :
    StrictMono (fun b => fieldIndex D N k b i) := by
  intro a b hab
  change D+a.val*N+i.val < D+b.val*N+i.val
  exact Nat.add_lt_add_right (Nat.add_lt_add_left
    (Nat.mul_lt_mul_of_pos_right hab (Nat.zero_lt_of_lt i.isLt)) D) i.val

theorem siteScalarCoefficients_at {D N k : ℕ} (v : Fin (k+1) → ℝ)
    (i : Fin N) (b : Fin (k+1)) :
    siteScalarCoefficients (D := D) v i (fieldIndex D N k b i) = v b := by
  have he (a : Fin (k+1)) : fieldIndex D N k a i = fieldIndex D N k b i ↔ a=b :=
    (fieldIndex_strictMono D N k i).injective.eq_iff
  simp only [siteScalarCoefficients,he,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem siteScalarCoefficients_off {D N k : ℕ} (v : Fin (k+1) → ℝ)
    (i : Fin N) (t : Fin (blockDimension D N k)) (ht : ∀ b, fieldIndex D N k b i ≠ t) :
    siteScalarCoefficients (D := D) v i t = 0 := by
  simp only [siteScalarCoefficients,ht,ite_false,Finset.sum_const_zero]

theorem hierarchyPressure_site_condensed {D N k : ℕ} (v : Fin (k+1) → ℝ) (i : Fin N) :
    hierarchyPressure (blockDimension D N k) (blockMass D N k)
      (siteLogPartition (D := D) v i) =
      fun _ => scalarHierarchy (k+1) (quantileMass k) v scalarSpinTerminal 0 := by
  rw [hierarchyPressure_site_scalar]
  have H := scalarHierarchy_compress (blockDimension D N k)
    (fun b => fieldIndex D N k b i) (fieldIndex_strictMono D N k i)
    (blockMass D N k) (siteScalarCoefficients (D := D) v i)
    (fun t ht => siteScalarCoefficients_off v i t ht) scalarSpinTerminal
  have hm : (blockMass D N k ∘ fun b => fieldIndex D N k b i) = quantileMass k := by
    funext b
    exact blockMass_at_field D N k b i
  have hv : (siteScalarCoefficients (D := D) v i ∘ fun b => fieldIndex D N k b i) = v := by
    funext b
    exact siteScalarCoefficients_at v i b
  rw [hm,hv] at H
  rw [H]

theorem skBlockRoot_zero_disorder_scalar {N k : ℕ} (hN : 0 < N) (v : Fin (k+1) → ℝ) :
    skBlockRoot N k 0 v = (N:ℝ)*scalarHierarchy (k+1) (quantileMass k) v scalarSpinTerminal 0 := by
  rw [skBlockRoot_zero_disorder_tensorizes hN]
  simp only [hierarchyPressure_site_condensed,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]

theorem skAdaptivePressure_terminal {N k : ℕ} (hN : 0 < N) (β : ℝ) (Q : Fin (k+1) → ℝ) :
    skAdaptivePressure N k β Q 1 =
      scalarHierarchy (k+1) (quantileMass k)
        (fun b => β*Real.sqrt (cumulativeGapMap k Q b)) scalarSpinTerminal 0 := by
  simp only [skAdaptivePressure,sub_self,Real.sqrt_zero,mul_zero,
    skBlockRoot_zero_disorder_scalar hN]
  exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hN.ne')

def extendedQuantileParisi (k : ℕ) (β : ℝ) (Q : Fin (k+1) → ℝ) : ℝ :=
  scalarHierarchy (k+1) (quantileMass k)
    (fun b => β*Real.sqrt (cumulativeGapMap k Q b)) scalarSpinTerminal 0 +
    (β^2/4)*(1-2*Q (Fin.last k)+∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(Q j)^2)

theorem exists_quenched_scalar_lower_bound {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    {β η : ℝ} (hβ : 0 < β) (hη : 0 < η)
    (hsmall : (k:ℝ)/Real.sqrt ((N:ℝ)*(β^2*η)) ≤ 1) :
    ∃ Q : Fin (k+1) → ℝ,
      (∀ j, η ≤ cumulativeGapMap k Q j) ∧
      (∀ j, Q j ≤ 1+((k+1:ℕ):ℝ)*η) ∧
      extendedQuantileParisi k β Q-
        (β^2/4)*(20*((k:ℝ)/Real.sqrt ((N:ℝ)*(β^2*η))+1/Real.sqrt (k:ℝ))+
          2*(((k+1:ℕ):ℝ)*η)*(1+((k+1:ℕ):ℝ)*η)+2*(((k+1:ℕ):ℝ)*η)) ≤
        (∫ J, logPartition β J ∂disorderLaw N)/(N:ℝ) := by
  obtain ⟨Q,hgap,hupper,H⟩ := exists_sk_finite_endpoint hN hk hβ hη hsmall
  refine ⟨Q,hgap,hupper,?_⟩
  simpa only [extendedQuantileParisi,skAdaptivePressure_terminal hN,skBlockRoot_zero_fields_eq] using H
end SK.Analytic

end
end

end

end OAI
