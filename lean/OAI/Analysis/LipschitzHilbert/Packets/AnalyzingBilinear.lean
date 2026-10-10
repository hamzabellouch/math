import OAI.Analysis.LipschitzHilbert.Packets.AnalyzingCoefficients

namespace OAI

/-! Finite synthesis/analysis duality with arbitrary synthesizing coefficients. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert

theorem finite_analyzing_pairing {X I K : Type*} [MeasurableSpace X] [Fintype K]
    (mu : Measure X) (area : I → ℝ) (wave : I → K → X → ℂ)
    (g : X → EuclideanSpace ℂ K) (c : I → EuclideanSpace ℂ K) (S : Finset I)
    (ha : ∀ i∈S, area i≠0)
    (hint : ∀ i∈S, ∀ k, Integrable (fun x => g x k*conj (wave i k x)) mu) :
    (∫ x, inner ℂ (∑ i∈S, WithLp.toLp 2 (fun k => c i k*wave i k x)) (g x) ∂mu)=
      ∑ i∈S, (area i:ℂ)*inner ℂ (c i) (analyzingCoefficient mu area wave g i) := by
  have hterm (i : I) (hi : i∈S) :
      (area i:ℂ)*inner ℂ (c i) (analyzingCoefficient mu area wave g i)=
        ∑ k, conj (c i k)*(∫ x, g x k*conj (wave i k x) ∂mu) := by
    simp only [PiLp.inner_apply,RCLike.inner_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    have harea : (area i:ℂ)*analyzingCoefficient mu area wave g i k=
        ∫ x, g x k*conj (wave i k x) ∂mu := by
      change (area i:ℂ)*(((area i)⁻¹:ℂ)*_)=_
      rw [←mul_assoc,mul_inv_cancel₀ (by exact_mod_cast ha i hi),one_mul]
    rw [←harea]
    ring
  have hInt (i : I) (hi : i∈S) (k : K) :
      Integrable (fun x => conj (c i k)*(g x k*conj (wave i k x))) mu :=
    (hint i hi k).const_mul _
  symm
  calc
    _ = ∑ i∈S, ∑ k, conj (c i k)*(∫ x, g x k*conj (wave i k x) ∂mu) :=
      Finset.sum_congr rfl hterm
    _ = ∫ x, ∑ i∈S, ∑ k, conj (c i k)*(g x k*conj (wave i k x)) ∂mu := by
      simp_rw [←integral_const_mul]
      rw [integral_finsetSum S (fun i hi => integrable_finsetSum _ (fun k _ => hInt i hi k))]
      apply Finset.sum_congr rfl
      intro i hi
      exact (integral_finsetSum Finset.univ (fun k _ => hInt i hi k)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [PiLp.inner_apply,RCLike.inner_apply,WithLp.ofLp_sum,Finset.sum_apply,
        map_sum,map_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      ring

end LipschitzHilbert

end

end OAI
