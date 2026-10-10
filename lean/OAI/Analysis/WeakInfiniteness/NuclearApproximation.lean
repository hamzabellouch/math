import Mathlib
import OAI.Analysis.WeakInfiniteness.NuclearTensorMap

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra ComplexOrder

universe u v w

section

variable {A : Type u} {B : Type v} {C : Type w}
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C]

omit [PartialOrder A] [StarOrderedRing A] in
lemma tensorPolynomial_eq_sum (d : A × C →₀ ℂ) :
    tensorPolynomial d=∑ p ∈ d.support,minimalElementary (d p • p.1) p.2 := by
  change (∑ p ∈ d.support,d p • minimalElementary p.1 p.2)=_
  apply Finset.sum_congr rfl
  intro p _
  exact Subtype.ext (spatialElementary_smul_left (d p) p.1 p.2).symm

lemma norm_cpTensor_comp_le (φ : A →L[ℂ] B) (ψ : B →L[ℂ] A)
    (hφ : CompletelyPositive φ) (hψ : CompletelyPositive ψ)
    (hφn : ‖φ‖ ≤ 1) (hψn : ‖ψ‖ ≤ 1) (z : MinimalTensor A C) :
    ‖minimalCPMap ψ (minimalCPMap φ z)‖ ≤ 16*‖z‖ := by
  have hp := norm_minimalCPMap_le φ hφ z
  have hq := norm_minimalCPMap_le ψ hψ (minimalCPMap φ z)
  have h1 : ‖minimalCPMap φ z‖ ≤ 4*‖z‖ := hp.trans (by gcongr; linarith)
  have h2 : ‖minimalCPMap ψ (minimalCPMap φ z)‖ ≤ 4*‖minimalCPMap φ z‖ := hq.trans (by gcongr; linarith)
  linarith

lemma norm_cpTensor_sum_error_le {ι : Type*} (s : Finset ι) (a : ι → A) (c : ι → C)
    (φ : A →L[ℂ] B) (ψ : B →L[ℂ] A) (hφ : CompletelyPositive φ) (hψ : CompletelyPositive ψ)
    {δ : ℝ} (hδ : ∀ i ∈ s,‖ψ (φ (a i))-a i‖ ≤ δ) :
    ‖minimalCPMap ψ (minimalCPMap φ (∑ i ∈ s,minimalElementary (a i) (c i)))-
      ∑ i ∈ s,minimalElementary (a i) (c i)‖ ≤ δ*(∑ i ∈ s,‖c i‖) := by
  simp only [map_sum,minimalCPMap_elementary φ hφ,minimalCPMap_elementary ψ hψ]
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ s,‖minimalElementary (ψ (φ (a i))) (c i)-minimalElementary (a i) (c i)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s,δ*‖c i‖ := by
      apply Finset.sum_le_sum
      intro i hi
      have he : minimalElementary (ψ (φ (a i))) (c i)-minimalElementary (a i) (c i)=
          minimalElementary (ψ (φ (a i))-a i) (c i) := (map_sub (minimalElementaryLeftLinear (c i)) _ _).symm
      rw [he]
      exact (norm_spatialElementary_le _ _).trans (mul_le_mul_of_nonneg_right (hδ i hi) (norm_nonneg _))
    _ = _ := (Finset.mul_sum s (fun i => ‖c i‖) δ).symm

end

section

variable {A : Type u} {C : Type w}
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra C]

lemma nuclear_tensor_approximation (hA : Nuclear A) (z : MinimalTensor A C)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ,1 ≤ n ∧ ∃ φ : A →L[ℂ] CStarMatrix (Fin n) (Fin n) ℂ,
      ∃ ψ : CStarMatrix (Fin n) (Fin n) ℂ →L[ℂ] A,
      CompletelyPositive φ ∧ CompletelyPositive ψ ∧ ‖φ‖ ≤ 1 ∧ ‖ψ‖ ≤ 1 ∧
        ‖minimalCPMap ψ (minimalCPMap φ z)-z‖ < ε := by
  classical
  obtain ⟨d,hd⟩ := Metric.denseRange_iff.mp (tensorPolynomial_dense (A := A) (C := C)) z (ε/34) (by positivity)
  let p := tensorPolynomial d
  have hp : ‖z-p‖ < ε/34 := by simpa only [dist_eq_norm] using hd
  let a : A × C → A := fun t => d t • t.1
  let K : ℝ := ∑ t ∈ d.support,‖t.2‖
  have hK : 0 ≤ K := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  let δ := ε/(2*(K+1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨n,hn,φ,ψ,hφ,hψ,hφn,hψn,hap⟩ := hA (d.support.image a) δ hδ
  have herr : ‖minimalCPMap ψ (minimalCPMap φ p)-p‖ ≤ δ*K := by
    rw [show p=∑ t ∈ d.support,minimalElementary (a t) t.2 from tensorPolynomial_eq_sum d]
    exact norm_cpTensor_sum_error_le d.support a Prod.snd φ ψ hφ hψ
      (fun t ht => (hap (a t) (Finset.mem_image.mpr ⟨t,ht,rfl⟩)).le)
  have hδK : δ*K < ε/2 := by
    have hh : δ*(2*(K+1))=ε := div_mul_cancel₀ ε (by positivity)
    dsimp [δ] at hh ⊢
    nlinarith
  have ht : ‖minimalCPMap ψ (minimalCPMap φ z)-minimalCPMap ψ (minimalCPMap φ p)‖ ≤ 16*‖z-p‖ := by
    rw [← map_sub,← map_sub]
    exact norm_cpTensor_comp_le φ ψ hφ hψ hφn hψn (z-p)
  refine ⟨n,hn,φ,ψ,hφ,hψ,hφn,hψn,?_⟩
  have hc : ‖(minimalCPMap ψ (minimalCPMap φ z)-minimalCPMap ψ (minimalCPMap φ p))+
      (minimalCPMap ψ (minimalCPMap φ p)-p)+(p-z)‖ ≤
      ‖minimalCPMap ψ (minimalCPMap φ z)-minimalCPMap ψ (minimalCPMap φ p)‖+
      ‖minimalCPMap ψ (minimalCPMap φ p)-p‖+‖p-z‖ := norm_add₃_le
  have he : (minimalCPMap ψ (minimalCPMap φ z)-minimalCPMap ψ (minimalCPMap φ p))+
      (minimalCPMap ψ (minimalCPMap φ p)-p)+(p-z)=minimalCPMap ψ (minimalCPMap φ z)-z := by abel
  rw [he,norm_sub_rev p z] at hc
  linarith

end

end

end WeakPureInfiniteness
end

end OAI
