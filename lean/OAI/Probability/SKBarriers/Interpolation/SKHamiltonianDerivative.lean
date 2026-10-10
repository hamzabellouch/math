import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.BlockFieldDerivative
import OAI.Probability.SKBarriers.Hierarchy.HierarchyEdgeVariation
import OAI.Probability.SKBarriers.Hierarchy.BlockDisorderDerivative
import OAI.Probability.SKBarriers.Interpolation.SKBlockCoordinates

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def skBlockRoot (N k : ℕ) (h : ℝ) (v : Fin (k+1) → ℝ) : ℝ :=
  hierarchyPressure (blockDimension (Fintype.card (Edge N)) N k)
    (blockMass (Fintype.card (Edge N)) N k)
    (affineLogPartition (fun _ => 0) (blockExponent (skInteraction N)
      (fun _ => h/Real.sqrt (N:ℝ)) v)) 0

theorem skBlock_disorder_differential {N k : ℕ} (hN : 0 < N)
    (h h' : ℝ) (v : Fin (k+1) → ℝ) :
    let D := Fintype.card (Edge N)
    let n := blockDimension D N k
    let a : Fin D → ℝ := fun _ => h/Real.sqrt (N:ℝ)
    let U := blockExponent (skInteraction N) a v
    fderiv ℝ (fun c : Fin n → ℝ => hierarchyPressure n (blockMass D N k)
      (affineLogPartition (fun _ => 0) (spinExponent n c (blockInteraction (skInteraction N)))) 0)
      (blockCoefficients a v) (blockCoefficients (N := N) (fun _ : Fin D => h'/Real.sqrt (N:ℝ)) (fun _ : Fin (k+1) => 0)) =
      (N:ℝ)*(h*h'/2)*(1-∑ l : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*
        hierarchyReplicaSecond n (blockMass D N k) U (fun s i => spin (s i)) (blockLevel D N k l)) := by
  dsimp only
  let D := Fintype.card (Edge N)
  let n := blockDimension D N k
  let a : Fin D → ℝ := fun _ => h/Real.sqrt (N:ℝ)
  let U := blockExponent (skInteraction N) a v
  let E := fun i : Fin D => fun l : Fin (k+1) =>
    ∫ z, (hierarchySpinMean n (blockMass D N k) U (fun s => spinMonomial s (skInteraction N i))
      (blockLevel D N k l) z)^2 ∂hierarchyPathLaw n (blockMass D N k) (affineLogPartition (fun _ => 0) U) 0
  let S := fun l : Fin (k+1) => hierarchyReplicaSecond n (blockMass D N k) U
    (fun s i => spin (s i)) (blockLevel D N k l)
  have hE (l : Fin (k+1)) : (∑ i : Fin D, (1-E i l)) = (N:ℝ)^2/2*(1-S l) := by
    have H := hierarchy_edge_variation hN n (blockMass D N k) U (blockLevel D N k l)
    have he : (∑ i : Fin D, (1-E i l)) = ∑ e : Edge N, (1-∫ z, (hierarchySpinMean n (blockMass D N k) U
      (fun s => spin (s e.val.1)*spin (s e.val.2)) (blockLevel D N k l) z)^2
        ∂hierarchyPathLaw n (blockMass D N k) (affineLogPartition (fun _ => 0) U) 0) := by
      dsimp only [E]
      simp only [spinMonomial_skInteraction]
      exact (Fintype.equivFin (Edge N)).symm.sum_comp (fun e : Edge N => (1-∫ z, (hierarchySpinMean n (blockMass D N k) U
        (fun s => spin (s e.val.1)*spin (s e.val.2)) (blockLevel D N k l) z)^2
          ∂hierarchyPathLaw n (blockMass D N k) (affineLogPartition (fun _ => 0) U) 0))
    rw [he]
    dsimp only [S]
    linarith [H]
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have sqN := Real.sq_sqrt (show (0:ℝ) ≤ N by positivity)
  have ha : h'/Real.sqrt (N:ℝ)*(h/Real.sqrt (N:ℝ)) = h*h'/(N:ℝ) := by
    rw [div_mul_div_comm,← pow_two,sqN]
    ring
  rw [linearMap_blockCoefficients]
  simp only [zero_mul,Finset.sum_const_zero,add_zero,blockPressure_disorder_coordinate]
  change (∑ i : Fin D, h'/Real.sqrt (N:ℝ)*(h/Real.sqrt (N:ℝ)*(1-∑ l : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*E i l))) =
    (N:ℝ)*(h*h'/2)*(1-∑ l : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*S l)
  simp only [← mul_assoc,ha]
  rw [← Finset.mul_sum,weighted_complement_sum _ (uniformAtom_sum k)]
  simp_rw [hE]
  have he : (∑ l : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*((N:ℝ)^2/2*(1-S l))) =
      (N:ℝ)^2/2*(1-∑ l : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*S l) := by
    rw [mul_sub,mul_one,Finset.mul_sum]
    simp only [mul_sub,mul_one,Finset.sum_sub_distrib]
    rw [← Finset.sum_mul,uniformAtom_sum,one_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he]
  field_simp
end SK.Analytic

end
end

end

end OAI
