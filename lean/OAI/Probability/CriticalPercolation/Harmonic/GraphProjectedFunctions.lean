import Mathlib
import OAI.Probability.CriticalPercolation.Harmonic.GraphWalkEnergy
import OAI.Probability.CriticalPercolation.Harmonic.GraphWalkProbability

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
open HarmonicAnalysis

variable {X : Type*} (W : Geometry X)

def projectedFunction (n : ℕ) (t x : X) : ℝ :=
  inner ℝ (W.walkFeature n x-W.walkState n) (W.walkFeature n t-W.walkState n) /
    (4*(W.degree:ℝ)*W.walkEnergy (W.walkState n))
lemma exists_large_neighbor_gradient (hD : 0<W.degree) (n : ℕ) :
    ∃ t∈W.neighbors W.root, 4*W.walkEnergy (W.walkState n)≤‖W.walkFeature n t-W.walkState n‖^2 := by
  by_contra! h
  have hh := Finset.sum_lt_sum_of_nonempty (Finset.card_pos.mp hD) (fun t ht => h t ht)
  rw [W.walkEnergy_gradient] at hh
  simp only [Finset.sum_const,nsmul_eq_mul] at hh
  nlinarith
lemma projectedFunction_root (n : ℕ) (t : X) : W.projectedFunction n t W.root=0 := by
  simp [projectedFunction,walkState]
lemma projectedFunction_edge_bound [Infinite X] (n : ℕ) (t : X)
    (ht : t∈W.neighbors W.root) {x y : X} (hxy : W.graph.Adj x y) :
    |W.projectedFunction n t y-W.projectedFunction n t x|≤1 := by
  let q := 4*(W.degree:ℝ)*W.walkEnergy (W.walkState n)
  have hc : (0:ℝ)<W.degree := by exact_mod_cast W.degree_pos
  have hf := W.walkState_energy_pos n
  have hq : 0<q := by dsimp [q]; positivity
  have he : (W.walkFeature n y-W.walkState n)-(W.walkFeature n x-W.walkState n)=
      W.walkFeature n y-W.walkFeature n x := by abel
  unfold projectedFunction
  rw [←sub_div,←inner_sub_left,he,abs_div,abs_of_pos hq]
  apply (div_le_one hq).mpr
  calc
    _ ≤ ‖W.walkFeature n y-W.walkFeature n x‖*‖W.walkFeature n t-W.walkState n‖ := abs_real_inner_le_norm _ _
    _ ≤ Real.sqrt q*Real.sqrt q := mul_le_mul (W.feature_edge_bound W.degree_pos n hxy)
      (W.feature_neighbor_bound W.degree_pos n ht) (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = q := Real.mul_self_sqrt hq.le
lemma projectedFunction_length_bound [Infinite X] (n : ℕ) (t : X)
    (ht : t∈W.neighbors W.root) (x : X) : |W.projectedFunction n t x|≤(W.length x:ℝ) := by
  let q := 4*(W.degree:ℝ)*W.walkEnergy (W.walkState n)
  have hc : (0:ℝ)<W.degree := by exact_mod_cast W.degree_pos
  have hf := W.walkState_energy_pos n
  have hq : 0<q := by dsimp [q]; positivity
  unfold projectedFunction
  rw [abs_div,abs_of_pos hq]
  apply (div_le_iff₀ hq).mpr
  calc
    _ ≤ ‖W.walkFeature n x-W.walkState n‖*‖W.walkFeature n t-W.walkState n‖ := abs_real_inner_le_norm _ _
    _ ≤ ((W.length x:ℝ)*Real.sqrt q)*Real.sqrt q :=
      mul_le_mul (W.feature_ball_bound W.degree_pos n _ (W.mem_ball_length x))
        (W.feature_neighbor_bound W.degree_pos n ht) (norm_nonneg _) (by positivity)
    _ = (W.length x:ℝ)*q := by rw [mul_assoc,Real.mul_self_sqrt hq.le]
lemma projectedFunction_neighbor_lower [Infinite X] (n : ℕ) (t : X)
    (ht : 4*W.walkEnergy (W.walkState n)≤‖W.walkFeature n t-W.walkState n‖^2) :
    (W.degree:ℝ)⁻¹≤W.projectedFunction n t t := by
  have hc : (0:ℝ)<W.degree := by exact_mod_cast W.degree_pos
  have hf := W.walkState_energy_pos n
  have hq : 0<4*(W.degree:ℝ)*W.walkEnergy (W.walkState n) := by positivity
  unfold projectedFunction
  rw [real_inner_self_eq_norm_sq]
  apply (le_div_iff₀ hq).mpr
  have he : (W.degree:ℝ)⁻¹*(4*(W.degree:ℝ)*W.walkEnergy (W.walkState n))=4*W.walkEnergy (W.walkState n) := by field_simp
  rw [he]; exact ht
lemma sum_feature_displacement (n : ℕ) (x : X) :
    (∑ y∈W.neighbors x, (W.walkFeature n x-W.walkFeature n y))=
      (2*(W.degree:ℝ)) • (W.walkFeature n x-W.lazyWalk (W.walkFeature n x)) := by
  rw [Finset.sum_sub_distrib,Finset.sum_const,←Nat.cast_smul_eq_nsmul ℝ,
    W.neighbors_card,W.walkFeature_average,W.lazyWalk_apply]
  module
lemma projectedFunction_residual (n : ℕ) (t x : X) :
    (∑ y∈W.neighbors x, (W.projectedFunction n t x-W.projectedFunction n t y))=
      (2*(W.degree:ℝ))*inner ℝ (W.walkFeature n x-W.lazyWalk (W.walkFeature n x))
        (W.walkFeature n t-W.walkState n)/(4*(W.degree:ℝ)*W.walkEnergy (W.walkState n)) := by
  simp only [projectedFunction,←sub_div,←Finset.sum_div,←inner_sub_left,←sum_inner]
  have he : (∑ y∈W.neighbors x, (W.walkFeature n x-W.walkState n-(W.walkFeature n y-W.walkState n)))=
      ∑ y∈W.neighbors x, (W.walkFeature n x-W.walkFeature n y) := by
    apply Finset.sum_congr rfl; intros; abel
  rw [he,W.sum_feature_displacement,real_inner_smul_left (F:=FH X)]
lemma feature_residual_norm (n : ℕ) (x : X) :
    ‖W.walkFeature n x-W.lazyWalk (W.walkFeature n x)‖=‖W.walkState n-W.lazyWalk (W.walkState n)‖ := by
  obtain ⟨g,rfl⟩ := W.transitive W.root x
  rw [←W.transport_walkFeature,←W.transport_lazyWalk,←map_sub,LinearIsometryEquiv.norm_map]
lemma projectedFunction_residual_sq [Infinite X] (n : ℕ) (t : X)
    (ht : t∈W.neighbors W.root) (x : X) :
    (∑ y∈W.neighbors x, (W.projectedFunction n t x-W.projectedFunction n t y))^2≤
      (W.degree:ℝ)*‖W.walkState n-W.lazyWalk (W.walkState n)‖^2/W.walkEnergy (W.walkState n) := by
  have hc : (0:ℝ)<W.degree := by exact_mod_cast W.degree_pos
  have hf := W.walkState_energy_pos n
  have hgrad := (Finset.single_le_sum (f:=fun y => ‖W.walkFeature n y-W.walkState n‖^2)
    (fun y hy => sq_nonneg _) ht).trans_eq (W.walkEnergy_gradient n)
  have hi := abs_real_inner_le_norm (W.walkFeature n x-W.lazyWalk (W.walkFeature n x))
    (W.walkFeature n t-W.walkState n)
  rw [W.feature_residual_norm] at hi
  have hisq := pow_le_pow_left₀ (abs_nonneg _) hi 2
  rw [sq_abs,mul_pow] at hisq
  have hb := mul_le_mul_of_nonneg_left hgrad (sq_nonneg ‖W.walkState n-W.lazyWalk (W.walkState n)‖)
  rw [W.projectedFunction_residual,div_pow]
  apply (div_le_div_iff₀ (sq_pos_of_pos (show 0<4*(W.degree:ℝ)*W.walkEnergy (W.walkState n) by positivity)) hf).mpr
  have hm := mul_le_mul_of_nonneg_left (hisq.trans hb)
    (show 0≤4*(W.degree:ℝ)^2*W.walkEnergy (W.walkState n) by positivity)
  nlinarith only [hm]
end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
