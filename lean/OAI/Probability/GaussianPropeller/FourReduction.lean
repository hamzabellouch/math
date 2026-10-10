import OAI.Probability.GaussianPropeller.Geometry

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

namespace GaussianPropeller.Reduction
variable {d k : ℕ}

lemma residual_inner_base {z y:Space d} (hz:z≠0) :
    ⟪z,y⟫ = -residualCoefficient z y*‖z‖^2 := by
  unfold residualCoefficient
  field_simp

lemma residual_norm_sq {z y:Space d} (hz:z≠0) :
    ‖residualVector z y‖^2=‖y‖^2-(residualCoefficient z y)^2*‖z‖^2 := by
  rw [residualVector,norm_add_sq_real,real_inner_smul_right,norm_smul]
  rw [real_inner_comm z y,residual_inner_base hz]
  simp only [mul_pow,Real.norm_eq_abs,sq_abs]
  ring

lemma residual_inner {z y v:Space d} (hz:z≠0) :
    ⟪residualVector z y,residualVector z v⟫ =
      ⟪y,v⟫-residualCoefficient z y*residualCoefficient z v*‖z‖^2 := by
  simp only [residualVector,inner_add_left,inner_add_right,real_inner_smul_left,
    real_inner_smul_right,real_inner_self_eq_norm_sq]
  rw [real_inner_comm z y,residual_inner_base hz (y:=y),residual_inner_base hz (y:=v)]
  ring

lemma residual_coefficient_sum (z:Fin k→Space d) (hsum:∑ j,z j=0) (i:Fin k) (hi:z i≠0) :
    ∑ j ∈ Finset.univ.erase i,residualCoefficient (z i) (z j)=1 := by
  have hh : ∑ j ∈ Finset.univ.erase i,⟪z i,z j⟫ = -‖z i‖^2 := by
    have he := congrArg (fun y=>⟪z i,y⟫) hsum
    rw [inner_sum,inner_zero_right,← Finset.sum_erase_add _ _ (Finset.mem_univ i),
      real_inner_self_eq_norm_sq] at he
    linarith only [he]
  simp only [residualCoefficient,←Finset.sum_div,Finset.sum_neg_distrib,hh,neg_neg]
  exact div_self (pow_ne_zero _ (norm_ne_zero_iff.mpr hi))

lemma residual_sum (z:Fin k→Space d) (hsum:∑ j,z j=0) (i:Fin k) (hi:z i≠0) :
    ∑ j ∈ Finset.univ.erase i,residualVector (z i) (z j)=0 := by
  have hh : ∑ j ∈ Finset.univ.erase i,z j = -(z i) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at hsum
    exact eq_neg_of_add_eq_zero_left hsum
  simp only [residualVector,Finset.sum_add_distrib,←Finset.sum_smul,
    residual_coefficient_sum z hsum i hi,one_smul,hh,neg_add_cancel]

lemma residualCoefficient_smul {s:ℝ} (hs:0<s) (z y:Space d) :
    residualCoefficient (s•z) (s•y)=residualCoefficient z y := by
  simp only [residualCoefficient,real_inner_smul_left,real_inner_smul_right,norm_smul,
    Real.norm_eq_abs,abs_of_pos hs,mul_pow]
  field_simp

lemma residualVector_smul {s:ℝ} (hs:0<s) (z y:Space d) :
    residualVector (s•z) (s•y)=s•residualVector z y := by
  rw [residualVector,residualCoefficient_smul hs,residualVector,smul_add,smul_comm]

lemma normalized_tuple_pair [NeZero k] {A:Fin k→Set (Space d)} (hA:MinimalOptimal A)
    (hC:9/(8*Real.pi)<value A) (hall:∀ j,gaussian d (A j)≠0)
    {i j l:Fin k} (hij:i≠j) (hil:i≠l) :
    let z := fun j=>(Real.sqrt (value A))⁻¹•centroid (A j)
    let u := residualVector (z i) (z j)
    let v := residualVector (z i) (z l)
    ‖u‖^2*‖v‖^2-⟪u,v⟫^2 ≤ (3/Real.pi)^2*‖z i‖^2*
      (1+residualCoefficient (z i) (z j))^2*(1+residualCoefficient (z i) (z l))^2 := by
  dsimp only
  have hCp : 0<value A := (by positivity : (0:ℝ)<9/(8*Real.pi)).trans hC
  have hs : 0<(Real.sqrt (value A))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hCp)
  rw [residualVector_smul hs,residualVector_smul hs,residualCoefficient_smul hs,
    residualCoefficient_smul hs]
  have h := minimal_normalized_pair hA hC (hall i) (hall j) (hall l) hij hil
  dsimp only at h
  have hb : 0 ≤ (3/Real.pi)*(‖centroid (A i)‖/Real.sqrt (value A))*
      (1+residualCoefficient (centroid (A i)) (centroid (A j)))*
      (1+residualCoefficient (centroid (A i)) (centroid (A l))) := by
    have hj:=residualCoefficient_pos (negative_inner_of_minimal hA hij (hall i) (hall j))
    have hl:=residualCoefficient_pos (negative_inner_of_minimal hA hil (hall i) (hall l))
    positivity
  have hh := (sq_le_sq₀ (Real.sqrt_nonneg _) hb).mpr h
  rw [Real.sq_sqrt (Geometry.gram_det_nonneg _ _)] at hh
  convert hh using 1
  first | rfl | (simp only [norm_smul,Real.norm_eq_abs,abs_of_pos hs,mul_pow,div_pow]; ring)

end GaussianPropeller.Reduction

namespace GaussianPropeller.Reduction
variable {d k:ℕ}

lemma residual_self (z:Space d) : residualVector z z=0 := by
  by_cases hz:z=0
  · simp [hz,residualVector,residualCoefficient]
  · have hn:‖z‖^2≠0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hz)
    simp [residualVector,residualCoefficient,hn]

lemma residual_sum_all (z:Fin k→Space d) (hsum:∑ j,z j=0) (i:Fin k) (hi:z i≠0) :
    ∑ j,residualVector (z i) (z j)=0 := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),residual_sum z hsum i hi,residual_self,add_zero]

lemma residual_obtuse (z:Fin k→Space d) (hneg:Pairwise (fun j l=>⟪z j,z l⟫<0))
    (i:Fin k) (hi:z i≠0) {j l:Fin k} (hij:i≠j) (hil:i≠l) (hjl:j≠l) :
    ⟪residualVector (z i) (z j),residualVector (z i) (z l)⟫<0 := by
  rw [residual_inner hi]
  have ha:0<residualCoefficient (z i) (z j) := residualCoefficient_pos (hneg hij)
  have hb:0<residualCoefficient (z i) (z l) := residualCoefficient_pos (hneg hil)
  have hh : 0≤residualCoefficient (z i) (z j)*residualCoefficient (z i) (z l)*‖z i‖^2 := by positivity
  linarith only [hneg hjl,hh]

lemma residual_obtuse_all (z:Fin k→Space d) (hneg:Pairwise (fun j l=>⟪z j,z l⟫<0))
    (i:Fin k) (hi:z i≠0) : ∀ j l, j≠l →
    ⟪residualVector (z i) (z j),residualVector (z i) (z l)⟫≤0 := by
  intro j l hjl
  by_cases hij:i=j
  · subst j; simp [residual_self]
  by_cases hil:i=l
  · subst l; simp [residual_self]
  exact (residual_obtuse z hneg i hi hij hil hjl).le

lemma residual_coefficients_three (z:Fin k→Space d) (hsum:∑ j,z j=0)
    (hneg:Pairwise (fun j l=>⟪z j,z l⟫<0)) (i:Fin k) (hi:z i≠0)
    {j l q : Fin k} (hij:i≠j) (hil:i≠l) (hiq:i≠q) (hjl:j≠l) (hjq:j≠q) (hlq:l≠q) :
    residualCoefficient (z i) (z j)+residualCoefficient (z i) (z l)+
      residualCoefficient (z i) (z q)≤1 := by
  have hsub : ({j,l,q}:Finset (Fin k))⊆Finset.univ.erase i := by
    intro a ha
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl|rfl|rfl <;> simp [Ne.symm hij,Ne.symm hil,Ne.symm hiq]
  have h:=Finset.sum_le_sum_of_subset_of_nonneg hsub (f:=fun a=>residualCoefficient (z i) (z a))
    (fun a ha _ => (residualCoefficient_pos (hneg (Finset.mem_erase.mp ha).1.symm)).le)
  rw [residual_coefficient_sum z hsum i hi] at h
  simpa [Finset.sum_insert,Finset.sum_singleton,hjl,hjq,hlq,add_assoc] using h

lemma configuration_determinants (z:Fin k→Space d) (hsum:∑ j,z j=0)
    (hneg:Pairwise (fun j l=>⟪z j,z l⟫<0)) (i:Fin k) (hi:z i≠0)
    {j l q : Fin k} (hij:i≠j) (hil:i≠l) (hiq:i≠q) (hjl:j≠l) (hjq:j≠q) (hlq:l≠q)
    (hj:‖z q‖≤‖z j‖) (hl:‖z q‖≤‖z l‖) (hmin:‖z i‖≤‖z q‖)
    (hpair:∀ a b, i≠a → i≠b →
      ‖residualVector (z i) (z a)‖^2*‖residualVector (z i) (z b)‖^2-
      ⟪residualVector (z i) (z a),residualVector (z i) (z b)⟫^2≤
      (3/Real.pi)^2*‖z i‖^2*(1+residualCoefficient (z i) (z a))^2*
      (1+residualCoefficient (z i) (z b))^2) :
    (‖z q‖^2-‖z i‖^2)*(‖z j‖^2+‖z l‖^2-‖z q‖^2-2*‖z i‖^2)≤
      8*(3/Real.pi)^2*‖z i‖^2 ∧
    (3/2:ℝ)*(‖z q‖^2-‖z i‖^2)^2≤10*(3/Real.pi)^2*‖z i‖^2 := by
  let a:=residualCoefficient (z i) (z j)
  let b:=residualCoefficient (z i) (z l)
  let c:=residualCoefficient (z i) (z q)
  let u:=residualVector (z i) (z j)
  let v:=residualVector (z i) (z l)
  let w:=residualVector (z i) (z q)
  have ha:0<a := residualCoefficient_pos (hneg hij)
  have hb:0<b := residualCoefficient_pos (hneg hil)
  have hc:0<c := residualCoefficient_pos (hneg hiq)
  have hs:a+b+c≤1 := residual_coefficients_three z hsum hneg i hi hij hil hiq hjl hjq hlq
  have ha1:a^2≤1 := by nlinarith only [ha,hb,hc,hs]
  have hb1:b^2≤1 := by nlinarith only [ha,hb,hc,hs]
  have hc1:c^2≤1 := by nlinarith only [ha,hb,hc,hs]
  have hu:‖u‖^2=‖z j‖^2-a^2*‖z i‖^2 := residual_norm_sq hi
  have hv:‖v‖^2=‖z l‖^2-b^2*‖z i‖^2 := residual_norm_sq hi
  have hw:‖w‖^2=‖z q‖^2-c^2*‖z i‖^2 := residual_norm_sq hi
  have ht:‖z i‖^2≤‖z q‖^2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hmin
  have hrj:‖z q‖^2≤‖z j‖^2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hj
  have hrl:‖z q‖^2≤‖z l‖^2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hl
  have hla:=mul_le_mul_of_nonneg_right ha1 (sq_nonneg ‖z i‖)
  have hlb:=mul_le_mul_of_nonneg_right hb1 (sq_nonneg ‖z i‖)
  have hlc:=mul_le_mul_of_nonneg_right hc1 (sq_nonneg ‖z i‖)
  have hlu:‖z q‖^2-‖z i‖^2≤‖u‖^2 := by nlinarith only [hu,hla,hrj]
  have hlv:‖z q‖^2-‖z i‖^2≤‖v‖^2 := by nlinarith only [hv,hlb,hrl]
  have hlw:‖z q‖^2-‖z i‖^2≤‖w‖^2 := by nlinarith only [hw,hlc]
  have huw:⟪u,w⟫<0 := residual_obtuse z hneg i hi hij hiq hjq
  have hvw:⟪v,w⟫<0 := residual_obtuse z hneg i hi hil hiq hlq
  have huv:⟪u,v⟫<0 := residual_obtuse z hneg i hi hij hil hjl
  have hwu:⟪w,u⟫≤0 := by rw [real_inner_comm u w]; exact huw.le
  have hwv:⟪w,v⟫≤0 := by rw [real_inner_comm v w]; exact hvw.le
  have hrow := Geometry.row_two_le (fun a=>residualVector (z i) (z a))
    (residual_sum_all z hsum i hi) (residual_obtuse_all z hneg i hi) hjq.symm hlq.symm hjl
  constructor
  · exact Geometry.first_constraint_of_pair_bounds u v w ha.le hb.le hc.le hs ht hlw
      (by nlinarith only [hu,hv,hw,hla,hlb,mul_nonneg (sq_nonneg c) (sq_nonneg ‖z i‖)])
      hwu hwv hrow (hpair q j hiq hij) (hpair q l hiq hil)
  · have hu0:u≠0 := by intro he; rw [he,inner_zero_left] at huv; exact (lt_irrefl _ huv)
    have hv0:v≠0 := by intro he; rw [he,inner_zero_right] at huv; exact (lt_irrefl _ huv)
    have hw0:w≠0 := by intro he; rw [he,inner_zero_right] at huw; exact (lt_irrefl _ huw)
    exact Geometry.second_constraint_of_pair_bounds u v w hu0 hv0 hw0 ha.le hb.le hc.le hs
      ht hlu hlv hlw huv.le huw.le hvw.le (hpair j l hij hil) (hpair j q hij hiq) (hpair l q hil hiq)

end GaussianPropeller.Reduction

end OAI
