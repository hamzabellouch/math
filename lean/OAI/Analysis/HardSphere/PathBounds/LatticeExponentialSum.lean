import Mathlib
import OAI.Analysis.HardSphere.Geometry.UnitCenter

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter SphericalCoordinates
open scoped ENNReal
noncomputable section

def latticeExponentialSum : ℝ := ∑' z : ℤ, Real.exp (-|(z:ℝ)|/3)

lemma latticeExponential_summable : Summable (fun z : ℤ ↦ Real.exp (-|(z:ℝ)|/3)) := by
  have h : Summable (fun n : ℕ ↦ Real.exp (-(n:ℝ)/3)) := by
    have hg := summable_geometric_of_abs_lt_one (r:=Real.exp (-1/3)) (by
      rw [abs_of_pos (Real.exp_pos _),Real.exp_lt_one_iff]; norm_num)
    convert hg using 1
    funext n
    rw [←Real.exp_nat_mul]
    congr 1
    ring
  apply Summable.of_nat_of_neg
  · simpa using h
  · simpa using h

lemma latticeExponentialSum_pos : 0<latticeExponentialSum := by
  have h := latticeExponential_summable.le_tsum 0 (fun _ _ ↦ (Real.exp_pos _).le)
  simp only [Int.cast_zero,abs_zero,neg_zero,zero_div,Real.exp_zero] at h
  exact lt_of_lt_of_le zero_lt_one h

def periodicLatticeIndex {K : ℕ} (L : Length) (x : AddCircle L.val) (v : Fin K) : ℤ :=
  (v.val:ℤ)-round (L.val⁻¹*((v.val:ℝ)+1/2-((AddCircle.equivIco L.val 0) x).val))*(K:ℤ)-
    ⌊((AddCircle.equivIco L.val 0) x).val-1/2⌋

lemma periodicLatticeIndex_injective {K : ℕ} {L : Length} (x : AddCircle L.val) :
    Function.Injective (periodicLatticeIndex (K:=K) L x) := by
  intro v w hvw
  have h := congrArg (fun z : ℤ ↦ (z+⌊((AddCircle.equivIco L.val 0) x).val-1/2⌋)%(K:ℤ)) hvw
  simp only [periodicLatticeIndex,sub_add_cancel,Int.sub_mul_emod_self_right] at h
  rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast v.isLt),
    Int.emod_eq_of_lt (by omega) (by exact_mod_cast w.isLt)] at h
  exact Fin.ext (by exact_mod_cast h)

lemma periodicLatticeIndex_bound {K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (x : AddCircle L.val) (v : Fin K) :
    |(periodicLatticeIndex L x v:ℝ)|≤dist (((v.val:ℝ)+1/2:ℝ):AddCircle L.val) x+1 := by
  let t := ((AddCircle.equivIco L.val 0) x).val
  let δ := t-1/2-(⌊t-1/2⌋:ℝ)
  have hδ0 : 0≤δ := Int.fract_nonneg (t-1/2)
  have hδ1 : δ<1 := Int.fract_lt_one (t-1/2)
  have hδ : |δ|≤1 := by rw [abs_of_nonneg hδ0]; exact hδ1.le
  have hd : dist (((v.val:ℝ)+1/2:ℝ):AddCircle L.val) x=
      |(periodicLatticeIndex L x v:ℝ)-δ| := by
    conv_lhs => rw [←(show (t:AddCircle L.val)=x from AddCircle.coe_equivIco)]
    rw [dist_eq_norm,←QuotientAddGroup.mk_sub,AddCircle.norm_eq]
    congr 1
    dsimp [periodicLatticeIndex,δ,t]
    push_cast
    rw [←hL]
    simp only [Int.fract]
    ring
  rw [hd]
  calc
    _ = |((periodicLatticeIndex L x v:ℝ)-δ)+δ| := by congr 1; ring
    _ ≤ |(periodicLatticeIndex L x v:ℝ)-δ|+|δ| := abs_add_le _ _
    _ ≤ _ := add_le_add le_rfl hδ

lemma circle_lattice_exponential_bound {K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (x : AddCircle L.val) :
    (∑ v : Fin K, Real.exp (-dist (((v.val:ℝ)+1/2:ℝ):AddCircle L.val) x/3))≤
      Real.exp (1/3)*latticeExponentialSum := by
  classical
  calc
    _ ≤ ∑ v : Fin K, Real.exp (1/3)*Real.exp (-|(periodicLatticeIndex L x v:ℝ)|/3) := by
      apply Finset.sum_le_sum
      intro v _
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h := periodicLatticeIndex_bound hL x v
      linarith only [h]
    _ = Real.exp (1/3)*∑ v : Fin K, Real.exp (-|(periodicLatticeIndex L x v:ℝ)|/3) := (Finset.mul_sum ..).symm
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      rw [←Finset.sum_image (f:=fun z : ℤ ↦ Real.exp (-|(z:ℝ)|/3)) (s:=Finset.univ) (periodicLatticeIndex_injective x).injOn]
      exact latticeExponential_summable.sum_le_tsum _ (fun _ _ ↦ (Real.exp_pos _).le)

lemma torus_exp_le_coordinate_exp (L : Length) (x y : Torus L) :
    Real.exp (-torusDistance L x y)≤Real.exp (-dist (x 0) (y 0)/3)*
      Real.exp (-dist (x 1) (y 1)/3)*Real.exp (-dist (x 2) (y 2)/3) := by
  rw [←Real.exp_add,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h0 := coordinate_distance_le L x y 0
  have h1 := coordinate_distance_le L x y 1
  have h2 := coordinate_distance_le L x y 2
  linarith only [h0,h1,h2]

theorem unitGrid_exponential_bound : ∃ C : ℝ, 0<C ∧
    ∀ (K : ℕ) (L : Length), L.val=(K:ℝ) → ∀ x : Torus L,
      (∑ v : CubeCell K, Real.exp (-torusDistance L (unitCenter L v) x))≤C := by
  let B := Real.exp (1/3)*latticeExponentialSum
  have hB : 0<B := mul_pos (Real.exp_pos _) latticeExponentialSum_pos
  refine ⟨B^3,pow_pos hB _,?_⟩
  intro K L hL x
  let f := fun (j : Fin 3) (v : Fin K) ↦ Real.exp (-dist (((v.val:ℝ)+1/2:ℝ):AddCircle L.val) (x j)/3)
  have hb (j : Fin 3) : (∑ v, f j v)≤B := circle_lattice_exponential_bound hL (x j)
  have hn (j : Fin 3) : 0≤∑ v, f j v := Finset.sum_nonneg (fun _ _ ↦ (Real.exp_pos _).le)
  calc
    _ ≤ ∑ v : CubeCell K, f 0 v.1*f 1 v.2.1*f 2 v.2.2 := by
      apply Finset.sum_le_sum
      intro v _
      exact torus_exp_le_coordinate_exp L (unitCenter L v) x
    _ = (∑ v, f 0 v)*(∑ v, f 1 v)*(∑ v, f 2 v) := by
      simp_rw [Fintype.sum_prod_type,←Finset.mul_sum,←Finset.sum_mul]
      rw [←Fintype.sum_mul_sum]
    _ ≤ B*B*B := mul_le_mul (mul_le_mul (hb 0) (hb 1) (hn 1) hB.le) (hb 2) (hn 2) (mul_nonneg hB.le hB.le)
    _ = B^3 := by ring

end
end HardSphere

namespace HardSphere
open MeasureTheory Set Filter SphericalCoordinates
open scoped ENNReal
noncomputable section

lemma unitGrid_site_exponential_bound : ∃ C : ℝ, 0<C ∧
    ∀ (K : ℕ) (L : Length), L.val=(K:ℝ) → ∀ (A : Finset (Torus L)), A.Nonempty →
      (∑ v : CubeCell K, Real.exp (-spatialSiteDistance L A (unitCenter L v)))≤C*(A.card:ℝ) := by
  obtain ⟨C,hC,h⟩ := unitGrid_exponential_bound
  refine ⟨C,hC,?_⟩
  intro K L hL A hA
  calc
    _ ≤ ∑ v : CubeCell K, ∑ w∈A, Real.exp (-torusDistance L (unitCenter L v) w) := by
      apply Finset.sum_le_sum
      intro v _
      obtain ⟨w,hw,he⟩ := spatialSiteDistance_attained L A hA (unitCenter L v)
      rw [he]
      exact Finset.single_le_sum (f:=fun w ↦ Real.exp (-torusDistance L (unitCenter L v) w)) (fun _ _ ↦ (Real.exp_pos _).le) hw
    _ = ∑ w∈A, ∑ v : CubeCell K, Real.exp (-torusDistance L (unitCenter L v) w) := Finset.sum_comm
    _ ≤ ∑ _w∈A, C := Finset.sum_le_sum (fun w _ ↦ h K L hL w)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul,mul_comm]

lemma unitOccupation_full_card {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (v : CubeCell K) (X : Configuration n L) :
    unitOccupation hL (fun _ ↦ True) v X=Fintype.card {i : Fin n // unitSite hL (X i)=v} := by
  classical
  apply Fintype.card_congr
  exact {
    toFun := fun i ↦ ⟨i.val.val,i.property⟩
    invFun := fun i ↦ ⟨⟨i.val,trivial⟩,i.property⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl }

lemma unitOccupation_sum_weight {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (a : CubeCell K → ℝ) (X : Configuration n L) :
    (∑ v : CubeCell K, a v*(unitOccupation hL (fun _ ↦ True) v X:ℝ))=
      ∑ i : Fin n, a (unitSite hL (X i)) := by
  classical
  rw [←Fintype.sum_fiberwise (fun i : Fin n ↦ unitSite hL (X i)) (fun i ↦ a (unitSite hL (X i)))]
  apply Finset.sum_congr rfl
  intro v _
  simp only [unitOccupation_full_card]
  have he : (fun i : {i : Fin n // unitSite hL (X i)=v} ↦ a (unitSite hL (X i.val)))=fun _ ↦ a v := by
    funext i
    rw [i.property]
  rw [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_comm]

lemma weightedSiteCount_le_cell {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (A : Finset (Torus L)) (hA : A.Nonempty) (X : Configuration n L) :
    weightedSiteCount L A X≤Real.exp 1*(∑ v : CubeCell K,
      Real.exp (-spatialSiteDistance L A (unitCenter L v))*(unitOccupation hL (fun _ ↦ True) v X:ℝ)) := by
  rw [unitOccupation_sum_weight,Finset.mul_sum,weightedSiteCount,ite_eq_left hA]
  apply Finset.sum_le_sum
  intro i _
  rw [←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hd := spatialSiteDistance_triangle L A (unitCenter L (unitSite hL (X i))) (X i)
  have hc := unitSite_dist_center hL (X i)
  rw [torusDistance_comm] at hd
  linarith only [hd,hc]

end
end HardSphere

end
end
end
end
end
end
end
end

end OAI
