import Mathlib
import OAI.Analysis.HardSphere.Geometry.LocalizedNearLabels

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter SphericalCoordinates
open scoped ENNReal

def unitCenter {K : ℕ} (L : Length) (v : CubeCell K) : Torus L :=
  fun j ↦ ((pointFin ((v.1:ℝ)+1/2,(v.2.1:ℝ)+1/2,(v.2.2:ℝ)+1/2) j : ℝ) : AddCircle L.val)

lemma unitIndex_dist_center {K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (x : AddCircle L.val) :
    dist x ((((unitIndex hL x).val:ℝ)+1/2:ℝ) : AddCircle L.val)≤1/2 := by
  let t := ((AddCircle.equivIco L.val 0) x).val
  have ht : 0≤t := ((AddCircle.equivIco L.val 0) x).property.1
  have hlo := Nat.floor_le ht
  have hhi := Nat.lt_floor_add_one t
  have hab : |t-((⌊t⌋₊:ℝ)+1/2)|≤1/2 := by rw [abs_le]; constructor <;> linarith
  change dist x (((⌊t⌋₊:ℝ)+1/2:ℝ) : AddCircle L.val)≤1/2
  have he : (t:AddCircle L.val)=x := AddCircle.coe_equivIco
  rw [←he,dist_eq_norm,←QuotientAddGroup.mk_sub]
  exact (QuotientAddGroup.norm_mk_le_norm).trans (by simpa only [Real.norm_eq_abs] using hab)

lemma unitSite_dist_center {K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (x : Torus L) :
    torusDistance L x (unitCenter L (unitSite hL x))≤1 := by
  have hc (j : Fin 3) : dist (x j) (unitCenter L (unitSite hL x) j)≤1/2 := by
    fin_cases j
    · exact unitIndex_dist_center hL (x 0)
    · exact unitIndex_dist_center hL (x 1)
    · exact unitIndex_dist_center hL (x 2)
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by norm_num,?_⟩
  calc
    _ ≤ ∑ j : Fin 3, (1/2:ℝ)^2 := Finset.sum_le_sum (fun j _ ↦ pow_le_pow_left₀ dist_nonneg (hc j) 2)
    _ ≤ (1:ℝ)^2 := by norm_num

lemma unitOccupation_eq_full {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (p : Fin n → Prop) [DecidablePred p] (v : CubeCell K) (X : Configuration n L)
    (hp : ∀ i, unitSite hL (X i)=v → p i) :
    unitOccupation hL p v X=unitOccupation hL (fun _ ↦ True) v X := by
  classical
  apply Fintype.card_congr
  exact {
    toFun := fun i ↦ ⟨⟨i.val.val,trivial⟩,i.property⟩
    invFun := fun i ↦ ⟨⟨i.val.val,hp i.val.val i.property⟩,i.property⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl }

lemma spatialPartition_cell_occupation {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (A : Finset (Torus L)) (H : ℝ) (σ : Fin n → Bool) (X : Configuration n L)
    (hn : (productPartition n L (spatialInside L A H) (spatialOutside L A H) σ).toFun X≠0)
    (v : CubeCell K) (hv : spatialSiteDistance L A (unitCenter L v)+1≤H) :
    unitOccupation hL (fun i ↦ σ i=true) v X=unitOccupation hL (fun _ ↦ True) v X := by
  apply unitOccupation_eq_full
  intro i hi
  apply spatialPartition_forces_inside L A H σ X hn
  have hd := spatialSiteDistance_triangle L A (X i) (unitCenter L v)
  have hc := unitSite_dist_center hL (X i)
  rw [hi] at hc
  linarith only [hd,hc,hv]

end HardSphere

end

end OAI
