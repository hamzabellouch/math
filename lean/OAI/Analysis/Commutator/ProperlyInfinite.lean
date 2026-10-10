import Mathlib
import OAI.Analysis.Commutator.MainMatrix
import OAI.Analysis.Commutator.RectangularColumn
import OAI.Analysis.Commutator.VonNeumannCStar

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace BigOperators

universe u

namespace Kadison

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma commutatorSeminorm_star_le (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K) :
    commutatorSeminorm P (star Y) ≤ commutatorSeminorm P Y := by
  apply csSup_le
  · exact ⟨0,0,zero_mem P,by simp,by simp⟩
  rintro r ⟨a,ha,hn,rfl⟩
  have hb := commutator_bound_unitball P Y (star_mem ha) (by simpa using hn)
  calc
    ‖star Y*a-a*star Y‖ = ‖star (star Y*a-a*star Y)‖ := (norm_star _).symm
    _ = ‖star a*Y-Y*star a‖ := by rw [star_sub,star_mul,star_mul,star_star]
    _ = ‖Y*star a-star a*Y‖ := norm_sub_rev _ _
    _ ≤ _ := hb

@[simp] lemma commutatorSeminorm_star (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K) :
    commutatorSeminorm P (star Y)=commutatorSeminorm P Y :=
  le_antisymm (commutatorSeminorm_star_le P Y)
    (by simpa using commutatorSeminorm_star_le P (star Y))

def operatorColumn (h : ℕ) (a : Fin h → (K →L[ℂ] K)) :
    K →L[ℂ] PiLp 2 (fun _ : Fin h => K) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin h => K)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi a)

def operatorRow (h : ℕ) (a : Fin h → (K →L[ℂ] K)) :
    PiLp 2 (fun _ : Fin h => K) →L[ℂ] K :=
  ∑ i, (a i).comp (PiLp.proj 2 (fun _ : Fin h => K) i)

omit [CompleteSpace K] in
@[simp] lemma operatorColumn_apply (h : ℕ) (a : Fin h → (K →L[ℂ] K)) (x : K) (i : Fin h) :
    operatorColumn h a x i=a i x := by simp [operatorColumn]

omit [CompleteSpace K] in
@[simp] lemma operatorRow_apply (h : ℕ) (a : Fin h → (K →L[ℂ] K))
    (x : PiLp 2 (fun _ : Fin h => K)) : operatorRow h a x=∑ i,a i (x i) := by
  simp [operatorRow]

lemma operatorRow_adjoint (h : ℕ) (a : Fin h → (K →L[ℂ] K)) :
    (operatorRow h a).adjoint=operatorColumn h (fun i => (a i).adjoint) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [PiLp.inner_apply,operatorColumn_apply,operatorRow_apply,inner_sum,
    ContinuousLinearMap.adjoint_inner_left]

lemma commutator_column_bound (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K)
    (h : ℕ) (a : Fin h → P) (ha : CyclicColumns.columnNorm a≤1) :
    ‖operatorColumn h (fun i => Y*(a i : K →L[ℂ] K)-(a i : K →L[ℂ] K)*Y)‖ ≤
      4*commutatorSeminorm P Y := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity [commutatorSeminorm_nonneg P Y])
  intro ξ
  let : StarOrderedRing P.toStarSubalgebra := VonNeumannCStar.starOrderedRing P
  have hb := RectangularColumn.column_bound P.toStarSubalgebra.subtype P.toStarSubalgebra.subtype
    (innerDerivation P Y) (innerDerivation_mul P Y) a ξ
  have he : operatorColumn h (fun i => Y*(a i : K →L[ℂ] K)-(a i : K →L[ℂ] K)*Y) ξ =
      WithLp.toLp 2 (fun i => innerDerivation P Y (a i) ξ) := by ext i; rfl
  rw [he]
  refine hb.trans ?_
  have hn := innerDerivation_norm_le P Y
  have hp := CyclicColumns.columnNorm_nonneg a
  have hm := (mul_le_mul hn ha hp (commutatorSeminorm_nonneg P Y)).trans_eq (mul_one _)
  calc
    (4*‖innerDerivation P Y‖)*CyclicColumns.columnNorm a*‖ξ‖ =
      4*(‖innerDerivation P Y‖*CyclicColumns.columnNorm a)*‖ξ‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (by norm_num)) (norm_nonneg ξ)

section Isometries

variable (P : VonNeumannAlgebra K) (h : ℕ) (v : Fin h → P)
  (hv : ∀ i j, star (v i)*v j=if i=j then 1 else 0)

include hv in
lemma isometry_range_sum_projection : IsStarProjection (∑ i,v i*star (v i)) := by
  refine ⟨?_,?_⟩
  · change (∑ i,v i*star (v i))*(∑ i,v i*star (v i))=∑ i,v i*star (v i)
    have he (i j : Fin h) : v i*star (v i)*(v j*star (v j))=
        if i=j then v i*star (v i) else 0 := by
      rw [show v i*star (v i)*(v j*star (v j))=v i*(star (v i)*v j)*star (v j) by noncomm_ring,hv]
      split_ifs with he
      · subst j; simp
      · simp
    simp only [Finset.sum_mul,Finset.mul_sum,he]
    simp
  · change star (∑ i,v i*star (v i))=∑ i,v i*star (v i)
    simp only [star_sum,star_mul,star_star]

include hv in
lemma isometry_star_columnNorm_le : CyclicColumns.columnNorm (fun i => star (v i))≤1 := by
  have hn := IsStarProjection.norm_le _ (isometry_range_sum_projection P h v hv)
  have he := CyclicColumns.columnNorm_sq (fun i => star (v i))
  simp only [star_star] at he
  nlinarith [CyclicColumns.columnNorm_nonneg (fun i => star (v i))]

include hv in
lemma isometry_row_adjoint_comp :
    (operatorRow h (fun i => (v i : K →L[ℂ] K))).adjoint.comp
      (operatorRow h (fun i => (v i : K →L[ℂ] K)))=ContinuousLinearMap.id ℂ _ := by
  rw [operatorRow_adjoint]
  ext x i
  change (operatorColumn h (fun j => (v j : K →L[ℂ] K).adjoint)
    (operatorRow h (fun j => (v j : K →L[ℂ] K)) x)) i=x i
  rw [operatorColumn_apply,operatorRow_apply,map_sum]
  have he (j : Fin h) : (v i : K →L[ℂ] K).adjoint ((v j : K →L[ℂ] K) (x j))=
      if i=j then x j else 0 := by
    by_cases hij : i=j
    · subst j
      have hh : (v i : K →L[ℂ] K).adjoint.comp (v i : K →L[ℂ] K)=ContinuousLinearMap.id ℂ K :=
        congrArg (fun a : P => (a:K →L[ℂ] K)) (by simpa using hv i i)
      simpa using congrArg (fun T : K →L[ℂ] K => T (x i)) hh
    · have hh : (v i : K →L[ℂ] K).adjoint.comp (v j : K →L[ℂ] K)=0 :=
        congrArg (fun a : P => (a:K →L[ℂ] K)) (by simpa only [ite_eq_right hij] using hv i j)
      simpa [hij] using congrArg (fun T : K →L[ℂ] K => T (x j)) hh
  simp only [he]
  simp

include hv in
lemma isometry_row_norm_le : ‖operatorRow h (fun i => (v i : K →L[ℂ] K))‖≤1 := by
  have he := (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mpr
    (isometry_row_adjoint_comp P h v hv)
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  rw [he x,one_mul]

end Isometries

end Kadison

end

end
end

end OAI
