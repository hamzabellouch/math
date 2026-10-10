import Mathlib
import OAI.Combinatorics.KMedian.Rounding.RationalTaperData

namespace OAI


                                    
section
namespace MetricKMedian.Taper
open Finset
variable {I J : Type} [Fintype I] [Fintype J]

 theorem image_univ_reindex [DecidableEq ℚ] (e : I ≃ J) (f : J → ℚ) :
    univ.image (fun i => f (e i))=univ.image f := by
  ext q
  simp only [mem_image,mem_univ,true_and]
  constructor
  · rintro ⟨i,rfl⟩; exact ⟨e i,rfl⟩
  · rintro ⟨j,rfl⟩; exact ⟨e.symm j,by rw [e.apply_symm_apply]⟩
 theorem upper_reindex (e : I ≃ J) (d : J → ℚ) : upper (fun i => d (e i))=upper d := by
  exact congrArg (fun q : ℚ => 1+q) (e.sum_comp (fun j => (d j)⁻¹))
 theorem breaks_reindex (e : I ≃ J) (P : ℚ) (d : J → ℚ) :
    breakpoints P (fun i => d (e i))=breakpoints P d := by
  unfold breakpoints
  rw [upper_reindex,image_univ_reindex e (fun j => (1-P)/d j),image_univ_reindex e (fun j => 1/d j)]
 theorem a_reindex (e : I ≃ J) (P t : ℚ) (d : J → ℚ) :
    A P (fun i => d (e i)) t=A P d t := e.sum_comp (fun j => aCoef P (d j) t)
 theorem b_reindex (e : I ≃ J) (P t : ℚ) (d : J → ℚ) :
    B P (fun i => d (e i)) t=B P d t := e.sum_comp (fun j => bCoef P (d j) t)
 theorem candidates_reindex (e : I ≃ J) (g P : ℚ) (d : J → ℚ) :
    candidates g P (fun i => d (e i))=candidates g P d := by
  simp only [candidates,breaks_reindex,a_reindex,b_reindex]
 theorem mass_reindex (e : I ≃ J) (g P t : ℚ) (d : J → ℚ) :
    rationalMass g P (fun i => d (e i)) t=rationalMass g P d t :=
  e.sum_comp (fun j => g*rationalMarginal P (d j) t)
 theorem roots_reindex (e : I ≃ J) (g P : ℚ) (d : J → ℚ) :
    rootCandidates g P (fun i => d (e i))=rootCandidates g P d := by
  simp only [rootCandidates,candidates_reindex,mass_reindex]
 theorem radius_reindex (e : I ≃ J) (g P : ℚ) (d : J → ℚ) :
    inverseRadius g P (fun i => d (e i))=inverseRadius g P d := by
  simp only [inverseRadius,roots_reindex]
 theorem colocated_reindex (e : I ≃ J) (g : ℚ) (d : J → ℚ) :
    rationalColocatedMass g (fun i => d (e i))=rationalColocatedMass g d :=
  e.sum_comp (fun j => if d j=0 then g else 0)

variable [LinearOrder I] [LinearOrder J]
omit [LinearOrder I] [LinearOrder J] in
 theorem zeros_reindex (e : I ≃ J) (d : J → ℚ) :
    (zeroSources (fun i => d (e i))).map e.toEmbedding=zeroSources d := by
  ext j
  simp only [mem_map_equiv,zeroSources,mem_filter,mem_univ,true_and,e.apply_symm_apply]
omit [Fintype I] [Fintype J] in
 theorem extend_reindex (e : I ≃o J) (own Z : Finset I) (Δ : ℕ) :
    extend (own.map e.toEquiv.toEmbedding) (Z.map e.toEquiv.toEmbedding) Δ=
      (extend own Z Δ).map e.toEquiv.toEmbedding := by
  have hs : ((Z\own).map e.toEquiv.toEmbedding).sort=
      ((Z\own).sort).map e := by
    exact (Finset.map_sort e.toEquiv.toEmbedding (Z\own) (·≤·) (·≤·)
      (fun _ _ _ _ => e.le_iff_le.symm)).symm
  have hm (xs : List I) : (xs.map e).toFinset=xs.toFinset.map e.toEquiv.toEmbedding := by
    ext j; simp only [List.mem_toFinset,List.mem_map,mem_map,Equiv.toEmbedding_apply]
    rfl
  simp only [extend,← Finset.map_sdiff,card_map,hs,← List.map_take,hm,Finset.map_union]
 theorem zeroMarginal_reindex (e : I ≃o J) (d : J → ℚ) (own : Finset I) (Δ : ℕ) (i : I) :
    zeroMarginal d (own.map e.toEquiv.toEmbedding) Δ (e i)=
      zeroMarginal (fun j => d (e j)) own Δ i := by
  rw [zeroMarginal,zeroSelection,← zeros_reindex e.toEquiv,extend_reindex]
  simp only [mem_map_equiv,zeroMarginal,zeroSelection]
  change (if e.toEquiv.symm (e.toEquiv i)∈extend own (zeroSources (fun j => d (e j))) Δ then (1:ℚ) else 0)=_
  rw [e.toEquiv.symm_apply_apply]
  rfl
 theorem source_reindex (e : I ≃o J) (g P : ℚ) (d : J → ℚ) (own : Finset I) (Δ : ℕ) (i : I) :
    sourceMarginals g P d (own.map e.toEquiv.toEmbedding) Δ (e i)=
      sourceMarginals g P (fun j => d (e j)) own Δ i := by
  have hc : rationalColocatedMass g (fun j => d (e j))=rationalColocatedMass g d := colocated_reindex e.toEquiv g d
  have hr : inverseRadius g P (fun j => d (e j))=inverseRadius g P d := radius_reindex e.toEquiv g P d
  simp only [sourceMarginals,hc,hr]
  split_ifs
  · exact zeroMarginal_reindex e d own Δ i
  · rfl
end MetricKMedian.Taper
end

end OAI
