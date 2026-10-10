import Mathlib
import OAI.Analysis.Commutator.DyadicDimensionAdd
import OAI.Analysis.Commutator.ProjectionSumEquivalence

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma Link.equivalentSupports {M : VonNeumannAlgebra H} {e f : H →L[ℂ] H}
    (v : Link M e f) : Equivalent M v.initial v.final :=
  ⟨⟨v.val,v.mem,v.triple,le_rfl,le_rfl⟩,rfl,rfl⟩

end Kadison.PartialIsometryOrder

namespace Kadison.PartialIsometryOrder.DyadicPartition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [Nontrivial H]

variable (M : VonNeumannAlgebra H) (hfac : FactorCorner.IsFactor M)
  (hd : DiffuseProjection.HasNoMinimalProjections M) (hfin : IsFiniteAlgebra M)

include hfin in
lemma dimension_difference {e f : H →L[ℂ] H} (heM : e∈M) (hfM : f∈M)
    (he : IsStarProjection e) (hf : IsStarProjection f) (hfe : f≤e) :
    dimension M hfac hd (e-f)=dimension M hfac hd e-dimension M hfac hd f := by
  have hfe' := (hf.le_iff_mul_eq_left he).mp hfe
  have hp := hf.sub_of_mul_eq_left he hfe'
  have ho : f*(e-f)=0 := by rw [mul_sub,hfe',hf.isIdempotentElem.eq,sub_self]
  have h := dimension_orthogonal_add M hfac hd hfin hfM (M.sub_mem heM hfM) hf hp ho
  have ha : f+(e-f)=e := by abel
  rw [ha] at h
  linarith

omit [Nontrivial H] in
lemma dimension_mono {e f : H →L[ℂ] H} (heM : e∈M) (he : IsStarProjection e)
    (hef : e≤f) : dimension M hfac hd e≤dimension M hfac hd f :=
  dimension_mono_subEquivalent M hfac hd he (subEquivalent_of_le heM he hef)

include hfin in
lemma dimension_finset_sum {ι : Type*} (e : ι → H →L[ℂ] H)
    (heM : ∀ i,e i∈M) (he : ∀ i,IsStarProjection (e i))
    (hc : ∀ i j,i≠j → e i*e j=0) (s : Finset ι) :
    dimension M hfac hd (∑ i∈s,e i)=∑ i∈s,dimension M hfac hd (e i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using dimension_zero M hfac hd hfin
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi,
      dimension_orthogonal_add M hfac hd hfin (heM i) (M.sum_mem fun j _ => heM j)
        (he i) (orthogonal_sum_projection e he hc s) (orthogonal_mul_sum_eq_zero e hc s hi),ih]

include hfin in
lemma dimension_base (n : ℕ) :
    dimension M hfac hd (partition M hfac hd n).base=(1:ℝ)/2^n := by
  let D := partition M hfac hd n
  have hp : ∀ i,dimension M hfac hd (D.piece i)=dimension M hfac hd D.base := by
    intro i
    exact dimension_congr_equivalent M hfac hd (D.piece_projection i) D.base_projection
      (D.base_equiv_piece i).symm
  have hs := dimension_finset_sum M hfac hd hfin D.piece D.piece_mem D.piece_projection
    D.piece_cross Finset.univ
  change dimension M hfac hd (D.part Finset.univ)=_ at hs
  rw [D.part_univ,dimension_one] at hs
  simp only [hp,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hs
  change 1=(Fintype.card (Index n):ℝ)*dimension M hfac hd D.base at hs
  rw [cardinality,Nat.cast_pow,Nat.cast_ofNat] at hs
  apply (eq_div_iff (by positivity : (2:ℝ)^n≠0)).mpr
  simpa only [mul_comm] using hs.symm

section Separable

variable [TopologicalSpace.SeparableSpace H]

include hfin

lemma dimension_eq_zero_iff {e : H →L[ℂ] H} (heM : e∈M) (he : IsStarProjection e) :
    dimension M hfac hd e=0 ↔ e=0 := by
  constructor
  · intro h
    by_contra hn
    have hp := dimension_pos M hfac hd hfin heM he hn
    linarith
  · rintro rfl
    exact dimension_zero M hfac hd hfin

lemma subEquivalent_of_dimension_le {e f : H →L[ℂ] H} (heM : e∈M) (hfM : f∈M)
    (he : IsStarProjection e) (hf : IsStarProjection f)
    (h : dimension M hfac hd e≤dimension M hfac hd f) : SubEquivalent M e f := by
  rcases factor_subEquivalent_total M hfac heM hfM he hf with hcmp|hcmp
  · exact hcmp
  obtain ⟨v,hvi⟩ := hcmp
  have hqM : v.final∈M := M.mul_mem v.mem (M.star_mem' v.mem)
  have heq : dimension M hfac hd v.final=dimension M hfac hd f := by
    exact dimension_congr_equivalent M hfac hd v.final_projection hf
      (by simpa only [hvi] using v.equivalentSupports.symm)
  have hdiff := dimension_difference M hfac hd hfin heM hqM he v.final_projection v.target_le
  have hz : dimension M hfac hd (e-v.final)=0 := by
    have hn := dimension_nonneg M hfac hd (e-v.final)
    rw [heq] at hdiff
    linarith
  have heq' : v.final=e := sub_eq_zero.mp
    ((dimension_eq_zero_iff M hfac hd hfin (M.sub_mem heM hqM)
      (v.residual_target_projection he)).mp hz) |>.symm
  refine ⟨v.adjoint,?_⟩
  simpa only [Link.adjoint_initial] using heq'

lemma equivalent_of_dimension_eq {e f : H →L[ℂ] H} (heM : e∈M) (hfM : f∈M)
    (he : IsStarProjection e) (hf : IsStarProjection f)
    (h : dimension M hfac hd e=dimension M hfac hd f) : Equivalent M e f := by
  obtain ⟨v,hvi⟩ := subEquivalent_of_dimension_le M hfac hd hfin heM hfM he hf h.le
  have hqM : v.final∈M := M.mul_mem v.mem (M.star_mem' v.mem)
  have hq : dimension M hfac hd v.final=dimension M hfac hd e :=
    dimension_congr_equivalent M hfac hd v.final_projection he (by simpa only [hvi] using v.equivalentSupports.symm)
  have hz : dimension M hfac hd (f-v.final)=0 := by
    rw [dimension_difference M hfac hd hfin hfM hqM hf v.final_projection v.target_le,hq,h,sub_self]
  have hp := (dimension_eq_zero_iff M hfac hd hfin (M.sub_mem hfM hqM)
    (v.residual_target_projection hf)).mp hz
  exact ⟨v,hvi,(sub_eq_zero.mp hp).symm⟩

end Separable

end Kadison.PartialIsometryOrder.DyadicPartition

end

end
end

end OAI
