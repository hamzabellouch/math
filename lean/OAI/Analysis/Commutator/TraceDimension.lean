import Mathlib
import OAI.Analysis.Commutator.DiffuseProjection
import OAI.Analysis.Commutator.DyadicDimensionAdd
import OAI.Analysis.Commutator.FactorCorner
import OAI.Analysis.Commutator.VonNeumannCStar

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Kadison.TraceDimension

open PartialIsometryOrder PartialIsometryOrder.DyadicPartition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

variable (hτ : ∀ a b : M,τ (a*b)=τ (b*a))

include hτ

lemma trace_subEquivalent {e f : H →L[ℂ] H} (heM : e∈M) (hfM : f∈M)
    (h : SubEquivalent M e f) : (τ ⟨e,heM⟩).re≤(τ ⟨f,hfM⟩).re := by
  obtain ⟨v,hv⟩ := h
  let a : M := ⟨v.val,v.mem⟩
  have ha : star a*a=⟨e,heM⟩ := Subtype.ext hv
  have hb : a*star a≤⟨f,hfM⟩ := v.target_le
  calc
    _=(τ (star a*a)).re := by rw [ha]
    _=(τ (a*star a)).re := congrArg Complex.re (hτ (star a) a)
    _≤_ := (τ.monotone hb).1

lemma trace_equivalent {e f : H →L[ℂ] H} (heM : e∈M) (hfM : f∈M)
    (h : Equivalent M e f) : τ ⟨e,heM⟩=τ ⟨f,hfM⟩ := by
  obtain ⟨v,hvi,hvf⟩ := h
  let a : M := ⟨v.val,v.mem⟩
  have ha : star a*a=⟨e,heM⟩ := Subtype.ext hvi
  have hb : a*star a=⟨f,hfM⟩ := Subtype.ext hvf
  rw [←ha,←hb,hτ]

lemma partition_base_trace {ι : Type*} [Fintype ι] [Nonempty ι]
    (D : EqualPartition M ι) (hone : τ 1=1) :
    τ ⟨D.base,D.base_mem⟩=(Fintype.card ι:ℂ)⁻¹ := by
  have hpiece (i : ι) : τ ⟨D.piece i,D.piece_mem i⟩=τ ⟨D.base,D.base_mem⟩ :=
    (trace_equivalent M τ hτ D.base_mem (D.piece_mem i) (D.base_equiv_piece i)).symm
  have hsum : (∑ i, (⟨D.piece i,D.piece_mem i⟩:M))=1 := by
    apply Subtype.ext
    change M.toStarSubalgebra.subtype (∑ i,(⟨D.piece i,D.piece_mem i⟩:M))=1
    rw [map_sum]
    exact D.total
  have he := congrArg τ hsum
  rw [map_sum] at he
  simp_rw [hpiece] at he
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hone] at he
  have hn : (Fintype.card ι:ℂ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  apply mul_left_cancel₀ hn
  rw [mul_inv_cancel₀ hn]
  exact he

lemma partition_part_trace {ι : Type*} [Fintype ι] [Nonempty ι]
    (D : EqualPartition M ι) (hone : τ 1=1) (s : Finset ι) :
    (τ ⟨D.part s,D.part_mem s⟩).re=(s.card:ℝ)/(Fintype.card ι:ℝ) := by
  have hp : (⟨D.part s,D.part_mem s⟩:M)=∑ i∈s,(⟨D.piece i,D.piece_mem i⟩:M) := by
    apply Subtype.ext
    change D.part s=M.toStarSubalgebra.subtype _
    rw [map_sum]
    rfl
  rw [hp,map_sum]
  have he (i : ι) : τ ⟨D.piece i,D.piece_mem i⟩=(Fintype.card ι:ℂ)⁻¹ :=
    (trace_equivalent M τ hτ D.base_mem (D.piece_mem i) (D.base_equiv_piece i)).symm.trans
      (partition_base_trace M τ hτ D hone)
  simp_rw [he]
  simp only [Finset.sum_const,nsmul_eq_mul,←Complex.ofReal_natCast,
    ←Complex.ofReal_inv,←Complex.ofReal_mul,Complex.ofReal_re,div_eq_mul_inv]

variable (hfac : FactorCorner.IsFactor M) (hd : DiffuseProjection.HasNoMinimalProjections M)

lemma dimension_le_trace (hone : τ 1=1) {e : H →L[ℂ] H}
    (heM : e∈M) (he : IsStarProjection e) :
    dimension M hfac hd e≤(τ ⟨e,heM⟩).re := by
  apply le_of_tendsto (lower_tendsto_dimension M hfac hd he)
  apply Eventually.of_forall
  intro n
  let D := partition M hfac hd n
  obtain ⟨s,hs,hse⟩ := D.exists_rank e he
  have ht := trace_subEquivalent M τ hτ (D.part_mem s) heM hse
  rw [partition_part_trace M τ hτ D hone s,hs] at ht
  change ((D.rank e:ℝ)/(2:ℝ)^n)≤_
  simpa only [D,cardinality,Nat.cast_pow,Nat.cast_ofNat] using ht

theorem trace_projection_dimension [Nontrivial H] (hfin : IsFiniteAlgebra M)
    (hone : τ 1=1) {e : H →L[ℂ] H} (heM : e∈M) (he : IsStarProjection e) :
    (τ ⟨e,heM⟩).re=dimension M hfac hd e := by
  apply le_antisymm _ (dimension_le_trace M τ hτ hfac hd hone heM he)
  have hc := dimension_le_trace M τ hτ hfac hd hone (M.sub_mem M.one_mem heM) he.one_sub
  have hsub : (⟨1-e,M.sub_mem M.one_mem heM⟩:M)=1-⟨e,heM⟩ := rfl
  rw [hsub,map_sub,hone,Complex.sub_re,Complex.one_re,
    dimension_complement M hfac hd hfin heM he] at hc
  linarith

end Kadison.TraceDimension

end

end
end

end OAI
