import Mathlib
import OAI.Analysis.Commutator.DyadicPartition
import OAI.Analysis.Commutator.PartitionRank
import OAI.Analysis.Commutator.DyadicRankStep

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

open Filter

namespace Kadison.PartialIsometryOrder.DyadicPartition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (hfac : FactorCorner.IsFactor M)
  (hd : DiffuseProjection.HasNoMinimalProjections M)

def lower (e : H →L[ℂ] H) (n : ℕ) : ℝ :=
  ((partition M hfac hd n).rank e : ℝ)/(2:ℝ)^n

def upper (e : H →L[ℂ] H) (n : ℕ) : ℝ :=
  (((partition M hfac hd n).rank e : ℝ)+1)/(2:ℝ)^n

def dimension (e : H →L[ℂ] H) : ℝ := sSup (Set.range (lower M hfac hd e))

lemma lower_nonneg (e : H →L[ℂ] H) (n : ℕ) : 0≤lower M hfac hd e n :=
  div_nonneg (Nat.cast_nonneg _) (by positivity)

lemma lower_le_one (e : H →L[ℂ] H) (n : ℕ) : lower M hfac hd e n≤1 := by
  apply (div_le_one (by positivity : (0:ℝ)<2^n)).mpr
  have h := (partition M hfac hd n).rank_le_card e
  rw [cardinality] at h
  exact_mod_cast h

lemma lower_le_upper (e : H →L[ℂ] H) (n : ℕ) : lower M hfac hd e n≤upper M hfac hd e n := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith

lemma rank_succ_lower {e : H →L[ℂ] H} (he : IsStarProjection e) (n : ℕ) :
    2*(partition M hfac hd n).rank e≤(partition M hfac hd (n+1)).rank e := by
  let D := partition M hfac hd n
  let p : ProjectionIn M := ⟨D.base,D.base_mem,D.base_projection⟩
  change 2*D.rank e≤(D.double (DyadicCuts.half M hfac hd p)
    (DyadicCuts.half_square M hfac hd p) (DyadicCuts.half_sum M hfac hd p)).rank e
  exact D.double_rank_lower (DyadicCuts.half M hfac hd p)
    (DyadicCuts.half_square M hfac hd p) (DyadicCuts.half_sum M hfac hd p) he

lemma rank_succ_upper {e : H →L[ℂ] H} (he : IsStarProjection e) (n : ℕ) :
    (partition M hfac hd (n+1)).rank e≤2*(partition M hfac hd n).rank e+1 := by
  let D := partition M hfac hd n
  let p : ProjectionIn M := ⟨D.base,D.base_mem,D.base_projection⟩
  change (D.double (DyadicCuts.half M hfac hd p)
    (DyadicCuts.half_square M hfac hd p) (DyadicCuts.half_sum M hfac hd p)).rank e≤2*D.rank e+1
  exact D.double_rank_upper (DyadicCuts.half M hfac hd p)
    (DyadicCuts.half_square M hfac hd p) (DyadicCuts.half_sum M hfac hd p) he

lemma lower_monotone {e : H →L[ℂ] H} (he : IsStarProjection e) : Monotone (lower M hfac hd e) := by
  apply monotone_nat_of_le_succ
  intro n
  have h : (2:ℝ)*(partition M hfac hd n).rank e≤(partition M hfac hd (n+1)).rank e :=
    by exact_mod_cast rank_succ_lower M hfac hd he n
  dsimp only [lower]
  rw [pow_succ]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [pow_pos (by norm_num : (0:ℝ)<2) n]

lemma upper_antitone {e : H →L[ℂ] H} (he : IsStarProjection e) : Antitone (upper M hfac hd e) := by
  apply antitone_nat_of_succ_le
  intro n
  have h : ((partition M hfac hd (n+1)).rank e:ℝ)≤2*(partition M hfac hd n).rank e+1 :=
    by exact_mod_cast rank_succ_upper M hfac hd he n
  dsimp only [upper]
  rw [pow_succ]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [pow_pos (by norm_num : (0:ℝ)<2) n]

lemma lower_le_dimension (e : H →L[ℂ] H) (n : ℕ) :
    lower M hfac hd e n≤dimension M hfac hd e :=
  le_csSup ⟨1,by rintro _ ⟨k,rfl⟩; exact lower_le_one M hfac hd e k⟩ ⟨n,rfl⟩

lemma dimension_le_upper {e : H →L[ℂ] H} (he : IsStarProjection e) (n : ℕ) :
    dimension M hfac hd e≤upper M hfac hd e n := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨k,rfl⟩
  rcases le_total k n with h|h
  · exact (lower_monotone M hfac hd he h).trans (lower_le_upper M hfac hd e n)
  · exact (lower_le_upper M hfac hd e k).trans (upper_antitone M hfac hd he h)

lemma dimension_nonneg (e : H →L[ℂ] H) : 0≤dimension M hfac hd e :=
  (lower_nonneg M hfac hd e 0).trans (lower_le_dimension M hfac hd e 0)

lemma dimension_le_one (e : H →L[ℂ] H) : dimension M hfac hd e≤1 := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨k,rfl⟩
  exact lower_le_one M hfac hd e k

lemma upper_sub_lower (e : H →L[ℂ] H) (n : ℕ) :
    upper M hfac hd e n-lower M hfac hd e n=(1:ℝ)/2^n := by
  dsimp only [upper,lower]
  rw [←sub_div]
  congr 1
  ring

lemma lower_tendsto_dimension {e : H →L[ℂ] H} (he : IsStarProjection e) :
    Tendsto (lower M hfac hd e) atTop (𝓝 (dimension M hfac hd e)) := by
  exact tendsto_atTop_ciSup (lower_monotone M hfac hd he)
    ⟨1,by rintro _ ⟨k,rfl⟩; exact lower_le_one M hfac hd e k⟩

lemma dimension_mono_subEquivalent {e f : H →L[ℂ] H} (he : IsStarProjection e)
    (h : SubEquivalent M e f) : dimension M hfac hd e≤dimension M hfac hd f := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨k,rfl⟩
  apply le_trans _ (lower_le_dimension M hfac hd f k)
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast (partition M hfac hd k).rank_mono_subEquivalent he h

lemma dimension_congr_equivalent {e f : H →L[ℂ] H}
    (he : IsStarProjection e) (hf : IsStarProjection f) (h : Equivalent M e f) :
    dimension M hfac hd e=dimension M hfac hd f := by
  apply le_antisymm
  · exact dimension_mono_subEquivalent M hfac hd he h.subEquivalent
  · exact dimension_mono_subEquivalent M hfac hd hf h.symm.subEquivalent

lemma dimension_one : dimension M hfac hd 1=1 := by
  apply le_antisymm (dimension_le_one M hfac hd 1)
  have h := lower_le_dimension M hfac hd 1 0
  simpa only [lower,EqualPartition.rank_one,cardinality,pow_zero,Nat.cast_one,div_one] using h

lemma dimension_zero [Nontrivial H] (hfin : IsFiniteAlgebra M) : dimension M hfac hd 0=0 := by
  apply le_antisymm _ (dimension_nonneg M hfac hd 0)
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨k,rfl⟩
  simp only [lower,EqualPartition.rank_zero _ hfin,Nat.cast_zero,zero_div,le_refl]

lemma dimension_pos [Nontrivial H] [TopologicalSpace.SeparableSpace H]
    (hfin : IsFiniteAlgebra M) {e : H →L[ℂ] H}
    (heM : e∈M) (he : IsStarProjection e) (hen : e≠0) : 0<dimension M hfac hd e := by
  obtain ⟨n,hn⟩ := exists_base_subEquivalent M hfac hd hfin heM he hen
  obtain ⟨i⟩ := (inferInstance : Nonempty (Index n))
  let D := partition M hfac hd n
  have hi : SubEquivalent M (D.piece i) e :=
    (D.base_equiv_piece i).symm.subEquivalent.trans (D.piece_projection i) D.base_projection hn
  have hk : 1≤D.rank e := by
    simpa only [Finset.card_singleton] using D.card_le_rank_of_subEquivalent {i}
      (by simpa only [D.part_singleton] using hi)
  apply lt_of_lt_of_le _ (lower_le_dimension M hfac hd e n)
  apply div_pos _ (by positivity)
  exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hk)

end Kadison.PartialIsometryOrder.DyadicPartition

end

end
end

end OAI
