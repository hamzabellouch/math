import Mathlib
import OAI.Analysis.Commutator.DyadicDimension
import OAI.Analysis.Commutator.OrthogonalRank

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

open Filter

namespace Kadison.PartialIsometryOrder.DyadicPartition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [Nontrivial H]

variable (M : VonNeumannAlgebra H) (hfac : FactorCorner.IsFactor M)
  (hd : DiffuseProjection.HasNoMinimalProjections M) (hfin : IsFiniteAlgebra M)

include hfin in
lemma lower_orthogonal_add_le {e f : H →L[ℂ] H} (heM : e∈M) (hfM : f∈M)
    (he : IsStarProjection e) (hf : IsStarProjection f) (hef : e*f=0) (n : ℕ) :
    lower M hfac hd e n+lower M hfac hd f n≤lower M hfac hd (e+f) n := by
  dsimp only [lower]
  rw [←add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast (partition M hfac hd n).orthogonal_rank_lower hfac hfin heM hfM he hf hef

include hfin in
lemma lower_orthogonal_add_upper {e f : H →L[ℂ] H} (heM : e∈M) (hfM : f∈M)
    (he : IsStarProjection e) (hf : IsStarProjection f) (hef : e*f=0) (n : ℕ) :
    lower M hfac hd (e+f) n≤lower M hfac hd e n+lower M hfac hd f n+2/(2:ℝ)^n := by
  dsimp only [lower]
  rw [←add_div,←add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast (partition M hfac hd n).orthogonal_rank_upper hfac hfin heM hfM he hf hef

lemma dyadic_error_tendsto : Tendsto (fun n : ℕ => (2:ℝ)/2^n) atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0≤(1/2:ℝ))
    (by norm_num : (1/2:ℝ)<1)).const_mul 2
  simpa only [div_pow,one_pow,mul_one_div,mul_zero] using h

include hfin in
theorem dimension_orthogonal_add {e f : H →L[ℂ] H} (heM : e∈M) (hfM : f∈M)
    (he : IsStarProjection e) (hf : IsStarProjection f) (hef : e*f=0) :
    dimension M hfac hd (e+f)=dimension M hfac hd e+dimension M hfac hd f := by
  have heT := lower_tendsto_dimension M hfac hd he
  have hfT := lower_tendsto_dimension M hfac hd hf
  have hefT := lower_tendsto_dimension M hfac hd (he.add hf hef)
  apply le_antisymm
  · have ht := (heT.add hfT).add dyadic_error_tendsto
    rw [add_zero] at ht
    exact le_of_tendsto_of_tendsto hefT ht (Eventually.of_forall
      (lower_orthogonal_add_upper M hfac hd hfin heM hfM he hf hef))
  · exact le_of_tendsto_of_tendsto (heT.add hfT) hefT (Eventually.of_forall
      (lower_orthogonal_add_le M hfac hd hfin heM hfM he hf hef))

include hfin in
lemma dimension_complement {e : H →L[ℂ] H} (heM : e∈M) (he : IsStarProjection e) :
    dimension M hfac hd (1-e)=1-dimension M hfac hd e := by
  have h := dimension_orthogonal_add M hfac hd hfin heM (M.sub_mem M.one_mem heM)
    he he.one_sub he.mul_one_sub_self
  have ha : e+(1-e)=1 := by abel
  rw [ha,dimension_one] at h
  linarith

end Kadison.PartialIsometryOrder.DyadicPartition

end

end
end

end OAI
