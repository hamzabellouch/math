import Mathlib
import OAI.Analysis.Commutator.ProjectionFaithfulFunctional
import OAI.Analysis.Commutator.TraceDimension
import OAI.Analysis.Commutator.DyadicDimensionNormal

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.TraceDimension

open PartialIsometryOrder PartialIsometryOrder.DyadicPartition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [Nontrivial H] [TopologicalSpace.SeparableSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

variable (hτ : ∀ a b : M,τ (a*b)=τ (b*a))

variable (hfac : FactorCorner.IsFactor M) (hd : DiffuseProjection.HasNoMinimalProjections M)

variable (hfin : IsFiniteAlgebra M) (hone : τ 1=1)

include hτ hfac hd hfin hone

theorem positive_faithful (a : M) (ha : 0≤a) (hzero : τ a=0) : a=0 := by
  apply ProjectionFaithfulFunctional.positive_eq_zero_of_projection_faithful M τ _ a ha hzero
  intro p hp hτp
  have he := trace_projection_dimension M τ hτ hfac hd hfin hone p.property hp
  rw [hτp,Complex.zero_re] at he
  apply Subtype.ext
  exact (dimension_eq_zero_iff M hfac hd hfin p.property hp).mp he.symm

theorem faithful (a : M) (hzero : τ (star a*a)=0) : a=0 := by
  have he := positive_faithful M τ hτ hfac hd hfin hone (star a*a) (star_mul_self_nonneg a) hzero
  apply norm_eq_zero.mp
  have hn := congrArg norm he
  rw [CStarRing.norm_star_mul_self,norm_zero] at hn
  nlinarith [norm_nonneg a]

omit [TopologicalSpace.SeparableSpace H] in
lemma projection_value {p : H →L[ℂ] H} (hpM : p∈M) (hp : IsStarProjection p) :
    τ ⟨p,hpM⟩=(dimension M hfac hd p:ℝ) := by
  apply Complex.ext
  · exact trace_projection_dimension M τ hτ hfac hd hfin hone hpM hp
  · exact (τ.map_nonneg hp.nonneg).2.symm

theorem projection_tendsto
    (p : M) (hp : IsStarProjection (p:H →L[ℂ] H)) (P : ℕ → M)
    (hP : ∀ n,IsStarProjection (P n:H →L[ℂ] H))
    (hmono : Monotone (fun n => (P n:H →L[ℂ] H)))
    (hPp : ∀ n,(P n:H →L[ℂ] H)≤(p:H →L[ℂ] H))
    (hlim : ∀ x,Tendsto (fun n => (P n:H →L[ℂ] H) x) atTop (𝓝 ((p:H →L[ℂ] H) x))) :
    Tendsto (fun n => τ (P n)) atTop (𝓝 (τ p)) := by
  have he : ∀ n,τ (P n)=(dimension M hfac hd (P n):ℝ) := fun n =>
    projection_value M τ hτ hfac hd hfin hone (P n).property (hP n)
  simp_rw [he]
  rw [projection_value M τ hτ hfac hd hfin hone p.property hp]
  exact Complex.continuous_ofReal.continuousAt.tendsto.comp
    (dimension_tendsto_of_strong_increasing M hfac hd hfin p.property hp
      (fun n => (P n:H →L[ℂ] H)) (fun n => (P n).property) hP hmono hPp hlim)

end Kadison.TraceDimension

end

end
end

end OAI
