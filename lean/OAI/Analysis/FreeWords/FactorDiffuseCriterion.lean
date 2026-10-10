import Mathlib
import OAI.Analysis.FreeWords.ProjectionSmall
import OAI.Analysis.FreeWords.ProjectionStructure

namespace OAI

noncomputable section

namespace KKVariableUltra

open KKTraceTransfer KKFreeLiftFrontier KKProjectionSupport

open scoped ComplexOrder

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem factor_diffuse_of_small_projections (M : VonNeumannAlgebra H)
    (τ : FaithfulNormalTrace M) (hF : IsFactor M)
    (hsmall : ∀ ε : ℝ, 0<ε → ∃ p : ConcreteAlgebra M,
      IsStarProjection p ∧ 0<(τ.map p).re ∧ (τ.map p).re<ε) : IsDiffuse M := by
  intro q hq hq0
  obtain ⟨p,hp,hp0,hpq⟩ := hsmall (τ.map q).re (trace_projection_pos τ hq hq0)
  obtain ⟨v,hv,hvp,hqv,he⟩ := projection_comparable_by_trace M τ hF p q hp hq
  have hpi := initial_bound hp hvp
  have hqi := final_bound hq hqv
  have htr : τ.map (star v*v)=τ.map (v*star v) := τ.tracial _ _
  have hle : (τ.map (star v*v)).re≤(τ.map p).re := by
    have hn := (Complex.nonneg_iff.mp (trace_projection_nonneg τ
      (projection_sub hp (partial_initial hv) hpi.1))).1
    simpa only [map_sub,Complex.sub_re,sub_nonneg] using hn
  have he' : star v*v=p := by
    rcases he with he | he
    · exact he
    · rw [he] at htr
      rw [htr] at hle
      exact False.elim (not_le.mpr hpq hle)
  refine ⟨v*star v,partial_final hv,?_,?_,hqi.1⟩
  · intro hz
    rw [he',hz,map_zero] at htr
    rw [htr,Complex.zero_re] at hp0
    exact lt_irrefl 0 hp0
  · intro heq
    rw [he',heq] at htr
    rw [htr] at hpq
    exact lt_irrefl _ hpq

theorem factor_diffuse_of_dyadic_projections (M : VonNeumannAlgebra H)
    (τ : FaithfulNormalTrace M) (hF : IsFactor M)
    (hproj : ∀ m : ℕ, ∃ p : ConcreteAlgebra M, IsStarProjection p ∧
      τ.map p=(((2:ℝ)^m)⁻¹:ℝ)) : IsDiffuse M := by
  apply factor_diffuse_of_small_projections M τ hF
  intro ε hε
  have ht : Filter.Tendsto (fun m : ℕ => 1/(2:ℝ)^m) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  obtain ⟨m,hm⟩ := (ht.eventually (eventually_lt_nhds hε)).exists
  obtain ⟨p,hp,hpτ⟩ := hproj m
  refine ⟨p,hp,?_,?_⟩
  · rw [hpτ,Complex.ofReal_re]
    positivity
  · rw [hpτ,Complex.ofReal_re]
    simpa only [one_div] using hm

end

end KKVariableUltra
end

end OAI
