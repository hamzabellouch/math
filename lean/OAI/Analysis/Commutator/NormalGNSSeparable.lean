import Mathlib
import OAI.Analysis.Commutator.NormalGNSContinuity
import OAI.Analysis.Commutator.WOTBallSeparable

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open Filter

open scoped InnerProductSpace Topology NNReal ComplexOrder

namespace Kadison.NormalGNS

open TracialGNS WOTDistance

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

lemma continuous_ball_coefficient (hnormal : BoundedWOTContinuous M τ) (x : τ.GNS) :
    Continuous (fun a : AlgebraBall M 1 => inner ℂ x (algebraVector τ ⟨a.val.toCLM,a.property.1⟩)) := by
  rw [continuous_iff_continuousAt]
  intro b
  have ht := tendsto_gns M τ hnormal
    (fun a : AlgebraBall M 1 => (⟨a.val.toCLM,a.property.1⟩ : M))
    (⟨b.val.toCLM,b.property.1⟩ : M) 1 (fun a => a.property.2) b.property.2
    (l := 𝓝 b) (fun ξ η => ?_) x (vacuum τ)
  · simp only [left_vacuum] at ht
    convert ht using 1
    rfl
  · have hc := ContinuousLinearMapWOT.continuous_inner_apply
      (continuous_subtype_val : Continuous (fun a : AlgebraBall M 1 => a.val)) ξ η
    have hh := (hc.tendsto b).star
    simp only [RCLike.star_def,inner_conj_symm] at hh
    exact hh

theorem separable_gns [TopologicalSpace.SeparableSpace H]
    (hnormal : BoundedWOTContinuous M τ) : TopologicalSpace.SeparableSpace τ.GNS := by
  classical
  let : SecondCountableTopology (AlgebraBall M 1) := secondCountable_algebraBall M zero_le_one
  let : Nonempty (AlgebraBall M 1) := ⟨⟨0,M.zero_mem,by simp⟩⟩
  obtain ⟨a,ha⟩ := TopologicalSpace.exists_dense_seq (AlgebraBall M 1)
  let v : ℕ → τ.GNS := fun n => algebraVector τ ⟨(a n).val.toCLM,(a n).property.1⟩
  let K : Submodule ℂ τ.GNS := Submodule.span ℂ (Set.range v)
  have hK : K.topologicalClosure=⊤ := by
    apply Submodule.topologicalClosure_eq_top_iff.mpr
    apply le_antisymm ?_ bot_le
    intro x hx
    have hv (n : ℕ) : inner ℂ x (v n)=0 := (K.mem_orthogonal' x).mp hx _
      (Submodule.subset_span (Set.mem_range_self n))
    have hball (b : AlgebraBall M 1) : inner ℂ x (algebraVector τ ⟨b.val.toCLM,b.property.1⟩)=0 := by
      exact ha.induction_on b (isClosed_eq (continuous_ball_coefficient M τ hnormal x) continuous_const) hv
    have hall (b : M) : inner ℂ x (algebraVector τ b)=0 := by
      by_cases hb : b=0
      · simp only [hb,map_zero,inner_zero_right]
      have hb' : (‖b‖ : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hb)
      let c : M := (‖b‖ : ℂ)⁻¹ • b
      have hn : ‖c‖≤1 := by
        dsimp only [c]
        rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg b)]
        exact le_of_eq (inv_mul_cancel₀ (norm_ne_zero_iff.mpr hb))
      have hc := hball ⟨ContinuousLinearMapWOT.ofCLM c,c.property,hn⟩
      have hbc : b=(‖b‖ : ℂ) • c := by
        dsimp only [c]
        rw [smul_smul,mul_inv_cancel₀ hb',one_smul]
      rw [hbc,map_smul,inner_smul_right,hc,mul_zero]
    have hx0 : x=0 := (algebraVector_dense τ).eq_of_inner_left ℂ
      (fun b => by simpa only [inner_zero_left] using hall b)
    simpa only [Submodule.mem_bot] using hx0
  have hs : TopologicalSpace.IsSeparable (K.topologicalClosure : Set τ.GNS) :=
    ((Set.countable_range v).isSeparable.span (R := ℂ)).closure
  rw [hK] at hs
  exact TopologicalSpace.isSeparable_univ_iff.mp hs

end Kadison.NormalGNS

end

end
end

end OAI
