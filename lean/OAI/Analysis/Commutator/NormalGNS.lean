import Mathlib
import OAI.Analysis.Commutator.BicommutantRange
import OAI.Analysis.Commutator.KaplanskyRange
import OAI.Analysis.Commutator.TracialRightClosure
import OAI.Analysis.Commutator.VonNeumannCStar
import OAI.Analysis.Commutator.WeakOperatorAlgebra
import OAI.Analysis.Commutator.WeakOperatorLimit

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace Topology ComplexOrder

open Filter ContinuousLinearMapWOT

namespace Kadison.NormalGNS

open TracialGNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

def BoundedWOTContinuous : Prop :=
  ∀ C : ℝ, Continuous (fun a : {T : H →WOT[ℂ] H // T.toCLM∈M ∧ ‖T.toCLM‖≤C} =>
    τ ⟨a.val.toCLM,a.property.1⟩)

lemma tendsto_trace (hnormal : BoundedWOTContinuous M τ)
    {ι : Type*} {l : Filter ι} (a : ι → M) (b : M) (C : ℝ)
    (ha : ∀ i, ‖a i‖≤C) (hb : ‖b‖≤C)
    (hlim : ∀ x y, Tendsto (fun i => inner ℂ ((a i : H →L[ℂ] H) x) y) l
      (𝓝 (inner ℂ ((b : H →L[ℂ] H) x) y))) :
    Tendsto (fun i => τ (a i)) l (𝓝 (τ b)) := by
  let f : ι → {T : H →WOT[ℂ] H // T.toCLM∈M ∧ ‖T.toCLM‖≤C} :=
    fun i => ⟨ofCLM (a i), (a i).property, ha i⟩
  let z : {T : H →WOT[ℂ] H // T.toCLM∈M ∧ ‖T.toCLM‖≤C} :=
    ⟨ofCLM b,b.property,hb⟩
  have hf : Tendsto f l (𝓝 z) := by
    apply tendsto_subtype_rng.mpr
    apply tendsto_iff_forall_inner_apply_tendsto.mpr
    intro x y
    simpa only [f,z,RCLike.star_def,inner_conj_symm,ofCLM_apply] using (hlim x y).star
  exact ((hnormal C).tendsto z).comp hf

theorem vector_unitball_isClosed (hnormal : BoundedWOTContinuous M τ) :
    IsClosed {x : τ.GNS | ∃ a : M, ‖a‖≤1 ∧ algebraVector τ a=x} := by
  apply IsSeqClosed.isClosed
  intro v x hv hx
  choose a ha hav using hv
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  have hω : (ω : Filter ℕ)≤atTop := Ultrafilter.of_le _
  obtain ⟨W,hW,hlim⟩ := WeakOperatorLimit.exists_ultralimit ω
    (fun i => (a i : H →L[ℂ] H)) 1 (by norm_num) ha
  have hWM : W∈M := WeakOperatorLimit.mem_vonNeumann hlim M
    (Eventually.of_forall fun i => (a i).property)
  let b : M := ⟨W,hWM⟩
  refine ⟨b,hW,?_⟩
  apply (algebraVector_dense τ).eq_of_inner_right ℂ
  intro c
  have htr : Tendsto (fun i => τ (star c*a i)) (ω : Filter ℕ) (𝓝 (τ (star c*b))) := by
    apply tendsto_trace M τ hnormal (fun i => star c*a i) (star c*b) ‖c‖
    · intro i
      exact (norm_mul_le _ _).trans (by simpa only [norm_star,mul_one] using mul_le_mul_of_nonneg_left (ha i) (norm_nonneg (star c)))
    · exact (norm_mul_le _ _).trans (by simpa only [norm_star,mul_one] using mul_le_mul_of_nonneg_left (show ‖b‖≤1 from hW) (norm_nonneg (star c)))
    · intro ξ η
      change Tendsto (fun i => inner ℂ ((star (c : H →L[ℂ] H)) ((a i : H →L[ℂ] H) ξ)) η)
        (ω : Filter ℕ) (𝓝 (inner ℂ ((star (c : H →L[ℂ] H)) (W ξ)) η))
      simpa only [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left] using hlim ξ ((c : H →L[ℂ] H) η)
  have hvec : Tendsto (fun i => inner ℂ (algebraVector τ c) (algebraVector τ (a i)))
      (ω : Filter ℕ) (𝓝 (inner ℂ (algebraVector τ c) x)) := by
    have ht : Tendsto (fun z : τ.GNS => inner ℂ (algebraVector τ c) z)
        (𝓝 x) (𝓝 (inner ℂ (algebraVector τ c) x)) :=
      (continuous_const.inner continuous_id).tendsto x
    exact ht.comp ((hx.mono_left hω).congr' (Eventually.of_forall fun i => (hav i).symm))
  rw [inner_algebraVector]
  simp only [inner_algebraVector] at hvec
  exact tendsto_nhds_unique htr hvec

variable (hτ : ∀ a b : M, τ (a*b)=τ (b*a))

include hτ

lemma eq_of_vacuum {S T : τ.GNS →L[ℂ] τ.GNS}
    (hS : S∈Set.centralizer (Set.centralizer (Set.range τ.gnsStarAlgHom)))
    (hT : T∈Set.centralizer (Set.centralizer (Set.range τ.gnsStarAlgHom)))
    (he : S (vacuum τ)=T (vacuum τ)) : S=T := by
  apply sub_eq_zero.mp
  apply bicommutant_vacuum_separating τ hτ
  · intro a ha
    simp only [mul_sub,sub_mul,hS a ha,hT a ha]
  · exact sub_eq_zero.mpr he

theorem bicommutant_selfAdjoint_contraction (hnormal : BoundedWOTContinuous M τ)
    {T : τ.GNS →L[ℂ] τ.GNS}
    (hT : T∈Set.centralizer (Set.centralizer (Set.range τ.gnsStarAlgHom)))
    (hsT : IsSelfAdjoint T) (hnT : ‖T‖≤1) :
    ∃ a : M, ‖a‖≤1 ∧ τ.gnsStarAlgHom a=T := by
  have hx : T (vacuum τ)∈closure {x : τ.GNS | ∃ a : M, ‖a‖≤1 ∧ algebraVector τ a=x} := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨a,_,hna,he⟩ := Kaplansky.range_selfAdjoint_contraction_finite_approx
      Unit τ.gnsStarAlgHom hT hsT hnT (fun _ => vacuum τ) ε hε
    refine ⟨algebraVector τ a,⟨a,hna,rfl⟩,?_⟩
    simpa only [dist_eq_norm,norm_sub_rev,left_vacuum,algebraVector_apply] using he ()
  rw [(vector_unitball_isClosed M τ hnormal).closure_eq] at hx
  obtain ⟨a,ha,he⟩ := hx
  refine ⟨a,ha,eq_of_vacuum M τ hτ (Set.subset_centralizer_centralizer (Set.mem_range_self a)) hT ?_⟩
  simpa only [left_vacuum,algebraVector_apply] using he

theorem range_bicommutant (hnormal : BoundedWOTContinuous M τ) :
    Set.centralizer (Set.centralizer (Set.range τ.gnsStarAlgHom))=Set.range τ.gnsStarAlgHom := by
  apply BicommutantRange.operatorHom_range
  intro T hT hsT hnT
  obtain ⟨a,_,ha⟩ := bicommutant_selfAdjoint_contraction M τ hτ hnormal hT hsT hnT
  exact ⟨a,ha⟩

end Kadison.NormalGNS

end

end
end

end OAI
