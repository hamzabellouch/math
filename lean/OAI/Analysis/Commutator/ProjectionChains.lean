import Mathlib
import OAI.Analysis.Commutator.WeakOperatorAlgebra
import OAI.Analysis.Commutator.WeakOperatorLimit

namespace OAI

noncomputable section

section

noncomputable section

open Filter ContinuousLinearMapWOT

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.ProjectionChains

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem monotone_ultralimit [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (ω : Ultrafilter ι) (hω : (ω : Filter ι)≤atTop)
    (P : ι → H →L[ℂ] H) (hp : ∀ i, IsStarProjection (P i)) (hmono : Monotone P) :
    ∃ W : H →L[ℂ] H, IsStarProjection W ∧ (∀ i, P i≤W) ∧
      Tendsto (fun i => ofCLM (P i)) (ω : Filter ι) (𝓝 (ofCLM W)) ∧
      ∀ Q : H →L[ℂ] H, IsStarProjection Q → (∀ i, P i≤Q) → W≤Q := by
  obtain ⟨W,_,hlim⟩ := WeakOperatorLimit.exists_ultralimit ω P 1 zero_le_one
    (fun i => (hp i).norm_le (P i))
  have hWot : Tendsto (fun i => ofCLM (P i)) (ω : Filter ι) (𝓝 (ofCLM W)) := by
    apply tendsto_iff_forall_inner_apply_tendsto.mpr
    intro x y
    simpa only [RCLike.star_def,inner_conj_symm,ofCLM_apply] using (hlim x y).star
  have hself : IsSelfAdjoint W := by
    have heq : star (ofCLM W)=ofCLM W := tendsto_nhds_unique hWot.star
      (hWot.congr' (Filter.Eventually.of_forall fun i => by
        change ofCLM (P i)=star (ofCLM (P i))
        apply toCLM_injective
        exact (hp i).isSelfAdjoint.star_eq.symm))
    exact congrArg toCLM heq
  have hWP : ∀ i, W*P i=P i := by
    intro i
    apply WeakOperatorLimit.right_eq hlim
    apply ((eventually_ge_atTop i).filter_mono hω).mono
    intro j hij
    exact ((hp i).le_iff_mul_eq_right (hp j)).mp (hmono hij)
  have hWsq : W*W=W := by
    have hh := WeakOperatorLimit.intertwine hlim 1 W (Filter.Eventually.of_forall
      fun i => by simpa only [mul_one] using (hWP i).symm)
    simpa only [mul_one] using hh.symm
  have hproj : IsStarProjection W := ⟨hWsq,hself⟩
  refine ⟨W,hproj,fun i => ((hp i).le_iff_mul_eq_right hproj).mpr (hWP i),hWot,?_⟩
  intro Q hQ hPQ
  have hh := WeakOperatorLimit.intertwine hlim Q 1 (Filter.Eventually.of_forall
    fun i => by simpa only [one_mul] using ((hp i).le_iff_mul_eq_left hQ).mp (hPQ i))
  apply (hproj.le_iff_mul_eq_left hQ).mpr
  simpa only [one_mul] using hh

variable (M : VonNeumannAlgebra H) (τ : (H →L[ℂ] H) →ₚ[ℂ] ℂ)

variable (e : H →L[ℂ] H) (t : ℝ)

abbrev TraceCut := {p : H →L[ℂ] H // p∈M ∧ IsStarProjection p ∧ p≤e ∧ (τ p).re≤t}

theorem cut_chain_upper (he : IsStarProjection e)
    (hτ : Continuous (fun T : H →WOT[ℂ] H => (τ T.toCLM).re))
    (c : Set (TraceCut M τ e t)) (hc : IsChain (·≤·) c) (hne : c.Nonempty) : BddAbove c := by
  let : Nonempty c := hne.to_subtype
  let : IsDirectedOrder c := hc.directedOn.isDirectedOrder
  let ω : Ultrafilter c := Ultrafilter.of atTop
  have hω : (ω : Filter c)≤atTop := Ultrafilter.of_le atTop
  let P : c → H →L[ℂ] H := fun v => v.val.val
  obtain ⟨W,hW,hPW,hlim,hLeast⟩ := monotone_ultralimit ω hω P (fun i => i.val.property.2.1)
    (fun _ _ h => h)
  have hscalar : ∀ x y, Tendsto (fun i => inner ℂ (P i x) y) (ω : Filter c)
      (𝓝 (inner ℂ (W x) y)) := by
    intro x y
    have h := tendsto_iff_forall_inner_apply_tendsto.mp hlim x y
    simpa only [RCLike.star_def,inner_conj_symm,ofCLM_apply] using h.star
  have hWM : W∈M := WeakOperatorLimit.mem_vonNeumann hscalar M
    (Filter.Eventually.of_forall fun i => i.val.property.1)
  have hWe : W≤e := hLeast e he (fun i => i.val.property.2.2.1)
  have htrace : (τ W).re≤t := le_of_tendsto ((hτ.tendsto (ofCLM W)).comp hlim)
    (Filter.Eventually.of_forall fun i : c => i.val.property.2.2.2)
  refine ⟨⟨W,hWM,hW,hWe,htrace⟩,?_⟩
  intro p hp
  exact hPW ⟨p,hp⟩

end Kadison.ProjectionChains

end

end
end

end OAI
