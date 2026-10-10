import Mathlib
import OAI.Analysis.BiholderTransport.Calculus.SecondDerivativeSlice
import OAI.Analysis.BiholderTransport.Regularity.CriticalChain
import OAI.Analysis.BiholderTransport.Coordinates.JoinCoordinates

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section JoinCongruence
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma split_join_hessian_congruence {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p∈minimizingVectors x)
    {h : ℝ} (hh : 0<h) (hh1 : h<1) :
    ∃ P : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ]
        TangentSpace 𝓘(ℝ,Model n) (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1,
      Function.Injective P ∧ ∀ a,
      fderiv ℝ (fderiv ℝ (diagonalSplitAction x h)) (p,p) (0,a) (0,a)=
        middleHessian (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M) h 1 (P a) (P a) := by
  let z : TangentBundle 𝓘(ℝ,Model n) M := ⟨x,p⟩
  have hleft := contracted_minimizer_mem_injectivityDomain hp hh hh1
  obtain ⟨q,hqp,hq,hqinj,hqr⟩ := exists_join_normal_coordinates hh.ne' hleft
  have hf := middleCenteredAction_contDiffAt (z := z) hp hh hh1
  have hf' : ContDiffAt ℝ 2 (middleCenteredAction z h) (q p) := by rwa [hqp]
  have hz : fderiv ℝ (middleCenteredAction z h) (q p)=0 := by
    rw [hqp]
    exact (middleCenteredAction_minimum (z := z) hp hh hh1).fderiv_eq_zero
  have hF : ContDiffAt ℝ 2 (diagonalSplitAction x h) (p,p) :=
    (diagonalSplitAction_contDiffAt hleft (proper_suffix_in_injectivityDomain
      (z := z) hp hh hh1 le_rfl)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have he := middle_action_in_join_coordinates hp hh hh1 hqr
  have heD := he.fderiv (𝕜 := ℝ)
  have heDD := heD.fderiv_eq (𝕜 := ℝ)
  change fderiv ℝ (fderiv ℝ (middleCenteredAction z h ∘ q)) p =
    fderiv ℝ (fderiv ℝ (fun a => diagonalSplitAction x h (p,a)-cost x (riemannianExp x p))) p at heDD
  have hsub : fderiv ℝ (fun a => diagonalSplitAction x h (p,a)-cost x (riemannianExp x p))=
      fderiv ℝ (fun a => diagonalSplitAction x h (p,a)) := by
    funext a; exact fderiv_sub_const _
  rw [hsub] at heDD
  refine ⟨fderiv ℝ q p,hqinj,?_⟩
  intro a
  have H := second_fderiv_comp_at_critical hf' (hq.of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hz a a
  rw [heDD,hqp,second_derivative_target_slice hF] at H
  exact H.trans (middleCenteredAction_hessian (z := z) hp hh hh1 _)

end JoinCongruence
end WeakMTWTransport

end

end

end

end OAI
