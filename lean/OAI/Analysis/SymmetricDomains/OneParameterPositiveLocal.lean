import Mathlib
import OAI.Analysis.SymmetricDomains.OneParameterGeneratorAdd

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)}

theorem exists_oneParameter_of_positive_local_ODE (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsPreconnected U) (hbd : Bornology.IsBounded U) (p : U)
    (X : Affine n → Affine n) (hX : AnalyticOnNhd ℂ X U)
    (g : ℝ → Biholomorph U U) {r T : ℝ} (hr : 0<r) (hT : 0<T)
    (_hball : closedBall p.val r⊆U) (hgc : ContinuousOn g (Icc 0 T))
    (hd : ∀ x∈closedBall p.val r, ∀ t∈Ioo 0 T,
      HasStrictDerivAt (fun s => (g s).ambientAut x) (X ((g t).ambientAut x)) t) :
    ∃ H : ℝ → Biholomorph U U, H 0=1 ∧ Continuous H ∧
      (∀ s t, H (s+t)=H s*H t) ∧ EqOn (infinitesimalGenerator H) X U := by
  let C : ℝ := T/2
  let δ : ℝ := T/4
  have hδ : 0<δ := by dsimp [δ]; positivity
  let p' : U := (g C).toHomeomorph p
  have hi : ((g C)⁻¹).ambientAut p'.val=p.val := by
    rw [ambientAut_apply]
    change (((g C)⁻¹).toHomeomorph ((g C).toHomeomorph p)).val=p.val
    rw [← mul_apply,inv_mul_cancel,one_apply]
  have hpre : ((g C)⁻¹).ambientAut ⁻¹' ball p.val r ∈ 𝓝 p'.val := by
    apply (ambientAut_analytic hU ((g C)⁻¹) p'.val p'.property).continuousAt
    simpa only [hi] using ball_mem_nhds p.val hr
  obtain ⟨ρ,hρ,hρsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (inter_mem hpre (hU.mem_nhds p'.property))
  let f : ℝ → Biholomorph U U := fun t => g (C+t)*(g C)⁻¹
  have hf0 : f 0=1 := by simp only [f,add_zero,mul_inv_cancel]
  have hfc : ContinuousOn f (Icc (-δ) δ) := by
    apply (hgc.comp (continuous_const.add continuous_id).continuousOn ?_).mul continuous_const.continuousOn
    intro t ht
    dsimp [C,δ] at *
    constructor <;> linarith [ht.1,ht.2]
  have hfd : ∀ x∈closedBall p'.val ρ, ∀ t∈Ioo (-δ) δ,
      HasStrictDerivAt (fun s => (f s).ambientAut x) (X ((f t).ambientAut x)) t := by
    intro x hx t ht
    have hxu : x∈U := (hρsub hx).2
    let y : U := ((g C)⁻¹).toHomeomorph ⟨x,hxu⟩
    have hy : y.val∈closedBall p.val r := by
      have hv := ball_subset_closedBall (hρsub hx).1
      change ((g C)⁻¹).ambientAut x∈closedBall p.val r at hv
      simpa only [ambientAut_apply (p := ⟨x,hxu⟩)] using hv
    have htt : C+t∈Ioo 0 T := by
      dsimp [C,δ] at *
      constructor <;> linarith [ht.1,ht.2]
    have hs : HasStrictDerivAt (fun s : ℝ => C+s) 1 t := by
      simpa only [id_eq] using (hasStrictDerivAt_id t).const_add C
    have hh := (hd y.val hy (C+t) htt).scomp t hs
    have he (s : ℝ) : (f s).ambientAut x=(g (C+s)).ambientAut y.val := by
      rw [ambientAut_apply (f s) ⟨x,hxu⟩,ambientAut_apply]
      exact congrArg Subtype.val (mul_apply _ _ _)
    simpa only [Function.comp_def,one_smul,← he] using hh
  exact exists_oneParameter_of_local_ODE hU hc hbd p' X hX f hf0 hρ hδ
    (fun x hx => (hρsub hx).2) hfc hfd

end Biholomorph
end Release061

end

end OAI
