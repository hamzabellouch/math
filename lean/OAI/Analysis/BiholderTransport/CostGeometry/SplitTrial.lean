import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.ActualRadial
import OAI.Analysis.BiholderTransport.LinearAlgebra.SchurEnvelope
import OAI.Analysis.BiholderTransport.Coordinates.SplitPairing
import OAI.Analysis.BiholderTransport.Volume.DiagonalKernel

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def splitTrialValue (x : M) (t : ℝ) (xi k w : TangentSpace 𝓘(ℝ,Model n) x) : ℝ :=
  iteratedDeriv 2 (fun s : ℝ => splitNormalAction x t w (s • xi,w+s • k)) 0

lemma splitTrialValue_contDiffAt {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hleft : t • p ∈ injectivityDomain x)
    (hright : (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    (xi k : TangentSpace 𝓘(ℝ,Model n) x) :
    ContDiffAt ℝ ∞ (splitTrialValue x t xi k) p := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hp := splitNormalAction_contDiffAt hleft hright
  have hl : ContDiffAt ℝ ∞ (fun q : V×ℝ => (q.1,(q.2 • xi,q.1+q.2 • k))) (p,0) := by fun_prop
  have hs : ContDiffAt ℝ ∞ (fun q : V×ℝ => splitNormalAction x t q.1 (q.2 • xi,q.1+q.2 • k)) (p,0) := by
    have hp' : ContDiffAt ℝ ∞ (fun z : V×(V×V) => splitNormalAction x t z.1 z.2)
        (p,((0:ℝ) • xi,p+(0:ℝ) • k)) := by simpa using hp
    exact hp'.comp (p,0) hl
  exact contDiffAt_iteratedDeriv_parameter hs 2

lemma splitTrialValue_eq_hessian {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hleft : t • p ∈ injectivityDomain x)
    (hright : (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    (xi k : TangentSpace 𝓘(ℝ,Model n) x) :
    splitTrialValue x t xi k p =
      fderiv ℝ (fderiv ℝ (splitNormalAction x t p)) (0,p) (xi,k) (xi,k) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hc := (splitNormalAction_contDiffAt hleft hright).comp
    (f := fun q : V×V => (p,q)) (0,p) (contDiffAt_const.prodMk contDiffAt_id)
  simpa only [Function.comp_def,splitTrialValue,Prod.mk_add_mk,Prod.smul_mk,Prod.fst_add,Prod.smul_fst,Prod.snd_add,Prod.smul_snd,zero_add] using
    iteratedDeriv_two_affine_line (hc.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) (xi,k)

lemma splitTrialValue_middle_eq_diagonal {x : M} {p k : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hleft : t • p ∈ injectivityDomain x)
    (hright : (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    splitTrialValue x t 0 k p =
      fderiv ℝ (fderiv ℝ (diagonalSplitAction x t)) (p,p) (0,k) (0,k) := by
  simpa only [splitTrialValue,diagonalSplitAction,Prod.fst_add,Prod.smul_fst,
    Prod.snd_add,Prod.smul_snd,smul_zero,add_zero] using
    iteratedDeriv_two_affine_line ((diagonalSplitAction_contDiffAt hleft hright).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) ((0 : TangentSpace 𝓘(ℝ,Model n) x),k)

lemma splitTrialValue_nonneg {x : M} {p k : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (ht : 0<t) (ht1 : t<1) (hp : p ∈ minimizingVectors x)
    (hleft : t • p ∈ injectivityDomain x)
    (hright : (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    0 ≤ splitTrialValue x t 0 k p := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let f : ℝ → ℝ := fun s => splitNormalAction x t p (0,p+s • k)
  have hmin : IsLocalMin f 0 := by
    apply Filter.Eventually.of_forall
    intro s
    change splitNormalAction x t p (0,p+(0:ℝ) • k) ≤ splitNormalAction x t p (0,p+s • k)
    simp only [zero_smul,add_zero,splitNormalAction_contact hp ht ht1]
    exact normalCost_le_splitNormalAction x p 0 (p+s • k) ht ht1
  have hp' : ContDiffAt ℝ ∞ (fun z : V×(V×V) => splitNormalAction x t z.1 z.2)
      (p,((0:V),p+(0:ℝ) • k)) := by simpa using splitNormalAction_contDiffAt hleft hright
  have hBc := hp'.comp
    (f := fun s : ℝ => (p,((0:V),p+s • k))) 0 (by fun_prop)
  have hfc : ContinuousAt f 0 := by exact hBc.continuousAt
  have H := localMin_second_deriv_nonneg hmin hfc
  simpa only [splitTrialValue,smul_zero,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero,f] using H

lemma splitTrialValue_conjugate_null {x : M} {p k : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (ht : 0<t) (ht1 : t<1) (hleft : t • p ∈ injectivityDomain x)
    (hright : (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    (hk : mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n) (riemannianExp x) p k=0) :
    splitTrialValue x t 0 k p=0 := by
  rw [splitTrialValue_middle_eq_diagonal hleft hright]
  exact diagonalSplitAction_conjugate_hessian_null ht ht1 hleft hright hk

lemma splitTrialValue_schur {x : M} {p xi k : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (ht : 0<t) (ht1 : t<1) (hp : p ∈ injectivityDomain x)
    (hleft : t • p ∈ injectivityDomain x)
    (hright : (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    (hpair : inner ℝ k xi≠0) :
    0<splitTrialValue x t 0 k p ∧
      hessianValue x p xi ≤ splitTrialValue x t xi 0 p-(inner ℝ k xi)^2/splitTrialValue x t 0 k p := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hf := (normalCost_contDiffAt hp).of_le (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hBc := (splitNormalAction_contDiffAt hleft hright).comp
    (f := fun q : V×V => (p,q)) (0,p) (contDiffAt_const.prodMk contDiffAt_id)
  have hB := hBc.of_le (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hle : ∀ᶠ z : V×V in 𝓝 (0,p), normalCost x p z.1 ≤ splitNormalAction x t p z :=
    Filter.Eventually.of_forall (fun z => normalCost_le_splitNormalAction x p z.1 z.2 ht ht1)
  have heq := (splitNormalAction_contact (injectivityDomain_subset_minimizingVectors x hp) ht ht1).symm
  have hmix := splitNormalAction_mixed_pairing ht.ne' hleft hright xi k
  have hmixne : fderiv ℝ (fderiv ℝ (splitNormalAction x t p)) (0,p) (xi,0) (0,k)≠0 := by
    rw [hmix]; exact neg_ne_zero.mpr hpair
  constructor
  · rw [splitTrialValue_eq_hessian hleft hright]
    exact upper_contact_block_positive hf hB hle heq xi k hmixne
  · rw [hessianValue_eq_normalHessian hp,splitTrialValue_eq_hessian hleft hright,
      splitTrialValue_eq_hessian hleft hright]
    have H := upper_contact_block_schur hf hB hle heq xi k hmixne
    dsimp only [Function.comp_def] at H
    rw [hmix,neg_sq] at H
    exact H
end WeakMTWTransport

end

end OAI
