import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.RadialIdentity
import OAI.Analysis.BiholderTransport.CostGeometry.BranchCost2
import OAI.Analysis.BiholderTransport.Coordinates.ProperPieces
import OAI.Analysis.BiholderTransport.Coordinates.ExpLocalBounds

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section FactorNorm
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma prefix_log_fderiv_exp_norm {x y : M} {t : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x}
    {q : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) y}
    (hq : DifferentiableAt ℝ q p)
    (hqr : ∀ᶠ a in 𝓝 p, riemannianExp y (q a)=riemannianExp x (t • a))
    (v : TangentSpace 𝓘(ℝ,Model n) x) :
    ‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) y) 𝓘(ℝ,Model n)
      (riemannianExp y) (q p) (fderiv ℝ q p v)‖=
    ‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n)
      (riemannianExp x) (t • p) (t • v)‖ := by
  let X := TangentSpace 𝓘(ℝ,Model n) x
  let Y := TangentSpace 𝓘(ℝ,Model n) y
  have he := (contMDiff_riemannianExp_fiber y (q p)).mdifferentiableAt (by simp)
  have hD := he.hasMFDerivAt.comp p hq.hasFDerivAt.hasMFDerivAt
  have hqr' : (riemannianExp y ∘ q) =ᶠ[𝓝 p] (fun a : X => riemannianExp x (t • a)) := hqr
  have hD' := hD.congr_of_eventuallyEq hqr'.symm
  have hscale : HasFDerivAt (fun a : X => t • a) (t • ContinuousLinearMap.id ℝ X) p :=
    (t • ContinuousLinearMap.id ℝ X).hasFDerivAt
  have hExp := ((contMDiff_riemannianExp_fiber x (t • p)).mdifferentiableAt
    (by simp)).hasMFDerivAt.comp p hscale.hasMFDerivAt
  have hN := congrArg (fun L : X →L[ℝ] TangentSpace 𝓘(ℝ,Model n)
      (riemannianExp x (t • p)) => ‖L v‖) (hD'.mfderiv.symm.trans hExp.mfderiv)
  have he0 := hqr.self_of_nhds
  convert! hN using 1
  congr 1
  rw [he0]

lemma prefix_zero_log_fderiv_norm {x y : M} {t : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x}
    {q : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) y}
    (hq : DifferentiableAt ℝ q p) (hqp : q p=0)
    (hqr : ∀ᶠ a in 𝓝 p, riemannianExp y (q a)=riemannianExp x (t • a))
    (v : TangentSpace 𝓘(ℝ,Model n) x) :
    ‖fderiv ℝ q p v‖=
    ‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n)
      (riemannianExp x) (t • p) (t • v)‖ := by
  have H := prefix_log_fderiv_exp_norm hq hqr v
  rw [hqp,mfderiv_exp_zero_norm] at H
  exact H

end FactorNorm
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section UniformPieces
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma suffix_log_total_eq_reverse {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} {t : ℝ}
    (hp : p∈minimizingVectors x) (ht : 0<t) (ht1 : t<1)
    {r : TangentSpace 𝓘(ℝ,Model n) (riemannianExp x p)}
    (hr : r∈injectivityDomain (riemannianExp x p))
    (her : riemannianExp (riemannianExp x p) r=riemannianExp x (t • p)) :
    (⟨riemannianExp x p,r⟩ : TangentBundle 𝓘(ℝ,Model n) M)=
      reverseRay (tangentScale (1-t) (sprayFlow t
        (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M))) := by
  let z : TangentBundle 𝓘(ℝ,Model n) M := ⟨x,p⟩
  let s := tangentScale (1-t) (sprayFlow t z)
  have hs : s.2∈injectivityDomain s.1 := proper_suffix_in_injectivityDomain hp ht ht1 le_rfl
  have hrev := reverseRay_injectivityDomain hs
  have he : (reverseRay s).1=riemannianExp x p := by
    change (sprayFlow 1 s).1=riemannianExp x p
    rw [←riemannianExp_eq_sprayFlow]
    exact shifted_exp_endpoint x p t
  have hEnd := reverseRay_endpoint s
  change riemannianExp (reverseRay s).1 (reverseRay s).2=(sprayFlow t z).1 at hEnd
  rw [←riemannianExp_smul] at hEnd
  change (⟨riemannianExp x p,r⟩ : TangentBundle 𝓘(ℝ,Model n) M)=reverseRay s
  generalize hdef : reverseRay s=w at hrev he hEnd ⊢
  rcases w with ⟨y,w⟩
  dsimp only at he hrev hEnd
  subst y
  have hrw : r=w := riemannianExp_injOn_injectivityDomain _ hr hrev (her.trans hEnd.symm)
  cases hrw
  rfl

lemma uniform_split_exp_bounds :
    ∃ l u : ℝ, 0<l ∧ 0<u ∧ ∀ z : TangentBundle 𝓘(ℝ,Model n) M,
      z.2∈minimizingVectors z.1 → ∀ t∈Icc (1/4:ℝ) (3/4),
      (∀ v, l*‖v‖≤‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) z.1) 𝓘(ℝ,Model n)
        (riemannianExp z.1) (t • z.2) v‖ ∧
        ‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) z.1) 𝓘(ℝ,Model n)
        (riemannianExp z.1) (t • z.2) v‖≤u*‖v‖) ∧
      (∀ v, let r := reverseRay (tangentScale (1-t) (sprayFlow t z));
        l*‖v‖≤‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) r.1) 𝓘(ℝ,Model n)
          (riemannianExp r.1) r.2 v‖ ∧
        ‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) r.1) 𝓘(ℝ,Model n)
          (riemannianExp r.1) r.2 v‖≤u*‖v‖) := by
  let G := {z : TangentBundle 𝓘(ℝ,Model n) M | z.2∈minimizingVectors z.1}
  let S := Icc (1/4:ℝ) (3/4) ×ˢ G
  let P : ℝ × TangentBundle 𝓘(ℝ,Model n) M → TangentBundle 𝓘(ℝ,Model n) M :=
    fun q => tangentScale q.1 q.2
  let R : ℝ × TangentBundle 𝓘(ℝ,Model n) M → TangentBundle 𝓘(ℝ,Model n) M :=
    fun q => reverseRay (tangentScale (1-q.1) (sprayFlow q.1 q.2))
  have hP : Continuous P := contMDiff_tangentScale.continuous
  have hR : Continuous R := continuous_reverseRay.comp (contMDiff_tangentScale.continuous.comp
    ((continuous_const.sub continuous_fst).prodMk contMDiff_sprayFlow.continuous))
  have hS : IsCompact S := isCompact_Icc.prod (isCompact_total_minimizingVectors (n := n) (M := M))
  have hK : IsCompact (P '' S ∪ R '' S) := (hS.image hP).union (hS.image hR)
  have hI : ∀ w∈P '' S ∪ R '' S, w.2∈injectivityDomain w.1 := by
    intro w hw
    rcases hw with hw | hw
    · rcases hw with ⟨⟨t,z⟩,htz,rfl⟩
      exact contracted_minimizer_mem_injectivityDomain htz.2 (by linarith [htz.1.1])
        (by linarith [htz.1.2])
    · rcases hw with ⟨⟨t,z⟩,htz,rfl⟩
      exact reverseRay_injectivityDomain (proper_suffix_in_injectivityDomain htz.2
        (by linarith [htz.1.1]) (by linarith [htz.1.2]) le_rfl)
  obtain ⟨l,u,hl,hu,H⟩ := compact_exp_differential_bounds hK hI
  refine ⟨l,u,hl,hu,?_⟩
  intro z hz t ht
  exact ⟨H (P (t,z)) (Or.inl (mem_image_of_mem _ ⟨ht,hz⟩)),
    H (R (t,z)) (Or.inr (mem_image_of_mem _ ⟨ht,hz⟩))⟩

end UniformPieces
end WeakMTWTransport

end

end

end

end OAI
