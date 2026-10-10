import Mathlib
import OAI.Geometry.NearbyLagrangian.OpenCylinders

namespace OAI

/-! Ambient radial trapping and uniqueness of central cylinder curves. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Transport
open Set Filter Function TopologicalSpace ContinuousLinearMap InnerProductSpace
open scoped Manifold ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {V A M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace A] {I : ModelWithCorners ℝ V A}
  [TopologicalSpace M] [ChartedSpace A M]

theorem hamiltonian_equation_of_open_chart (U : Opens (E × E))
    (e : Diffeomorph I 𝓘(ℝ,E × E) M U ∞)
    (form : M → V → V → ℝ)
    (he : ∀ x u v,
      inner ℝ (mfderiv I 𝓘(ℝ,E × E) e x u).2 (mfderiv I 𝓘(ℝ,E × E) e x v).1 -
        inner ℝ (mfderiv I 𝓘(ℝ,E × E) e x v).2 (mfderiv I 𝓘(ℝ,E × E) e x u).1 = form x u v)
    {H : M → ℝ} {K : E × E → ℝ} {c : ℝ → M} {s : Set ℝ} {t : ℝ}
    (hKH : ∀ x : U, K (x:E × E) = H (e.symm x))
    (hK : DifferentiableAt ℝ K (e (c t) : E × E))
    (hc : MDifferentiableWithinAt 𝓘(ℝ,ℝ) I c s t)
    (ht : UniqueMDiffWithinAt 𝓘(ℝ,ℝ) s t)
    (hham : ∀ v,
      let d : ℝ → E × E := Subtype.val ∘ e ∘ c
      inner ℝ (fderivWithin ℝ d s t 1).2 v.1 - inner ℝ v.2 (fderivWithin ℝ d s t 1).1 =
        -fderiv ℝ K (d t) v) :
    ∀ v, form (c t) (mfderivWithin 𝓘(ℝ,ℝ) I c s t 1) v =
      -mfderiv I 𝓘(ℝ,ℝ) H (c t) v := by
  have hec := (e.contMDiffAt.mdifferentiableAt (by simp)).comp_mdifferentiableWithinAt t hc
  have hfun : (K ∘ Subtype.val : U → ℝ) ∘ e = H := by
    funext x
    change K (e x : E × E) = H x
    rw [hKH, e.symm_apply_apply]
  have hdiff : MDifferentiableAt 𝓘(ℝ,E × E) 𝓘(ℝ,ℝ) (K ∘ Subtype.val : U → ℝ) (e (c t)) :=
    hK.mdifferentiableAt.comp _ ((contMDiff_subtype_val (U:=U) (n:=∞)).mdifferentiableAt (by simp))
  have hd := mfderiv_comp (c t) hdiff (e.contMDiffAt.mdifferentiableAt (by simp))
  rw [hfun] at hd
  erw [mfderiv_open_restriction U hK] at hd
  intro v
  have h := hham (mfderiv I 𝓘(ℝ,E × E) e (c t) v)
  dsimp only at h
  rw [show (Subtype.val ∘ e ∘ c : ℝ → E × E) = Subtype.val ∘ (e ∘ c) from rfl,
    fderivWithin_open_curve U hec ht,
    mfderiv_comp_mfderivWithin t (e.contMDiffAt.mdifferentiableAt (by simp)) hc ht] at h
  change inner ℝ
    (mfderiv I 𝓘(ℝ,E × E) e (c t)
      (mfderivWithin 𝓘(ℝ,ℝ) I c s t 1)).2
    (mfderiv I 𝓘(ℝ,E × E) e (c t) v).1 - inner ℝ
      (mfderiv I 𝓘(ℝ,E × E) e (c t) v).2
      (mfderiv I 𝓘(ℝ,E × E) e (c t)
        (mfderivWithin 𝓘(ℝ,ℝ) I c s t 1)).1 =
      -fderiv ℝ K (e (c t):E × E) (mfderiv I 𝓘(ℝ,E × E) e (c t) v) at h
  erw [he] at h
  rw [hd]
  exact h

end NearbyLagrangian.Transport

namespace NearbyLagrangian.RadialExtension
open scoped Manifold ContDiff Topology NNReal
open Set Filter Function TopologicalSpace ContinuousLinearMap InnerProductSpace Transport
variable {V A M F G : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace A] {I : ModelWithCorners ℝ V A}
  [TopologicalSpace M] [ChartedSpace A M]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

omit [CompleteSpace G] in

theorem ambient_hamiltonian_radial_trapping (U : Opens (F × F)) (W : Opens (G × G))
    (e : Diffeomorph (I.prod 𝓘(ℝ,F × F)) 𝓘(ℝ,G × G) (M × U) W ∞)
    (form : M → V → V → ℝ) (hω : ∀ x u, form x u 0 = 0)
    (he : ∀ z u v,
      inner ℝ (mfderiv (I.prod 𝓘(ℝ,F × F)) 𝓘(ℝ,G × G) e z u).2
        (mfderiv (I.prod 𝓘(ℝ,F × F)) 𝓘(ℝ,G × G) e z v).1 -
      inner ℝ (mfderiv (I.prod 𝓘(ℝ,F × F)) 𝓘(ℝ,G × G) e z v).2
        (mfderiv (I.prod 𝓘(ℝ,F × F)) 𝓘(ℝ,G × G) e z u).1 =
        form z.1 u.1 v.1 + inner ℝ u.2.2 v.2.1 - inner ℝ v.2.2 u.2.1)
    {H : ℝ → M → ℝ} {ζ ξ : F → ℝ} {K : ℝ × (G × G) → ℝ}
    {c : ℝ → M × U}
    (hKH : ∀ t ∈ Icc (0:ℝ) 1, ∀ x : W,
      K (t,(x:G × G)) = (cutoffHamiltonian (H t) ζ ξ ∘ radialInclusion U) (e.symm x))
    (hK : ∀ t ∈ Icc (0:ℝ) 1, Differentiable ℝ (fun x => K (t,x)))
    (hc : ∀ t ∈ Icc (0:ℝ) 1,
      MDifferentiableWithinAt 𝓘(ℝ,ℝ) (I.prod 𝓘(ℝ,F × F)) c (Icc (0:ℝ) 1) t)
    (hH : ∀ t ∈ Icc (0:ℝ) 1, MDifferentiableAt I 𝓘(ℝ,ℝ) (H t) (c t).1)
    (hζd : Differentiable ℝ ζ) (hξd : Differentiable ℝ ξ)
    (hcH : ∀ t ∈ Icc (0:ℝ) 1, ∀ v,
      let d : ℝ → G × G := Subtype.val ∘ e ∘ c
      inner ℝ (fderivWithin ℝ d (Icc (0:ℝ) 1) t 1).2 v.1 -
        inner ℝ v.2 (fderivWithin ℝ d (Icc (0:ℝ) 1) t 1).1 =
          -fderiv ℝ (fun x => K (t,x)) (d t) v)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hbound : ∀ t ∈ Icc (0:ℝ) 1, |H t (c t).1| ≤ B)
    (hζ : ∀ a, ‖gradient ζ a‖ ≤ C)
    (hξ : ∀ w, ξ w ∈ Icc (0:ℝ) 1)
    (hplateau : ∀ w, ‖w‖ ≤ B*C+1 → ξ w = 1)
    (hp0 : ((c 0).2:F × F).2 = 0) :
    ∀ t ∈ Icc (0:ℝ) 1, ‖((c t).2:F × F).2‖ ≤ B*C ∧
      ξ ((c t).2:F × F).2 = 1 ∧ gradient ξ ((c t).2:F × F).2 = 0 ∧
      ((c t).2:F × F).1 = ((c 0).2:F × F).1 := by
  apply hamiltonian_open_radial_trapping U hc hH hζd hξd form hω _
    hB hC hbound hζ hξ hplateau hp0
  intro t ht
  exact hamiltonian_equation_of_open_chart W e
    (fun z u v => form z.1 u.1 v.1 + inner ℝ u.2.2 v.2.1 - inner ℝ v.2.2 u.2.1)
    he (hKH t ht) (hK t ht _) (hc t ht)
    ((uniqueDiffOn_Icc (by norm_num : (0:ℝ)<1) t ht).uniqueMDiffWithinAt) (hcH t ht)

omit [CompleteSpace F] in

theorem central_radial_curve_unique (U : Opens (F × F)) (W : Opens (G × G))
    (e : Diffeomorph (I.prod 𝓘(ℝ,F × F)) 𝓘(ℝ,G × G) (M × U) W ∞)
    (form : M → V → V → ℝ)
    (he : ∀ z u v,
      inner ℝ (mfderiv (I.prod 𝓘(ℝ,F × F)) 𝓘(ℝ,G × G) e z u).2
        (mfderiv (I.prod 𝓘(ℝ,F × F)) 𝓘(ℝ,G × G) e z v).1 -
      inner ℝ (mfderiv (I.prod 𝓘(ℝ,F × F)) 𝓘(ℝ,G × G) e z v).2
        (mfderiv (I.prod 𝓘(ℝ,F × F)) 𝓘(ℝ,G × G) e z u).1 =
        form z.1 u.1 v.1 + inner ℝ u.2.2 v.2.1 - inner ℝ v.2.2 u.2.1)
    {H : ℝ → M → ℝ} {ζ ξ : F → ℝ} {K : ℝ × (G × G) → ℝ}
    {b : ℝ → M} {c : ℝ → M × U} {a : F} (ha : (a,0) ∈ U)
    (hζ : ζ =ᶠ[𝓝 a] fun _ => (1:ℝ)) (hξ : ξ =ᶠ[𝓝 (0:F)] fun _ => (1:ℝ))
    (hKH : ∀ t ∈ Icc (0:ℝ) 1, ∀ x : W,
      K (t,(x:G × G)) = (cutoffHamiltonian (H t) ζ ξ ∘ radialInclusion U) (e.symm x))
    (hK : ∀ t ∈ Icc (0:ℝ) 1, Differentiable ℝ (fun x => K (t,x)))
    {L : ℝ≥0} (hL : ∀ t, LipschitzWith L (fun x => hamiltonianField K (t,x)))
    (hb : ∀ t ∈ Icc (0:ℝ) 1, MDifferentiableWithinAt 𝓘(ℝ,ℝ) I b (Icc (0:ℝ) 1) t)
    (hH : ∀ t ∈ Icc (0:ℝ) 1, MDifferentiableAt I 𝓘(ℝ,ℝ) (H t) (b t))
    (hbH : ∀ t ∈ Icc (0:ℝ) 1, ∀ v,
      form (b t) (mfderivWithin 𝓘(ℝ,ℝ) I b (Icc (0:ℝ) 1) t 1) v =
        -mfderiv I 𝓘(ℝ,ℝ) (H t) (b t) v)
    (hc : ∀ t ∈ Icc (0:ℝ) 1,
      MDifferentiableWithinAt 𝓘(ℝ,ℝ) (I.prod 𝓘(ℝ,F × F)) c (Icc (0:ℝ) 1) t)
    (hcH : ∀ t ∈ Icc (0:ℝ) 1, ∀ v,
      let d : ℝ → G × G := Subtype.val ∘ e ∘ c
      inner ℝ (fderivWithin ℝ d (Icc (0:ℝ) 1) t 1).2 v.1 -
        inner ℝ v.2 (fderivWithin ℝ d (Icc (0:ℝ) 1) t 1).1 =
          -fderiv ℝ (fun x => K (t,x)) (d t) v)
    (h0 : c 0 = (b 0,⟨(a,0),ha⟩)) :
    ∀ t ∈ Icc (0:ℝ) 1, c t = (b t,⟨(a,0),ha⟩) := by
  let d : ℝ → M × U := fun t => (b t,⟨(a,0),ha⟩)
  have hd (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      MDifferentiableWithinAt 𝓘(ℝ,ℝ) (I.prod 𝓘(ℝ,F × F)) d (Icc (0:ℝ) 1) t :=
    (hb t ht).prodMk mdifferentiableWithinAt_const
  have hHd (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      MDifferentiableAt (I.prod 𝓘(ℝ,F × F)) 𝓘(ℝ,ℝ)
        (cutoffHamiltonian (H t) ζ ξ ∘ radialInclusion U) (d t) :=
    (mdifferentiableAt_cutoffHamiltonian (hH t ht)
      (hζ.differentiableAt_iff.mpr (differentiableAt_const 1))
      (hξ.differentiableAt_iff.mpr (differentiableAt_const 1))).comp _
        ((contMDiff_radialInclusion U).mdifferentiableAt (by simp))
  have hdc := open_chart_hamiltonian_curve_unique W e
    (fun z u v => form z.1 u.1 v.1 + inner ℝ u.2.2 v.2.1 - inner ℝ v.2.2 u.2.1)
    he hKH hK hL hd hHd
    (fun t ht => central_open_product_hamiltonian_curve U ha hζ hξ form
      (hb t ht) ((uniqueDiffOn_Icc (by norm_num : (0:ℝ)<1) t ht).uniqueMDiffWithinAt)
      (hH t ht) (hbH t ht))
    (d := Subtype.val ∘ e ∘ c)
    (fun t ht => ((contMDiff_subtype_val (U:=W) (n:=∞)).mdifferentiableAt (by simp)).comp_mdifferentiableWithinAt t
      ((e.contMDiffAt.mdifferentiableAt (by simp)).comp_mdifferentiableWithinAt t (hc t ht)) |>.differentiableWithinAt)
    hcH (by change (e (b 0,⟨(a,0),ha⟩):G × G) = (e (c 0):G × G); rw [h0])
  intro t ht
  exact e.injective (Subtype.val_injective (hdc ht).symm)

end NearbyLagrangian.RadialExtension

end

end OAI
