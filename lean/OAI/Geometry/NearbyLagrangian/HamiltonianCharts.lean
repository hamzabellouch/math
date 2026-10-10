import Mathlib
import OAI.Geometry.NearbyLagrangian.HamiltonianFlow

namespace OAI

/-! Hamiltonian equations and uniqueness in smooth open charts. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Transport
open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Manifold ContDiff Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma symplecticGradient_unique {L : (E × E) →L[ℝ] ℝ} {u : E × E}
    (hu : ∀ v, inner ℝ u.2 v.1 - inner ℝ v.2 u.1 = -L v) :
    u = symplecticGradient L := by
  apply Prod.ext
  · apply ext_inner_right ℝ
    intro w
    have h := (hu (0,w)).trans (symplecticGradient_identity L (0,w)).symm
    simp only [inner_zero_right,zero_sub] at h
    rw [real_inner_comm w u.1,real_inner_comm w (symplecticGradient L).1]
    exact neg_injective h
  · apply ext_inner_right ℝ
    intro w
    have h := (hu (w,0)).trans (symplecticGradient_identity L (w,0)).symm
    simpa only [inner_zero_left,sub_zero] using h

lemma canonical_hamiltonian_hasDerivWithinAt
    {H : ℝ × (E × E) → ℝ} {c : ℝ → E × E} {s : Set ℝ} {t : ℝ}
    (hc : DifferentiableWithinAt ℝ c s t)
    (hham : ∀ v, inner ℝ (fderivWithin ℝ c s t 1).2 v.1 -
      inner ℝ v.2 (fderivWithin ℝ c s t 1).1 =
        -fderiv ℝ (fun x => H (t,x)) (c t) v) :
    HasDerivWithinAt c (hamiltonianField H (t,c t)) s t := by
  have hu := symplecticGradient_unique hham
  have hd := hc.hasDerivWithinAt
  change HasDerivWithinAt c (fderivWithin ℝ c s t 1) s t at hd
  rw [hu] at hd
  exact hd

lemma closedSlab_hasDerivWithinAt_right {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {c : ℝ → F} {v : F} {t : ℝ}
    (h : HasDerivWithinAt c v (Icc (0:ℝ) 1) t) (ht : t ∈ Ico (0:ℝ) 1) :
    HasDerivWithinAt c v (Ici t) t := by
  apply h.mono_of_mem_nhdsWithin
  exact Filter.mem_of_superset (Icc_mem_nhdsGE ht.2)
    (Icc_subset_Icc_left ht.1)

theorem canonical_hamiltonian_curves_unique
    {H : ℝ × (E × E) → ℝ} {c d : ℝ → E × E} {K : ℝ≥0}
    (hK : ∀ t, LipschitzWith K (fun x => hamiltonianField H (t,x)))
    (hc : ∀ t ∈ Icc (0:ℝ) 1, DifferentiableWithinAt ℝ c (Icc (0:ℝ) 1) t)
    (hd : ∀ t ∈ Icc (0:ℝ) 1, DifferentiableWithinAt ℝ d (Icc (0:ℝ) 1) t)
    (hcH : ∀ t ∈ Icc (0:ℝ) 1, ∀ v,
      inner ℝ (fderivWithin ℝ c (Icc (0:ℝ) 1) t 1).2 v.1 -
      inner ℝ v.2 (fderivWithin ℝ c (Icc (0:ℝ) 1) t 1).1 =
        -fderiv ℝ (fun x => H (t,x)) (c t) v)
    (hdH : ∀ t ∈ Icc (0:ℝ) 1, ∀ v,
      inner ℝ (fderivWithin ℝ d (Icc (0:ℝ) 1) t 1).2 v.1 -
      inner ℝ v.2 (fderivWithin ℝ d (Icc (0:ℝ) 1) t 1).1 =
        -fderiv ℝ (fun x => H (t,x)) (d t) v)
    (h0 : c 0 = d 0) : EqOn c d (Icc (0:ℝ) 1) := by
  apply ODE_solution_unique hK
  · exact fun t ht => (hc t ht).continuousWithinAt
  · intro t ht
    exact closedSlab_hasDerivWithinAt_right
      (canonical_hamiltonian_hasDerivWithinAt (hc t ⟨ht.1,ht.2.le⟩)
        (hcH t ⟨ht.1,ht.2.le⟩)) ht
  · exact fun t ht => (hd t ht).continuousWithinAt
  · intro t ht
    exact closedSlab_hasDerivWithinAt_right
      (canonical_hamiltonian_hasDerivWithinAt (hd t ⟨ht.1,ht.2.le⟩)
        (hdH t ⟨ht.1,ht.2.le⟩)) ht
  · exact h0

end NearbyLagrangian.Transport

namespace NearbyLagrangian
variable {V W A B M N : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace A] [TopologicalSpace B]
  {I : ModelWithCorners ℝ V A} {J : ModelWithCorners ℝ W B}
  [TopologicalSpace M] [ChartedSpace A M]
  [TopologicalSpace N] [ChartedSpace B N]

lemma diffeomorph_mfderiv_inverse (e : Diffeomorph I J M N ∞) (x : M) :
    (mfderiv J I e.symm (e x)).comp (mfderiv I J e x) =
      ContinuousLinearMap.id ℝ V := by
  have h := mfderiv_comp x (e.symm.contMDiffAt.mdifferentiableAt (by simp))
    (e.contMDiffAt.mdifferentiableAt (by simp))
  have he : (e.symm ∘ e) = id := funext e.symm_apply_apply
  rw [he,mfderiv_id] at h
  exact h.symm

theorem hamiltonian_equation_diffeomorph
    (e : Diffeomorph I J M N ∞)
    (ωM : M → V → V → ℝ) (ωN : N → W → W → ℝ)
    (he : ∀ x u v, ωN (e x) (mfderiv I J e x u) (mfderiv I J e x v) = ωM x u v)
    {c : ℝ → M} {H : M → ℝ} {s : Set ℝ} {t : ℝ}
    (hc : MDifferentiableWithinAt 𝓘(ℝ,ℝ) I c s t)
    (ht : UniqueMDiffWithinAt 𝓘(ℝ,ℝ) s t)
    (hH : MDifferentiableAt I 𝓘(ℝ,ℝ) H (c t))
    (hham : ∀ v, ωM (c t) (mfderivWithin 𝓘(ℝ,ℝ) I c s t 1) v =
      -mfderiv I 𝓘(ℝ,ℝ) H (c t) v) :
    ∀ v, ωN (e (c t)) (mfderivWithin 𝓘(ℝ,ℝ) J (e ∘ c) s t 1) v =
      -mfderiv J 𝓘(ℝ,ℝ) (H ∘ e.symm) (e (c t)) v := by
  intro v
  have hd := e.contMDiffAt.mdifferentiableAt (x:=c t) (by simp)
  have hdi := e.symm.contMDiffAt.mdifferentiableAt (x:=e (c t)) (by simp)
  have hcurve := mfderiv_comp_mfderivWithin t hd hc ht
  have hinv := diffeomorph_mfderiv_inverse e.symm (e (c t))
  have hec : (mfderiv I J e (e.symm (e (c t))) : V →L[ℝ] W) =
      mfderiv I J e (c t) := by rw [e.symm_apply_apply]
  change (mfderiv I J e (e.symm (e (c t)))).comp
    (mfderiv J I e.symm (e (c t))) = ContinuousLinearMap.id ℝ W at hinv
  rw [hec] at hinv
  have hv := congrArg (fun L : W →L[ℝ] W => L v) hinv
  change mfderiv I J e (c t) (mfderiv J I e.symm (e (c t)) v) = v at hv
  have hcomp := mfderiv_comp_of_eq (x:=e (c t)) hH hdi (e.symm_apply_apply (c t))
  rw [hcurve,hcomp]
  have hHe : (mfderiv I 𝓘(ℝ,ℝ) H (e.symm (e (c t))) : V →L[ℝ] ℝ) =
      mfderiv I 𝓘(ℝ,ℝ) H (c t) := by rw [e.symm_apply_apply]
  rw [hHe]
  change ωN (e (c t)) (mfderiv I J e (c t)
    (mfderivWithin 𝓘(ℝ,ℝ) I c s t 1)) v =
      -mfderiv I 𝓘(ℝ,ℝ) H (c t) (mfderiv J I e.symm (e (c t)) v)
  have hn := he (c t) (mfderivWithin 𝓘(ℝ,ℝ) I c s t 1)
    (mfderiv J I e.symm (e (c t)) v)
  erw [hv] at hn
  exact hn.trans (hham _)

end NearbyLagrangian

namespace NearbyLagrangian.Transport
open Set Filter Function TopologicalSpace ContinuousLinearMap InnerProductSpace
open scoped Manifold ContDiff Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma mfderiv_open_inclusion (U : Opens (E × E)) (x : U) :
    (mfderiv 𝓘(ℝ,E × E) 𝓘(ℝ,E × E) (Subtype.val : U → E × E) x :
      (E × E) →L[ℝ] (E × E)) = ContinuousLinearMap.id ℝ (E × E) := by
  have he : (extChartAt 𝓘(ℝ,E × E) x : U → E × E) = Subtype.val := rfl
  rw [← he]
  exact mfderiv_extChartAt_self

omit [CompleteSpace E] in
lemma mfderiv_open_restriction (U : Opens (E × E)) {H : E × E → ℝ} {x : U}
    (hH : DifferentiableAt ℝ H (x:E × E)) :
    (mfderiv 𝓘(ℝ,E × E) 𝓘(ℝ,ℝ) (H ∘ Subtype.val : U → ℝ) x :
      (E × E) →L[ℝ] ℝ) = fderiv ℝ H (x:E × E) := by
  have hi : MDifferentiableAt 𝓘(ℝ,E × E) 𝓘(ℝ,E × E) (Subtype.val : U → E × E) x :=
    (contMDiff_subtype_val (n:=∞)).mdifferentiableAt (by simp)
  rw [mfderiv_comp x hH.mdifferentiableAt hi]
  erw [mfderiv_open_inclusion, ContinuousLinearMap.comp_id,mfderiv_eq_fderiv]

omit [CompleteSpace E] in
lemma fderivWithin_open_curve (U : Opens (E × E)) {c : ℝ → U} {s : Set ℝ} {t : ℝ}
    (hc : MDifferentiableWithinAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E × E) c s t)
    (ht : UniqueMDiffWithinAt 𝓘(ℝ,ℝ) s t) :
    fderivWithin ℝ (Subtype.val ∘ c : ℝ → E × E) s t =
      mfderivWithin 𝓘(ℝ,ℝ) 𝓘(ℝ,E × E) c s t := by
  have hi : MDifferentiableAt 𝓘(ℝ,E × E) 𝓘(ℝ,E × E) (Subtype.val : U → E × E) (c t) :=
    (contMDiff_subtype_val (n:=∞)).mdifferentiableAt (by simp)
  have hh := mfderiv_comp_mfderivWithin t hi hc ht
  erw [mfderivWithin_eq_fderivWithin,mfderiv_open_inclusion,
    ContinuousLinearMap.id_comp] at hh
  exact hh

variable {V A M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace A] {I : ModelWithCorners ℝ V A}
  [TopologicalSpace M] [ChartedSpace A M]

omit [CompleteSpace E] in

theorem hamiltonian_equation_open_chart (U : Opens (E × E))
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
    (hH : MDifferentiableAt I 𝓘(ℝ,ℝ) H (c t))
    (hham : ∀ v, form (c t) (mfderivWithin 𝓘(ℝ,ℝ) I c s t 1) v =
      -mfderiv I 𝓘(ℝ,ℝ) H (c t) v) :
    ∀ v,
      let d : ℝ → E × E := Subtype.val ∘ e ∘ c
      inner ℝ (fderivWithin ℝ d s t 1).2 v.1 - inner ℝ v.2 (fderivWithin ℝ d s t 1).1 =
        -fderiv ℝ K (d t) v := by
  have h := hamiltonian_equation_diffeomorph e form
    (fun _ u v => inner ℝ u.2 v.1 - inner ℝ v.2 u.1) he hc ht hH hham
  have hec := (e.contMDiffAt.mdifferentiableAt (by simp)).comp_mdifferentiableWithinAt t hc
  have hfun : H ∘ e.symm = (K ∘ Subtype.val : U → ℝ) := funext (fun x => (hKH x).symm)
  rw [hfun] at h
  erw [mfderiv_open_restriction U hK] at h
  intro v
  dsimp only
  rw [show (Subtype.val ∘ e ∘ c : ℝ → E × E) = Subtype.val ∘ (e ∘ c) from rfl,
    fderivWithin_open_curve U hec ht]
  exact h v

theorem open_chart_hamiltonian_curve_unique (U : Opens (E × E))
    (e : Diffeomorph I 𝓘(ℝ,E × E) M U ∞) (form : M → V → V → ℝ)
    (he : ∀ x u v,
      inner ℝ (mfderiv I 𝓘(ℝ,E × E) e x u).2 (mfderiv I 𝓘(ℝ,E × E) e x v).1 -
        inner ℝ (mfderiv I 𝓘(ℝ,E × E) e x v).2 (mfderiv I 𝓘(ℝ,E × E) e x u).1 = form x u v)
    {H : ℝ → M → ℝ} {K : ℝ × (E × E) → ℝ} {c : ℝ → M} {d : ℝ → E × E} {L : ℝ≥0}
    (hKH : ∀ t ∈ Icc (0:ℝ) 1, ∀ x : U, K (t,(x:E × E)) = H t (e.symm x))
    (hK : ∀ t ∈ Icc (0:ℝ) 1, Differentiable ℝ (fun x => K (t,x)))
    (hL : ∀ t, LipschitzWith L (fun x => hamiltonianField K (t,x)))
    (hc : ∀ t ∈ Icc (0:ℝ) 1, MDifferentiableWithinAt 𝓘(ℝ,ℝ) I c (Icc (0:ℝ) 1) t)
    (hH : ∀ t ∈ Icc (0:ℝ) 1, MDifferentiableAt I 𝓘(ℝ,ℝ) (H t) (c t))
    (hcH : ∀ t ∈ Icc (0:ℝ) 1, ∀ v,
      form (c t) (mfderivWithin 𝓘(ℝ,ℝ) I c (Icc (0:ℝ) 1) t 1) v =
        -mfderiv I 𝓘(ℝ,ℝ) (H t) (c t) v)
    (hd : ∀ t ∈ Icc (0:ℝ) 1, DifferentiableWithinAt ℝ d (Icc (0:ℝ) 1) t)
    (hdH : ∀ t ∈ Icc (0:ℝ) 1, ∀ v,
      inner ℝ (fderivWithin ℝ d (Icc (0:ℝ) 1) t 1).2 v.1 -
        inner ℝ v.2 (fderivWithin ℝ d (Icc (0:ℝ) 1) t 1).1 =
          -fderiv ℝ (fun x => K (t,x)) (d t) v)
    (h0 : (e (c 0) : E × E) = d 0) :
    EqOn (Subtype.val ∘ e ∘ c : ℝ → E × E) d (Icc (0:ℝ) 1) := by
  apply canonical_hamiltonian_curves_unique hL _ hd _ hdH h0
  · intro t ht
    exact ((contMDiff_subtype_val (U:=U) (n:=∞)).mdifferentiableAt (by simp)).comp_mdifferentiableWithinAt t
      ((e.contMDiffAt.mdifferentiableAt (by simp)).comp_mdifferentiableWithinAt t (hc t ht))
      |>.differentiableWithinAt
  · intro t ht
    exact hamiltonian_equation_open_chart U e form he (hKH t ht) (hK t ht _)
      (hc t ht) ((uniqueDiffOn_Icc (by norm_num : (0:ℝ)<1) t ht).uniqueMDiffWithinAt)
      (hH t ht) (hcH t ht)

end NearbyLagrangian.Transport

end

end OAI
