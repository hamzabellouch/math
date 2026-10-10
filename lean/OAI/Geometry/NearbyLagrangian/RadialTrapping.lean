import Mathlib

namespace OAI

/-! Compact radial Hamiltonian extensions and central trapping. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.RadialExtension
variable {V A M E : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace A] {I : ModelWithCorners ℝ V A}
  [TopologicalSpace M] [ChartedSpace A M]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def cutoffHamiltonian (H : M → ℝ) (ζ ξ : E → ℝ) (z : M × (E × E)) : ℝ :=
  H z.1 * ζ z.2.1 * ξ z.2.2

omit [CompleteSpace E] in
lemma mdifferentiableAt_cutoffHamiltonian {H : M → ℝ} {ζ ξ : E → ℝ}
    {z : M × (E × E)} (hH : MDifferentiableAt I 𝓘(ℝ,ℝ) H z.1)
    (hζ : DifferentiableAt ℝ ζ z.2.1) (hξ : DifferentiableAt ℝ ξ z.2.2) :
    MDifferentiableAt (I.prod 𝓘(ℝ,E × E)) 𝓘(ℝ,ℝ) (cutoffHamiltonian H ζ ξ) z :=
  ((hH.comp z mdifferentiableAt_fst).mul
    ((hζ.comp z.2 differentiableAt_fst).mdifferentiableAt.comp z mdifferentiableAt_snd)).mul
      ((hξ.comp z.2 differentiableAt_snd).mdifferentiableAt.comp z mdifferentiableAt_snd)

omit [CompleteSpace E] in
lemma cutoffHamiltonian_radial_derivative {H : M → ℝ} {ζ ξ : E → ℝ}
    {z : M × (E × E)} (hH : MDifferentiableAt I 𝓘(ℝ,ℝ) H z.1)
    (hζ : DifferentiableAt ℝ ζ z.2.1) (hξ : DifferentiableAt ℝ ξ z.2.2) (w : E × E) :
    mfderiv (I.prod 𝓘(ℝ,E × E)) 𝓘(ℝ,ℝ) (cutoffHamiltonian H ζ ξ) z (0,w) =
      H z.1 * ξ z.2.2 * fderiv ℝ ζ z.2.1 w.1 +
        H z.1 * ζ z.2.1 * fderiv ℝ ξ z.2.2 w.2 := by
  have hc := mfderiv_comp z.2 (mdifferentiableAt_cutoffHamiltonian hH hζ hξ)
    (mdifferentiableAt_const.prodMk mdifferentiableAt_id :
      MDifferentiableAt 𝓘(ℝ,E × E) (I.prod 𝓘(ℝ,E × E))
        (fun y : E × E => (z.1,y)) z.2)
  erw [mfderiv_prod_right] at hc
  have hfd := (((hζ.hasFDerivAt.comp z.2 hasFDerivAt_fst).const_mul (H z.1)).mul
    (hξ.hasFDerivAt.comp z.2 hasFDerivAt_snd)).fderiv
  have hv := congrArg (fun L : (E × E) →L[ℝ] ℝ => L w) hc
  rw [mfderiv_eq_fderiv] at hv
  change fderiv ℝ (fun y : E × E => H z.1 * ζ y.1 * ξ y.2) z.2 w =
    mfderiv (I.prod 𝓘(ℝ,E × E)) 𝓘(ℝ,ℝ) (cutoffHamiltonian H ζ ξ) z (0,w) at hv
  change fderiv ℝ (fun y : E × E => H z.1 * ζ y.1 * ξ y.2) z.2 = _ at hfd
  erw [hfd] at hv
  simp only [add_apply,smul_apply,smul_eq_mul,comp_apply] at hv
  rw [← hv]
  change H z.1 * ζ z.2.1 * fderiv ℝ ξ z.2.2 w.2 +
    ξ z.2.2 * (H z.1 * fderiv ℝ ζ z.2.1 w.1) = _
  ring

theorem cutoffHamiltonian_radial_equations
    {H : M → ℝ} {ζ ξ : E → ℝ} {z : M × (E × E)}
    (hH : MDifferentiableAt I 𝓘(ℝ,ℝ) H z.1)
    (hζ : DifferentiableAt ℝ ζ z.2.1) (hξ : DifferentiableAt ℝ ξ z.2.2)
    (form : M → V → V → ℝ) (hω : ∀ u, form z.1 u 0 = 0)
    (u : V × (E × E))
    (hham : ∀ (v : V × (E × E)), form z.1 u.1 v.1 +
      inner ℝ u.2.2 v.2.1 - inner ℝ v.2.2 u.2.1 =
        -mfderiv (I.prod 𝓘(ℝ,E × E)) 𝓘(ℝ,ℝ) (cutoffHamiltonian H ζ ξ) z v) :
    u.2.1 = (H z.1 * ζ z.2.1) • gradient ξ z.2.2 ∧
      u.2.2 = -(H z.1 * ξ z.2.2) • gradient ζ z.2.1 := by
  constructor
  · apply (ext_inner_right ℝ)
    intro v
    have h := hham (0,(0,v))
    rw [hω,cutoffHamiltonian_radial_derivative hH hζ hξ] at h
    simp only [inner_zero_right,map_zero,mul_zero,zero_add,zero_sub] at h
    rw [real_inner_comm,real_inner_smul_left,inner_gradient_left]
    exact neg_injective h
  · apply (ext_inner_right ℝ)
    intro v
    have h := hham (0,(v,0))
    rw [hω,cutoffHamiltonian_radial_derivative hH hζ hξ] at h
    simp only [inner_zero_left,map_zero,mul_zero,add_zero,zero_add,sub_zero] at h
    rw [real_inner_smul_left,inner_gradient_left]
    rw [neg_mul]
    exact h

end NearbyLagrangian.RadialExtension

namespace NearbyLagrangian.RadialExtension
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma norm_curve_le {p p' : ℝ → E} {M : ℝ} (hM : 0 ≤ M)
    (hp : ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt p (p' t) (Icc (0:ℝ) 1) t)
    (hb : ∀ t ∈ Icc (0:ℝ) 1, ‖p' t‖ ≤ M) (hp0 : p 0 = 0)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : ‖p t‖ ≤ M := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hp hb (convex_Icc 0 1)
    (left_mem_Icc.mpr (by norm_num : (0:ℝ) ≤ 1)) ht
  simpa only [hp0,sub_zero,Real.norm_eq_abs,abs_of_nonneg ht.1] using
    h.trans (mul_le_of_le_one_right hM (by simpa only [sub_zero,Real.norm_eq_abs,abs_of_nonneg ht.1] using ht.2))

omit [CompleteSpace E] in
lemma curve_constant {a : ℝ → E}
    (ha : ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt a 0 (Icc (0:ℝ) 1) t)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : a t = a 0 := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le ha (C:=0)
    (by intro s hs; simp) (convex_Icc 0 1) (left_mem_Icc.mpr (by norm_num : (0:ℝ) ≤ 1)) ht
  exact sub_eq_zero.mp (norm_le_zero_iff.mp (by simpa using h))

lemma gradient_plateau {ξ : E → ℝ} {R : ℝ} (hξ : ∀ u, ‖u‖ ≤ R → ξ u = 1)
    {p : E} (hp : ‖p‖ < R) : gradient ξ p = 0 := by
  have he : ξ =ᶠ[𝓝 p] fun _ => (1:ℝ) := by
    filter_upwards [continuous_norm.continuousAt.eventually (gt_mem_nhds hp)] with u hu
    exact hξ u (le_of_lt hu)
  simpa using he.gradient_eq

theorem radial_trapping {h : ℝ → ℝ} {ζ ξ : E → ℝ} {α p : ℝ → E}
    {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hh : ∀ t ∈ Icc (0:ℝ) 1, |h t| ≤ A)
    (hζ : ∀ a, ‖gradient ζ a‖ ≤ C)
    (hξ : ∀ w, ξ w ∈ Icc (0:ℝ) 1)
    (hplateau : ∀ w, ‖w‖ ≤ A*C+1 → ξ w = 1)
    (hp0 : p 0 = 0)
    (hp : ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt p
      (-(h t * ξ (p t)) • gradient ζ (α t)) (Icc (0:ℝ) 1) t)
    (hα : ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt α
      ((h t * ζ (α t)) • gradient ξ (p t)) (Icc (0:ℝ) 1) t) :
    ∀ t ∈ Icc (0:ℝ) 1, ‖p t‖ ≤ A*C ∧ ξ (p t) = 1 ∧
      gradient ξ (p t) = 0 ∧ α t = α 0 := by
  have hb : ∀ t ∈ Icc (0:ℝ) 1, ‖-(h t * ξ (p t)) • gradient ζ (α t)‖ ≤ A*C := by
    intro t ht
    rw [norm_smul,Real.norm_eq_abs,abs_neg,abs_mul,abs_of_nonneg (hξ (p t)).1]
    exact mul_le_mul (by nlinarith [hh t ht,(hξ (p t)).1,(hξ (p t)).2,abs_nonneg (h t)])
      (hζ (α t)) (norm_nonneg _) hA
  have hbound : ∀ t ∈ Icc (0:ℝ) 1, ‖p t‖ ≤ A*C := fun t ht =>
    norm_curve_le (mul_nonneg hA hC) hp hb hp0 ht
  have hgrad : ∀ t ∈ Icc (0:ℝ) 1, gradient ξ (p t) = 0 := fun t ht =>
    gradient_plateau hplateau (lt_of_le_of_lt (hbound t ht) (lt_add_one _))
  have hac : ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt α 0 (Icc (0:ℝ) 1) t := by
    intro t ht
    simpa only [hgrad t ht,smul_zero] using hα t ht
  intro t ht
  exact ⟨hbound t ht,hplateau (p t) (le_trans (hbound t ht) (by linarith)),
    hgrad t ht,curve_constant hac ht⟩

theorem radial_trapping_central {h : ℝ → ℝ} {ζ ξ : E → ℝ} {α p : ℝ → E}
    {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hh : ∀ t ∈ Icc (0:ℝ) 1, |h t| ≤ A)
    (hζ : ∀ a, ‖gradient ζ a‖ ≤ C)
    (hξ : ∀ w, ξ w ∈ Icc (0:ℝ) 1)
    (hplateau : ∀ w, ‖w‖ ≤ A*C+1 → ξ w = 1)
    (hp0 : p 0 = 0)
    (hp : ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt p
      (-(h t * ξ (p t)) • gradient ζ (α t)) (Icc (0:ℝ) 1) t)
    (hα : ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt α
      ((h t * ζ (α t)) • gradient ξ (p t)) (Icc (0:ℝ) 1) t)
    (hcentral : ζ =ᶠ[𝓝 (α 0)] fun _ => (1:ℝ)) :
    ∀ t ∈ Icc (0:ℝ) 1, α t = α 0 ∧ p t = 0 ∧ ζ (α t) = 1 ∧ ξ (p t) = 1 := by
  have h := radial_trapping hA hC hh hζ hξ hplateau hp0 hp hα
  have hg : gradient ζ (α 0) = 0 := by simpa using hcentral.gradient_eq
  have hpc : ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt p 0 (Icc (0:ℝ) 1) t := by
    intro t ht
    simpa only [(h t ht).2.2.2,hg,smul_zero] using hp t ht
  intro t ht
  exact ⟨(h t ht).2.2.2,(curve_constant hpc ht).trans hp0,
    by rw [(h t ht).2.2.2]; exact hcentral.self_of_nhds,(h t ht).2.1⟩
end NearbyLagrangian.RadialExtension

namespace NearbyLagrangian.RadialExtension
open scoped Manifold ContDiff Topology
open Set ContinuousLinearMap
variable {V A M E : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace A] {I : ModelWithCorners ℝ V A}
  [TopologicalSpace M] [ChartedSpace A M]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma radialCurve_hasDerivWithinAt {c : ℝ → M × (E × E)} {s : Set ℝ} {t : ℝ}
    (hc : MDifferentiableWithinAt 𝓘(ℝ,ℝ) (I.prod 𝓘(ℝ,E × E)) c s t)
    (ht : UniqueMDiffWithinAt 𝓘(ℝ,ℝ) s t) :
    HasDerivWithinAt (fun r => (c r).2)
      (mfderivWithin 𝓘(ℝ,ℝ) (I.prod 𝓘(ℝ,E × E)) c s t 1).2 s t := by
  have hd : DifferentiableWithinAt ℝ (fun r => (c r).2) s t :=
    hc.snd.differentiableWithinAt
  have he := mfderiv_comp_mfderivWithin t (mdifferentiableAt_snd (I:=I)
    (I':=𝓘(ℝ,E × E))) hc ht
  erw [mfderiv_snd,mfderivWithin_eq_fderivWithin] at he
  have hv := hd.hasFDerivWithinAt.hasDerivWithinAt
  change HasDerivWithinAt _ (fderivWithin ℝ (fun r => (c r).2) s t 1) s t at hv
  erw [he] at hv
  exact hv

theorem hamiltonian_radial_trapping
    {H : ℝ → M → ℝ} {ζ ξ : E → ℝ} {c : ℝ → M × (E × E)}
    (hc : ∀ t ∈ Icc (0:ℝ) 1,
      MDifferentiableWithinAt 𝓘(ℝ,ℝ) (I.prod 𝓘(ℝ,E × E)) c (Icc (0:ℝ) 1) t)
    (hH : ∀ t ∈ Icc (0:ℝ) 1, MDifferentiableAt I 𝓘(ℝ,ℝ) (H t) (c t).1)
    (hζd : Differentiable ℝ ζ) (hξd : Differentiable ℝ ξ)
    (form : M → V → V → ℝ) (hω : ∀ x u, form x u 0 = 0)
    (hham : ∀ t ∈ Icc (0:ℝ) 1, ∀ v : V × (E × E),
      let u := mfderivWithin 𝓘(ℝ,ℝ) (I.prod 𝓘(ℝ,E × E)) c (Icc (0:ℝ) 1) t 1
      form (c t).1 u.1 v.1 + inner ℝ u.2.2 v.2.1 - inner ℝ v.2.2 u.2.1 =
        -mfderiv (I.prod 𝓘(ℝ,E × E)) 𝓘(ℝ,ℝ) (cutoffHamiltonian (H t) ζ ξ) (c t) v)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hbound : ∀ t ∈ Icc (0:ℝ) 1, |H t (c t).1| ≤ B)
    (hζ : ∀ a, ‖gradient ζ a‖ ≤ C)
    (hξ : ∀ w, ξ w ∈ Icc (0:ℝ) 1)
    (hplateau : ∀ w, ‖w‖ ≤ B*C+1 → ξ w = 1)
    (hp0 : (c 0).2.2 = 0) :
    ∀ t ∈ Icc (0:ℝ) 1, ‖(c t).2.2‖ ≤ B*C ∧ ξ (c t).2.2 = 1 ∧
      gradient ξ (c t).2.2 = 0 ∧ (c t).2.1 = (c 0).2.1 := by
  have heq t (ht : t ∈ Icc (0:ℝ) 1) := cutoffHamiltonian_radial_equations
    (hH t ht) (hζd _ ) (hξd _) form (hω _) _ (hham t ht)
  have hrad t (ht : t ∈ Icc (0:ℝ) 1) := radialCurve_hasDerivWithinAt (hc t ht)
    ((uniqueDiffOn_Icc (by norm_num : (0:ℝ) < 1) t ht).uniqueMDiffWithinAt)
  apply radial_trapping hB hC hbound hζ hξ hplateau hp0
  · intro t ht
    have hf : HasFDerivWithinAt _ _ _ _ := (hrad t ht).snd
    have h := hf.hasDerivWithinAt
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      one_smul] at h
    change HasDerivWithinAt (fun r => (c r).2.2)
      (mfderivWithin 𝓘(ℝ,ℝ) (I.prod 𝓘(ℝ,E × E)) c (Icc (0:ℝ) 1) t 1).2.2 _ _ at h
    erw [(heq t ht).2] at h
    exact h
  · intro t ht
    have hf : HasFDerivWithinAt _ _ _ _ := (hrad t ht).fst
    have h := hf.hasDerivWithinAt
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      one_smul] at h
    change HasDerivWithinAt (fun r => (c r).2.1)
      (mfderivWithin 𝓘(ℝ,ℝ) (I.prod 𝓘(ℝ,E × E)) c (Icc (0:ℝ) 1) t 1).2.1 _ _ at h
    erw [(heq t ht).1] at h
    exact h

end NearbyLagrangian.RadialExtension

namespace NearbyLagrangian.RadialExtension
open scoped Manifold ContDiff Topology
open Set Filter ContinuousLinearMap
variable {V A M E : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace A] {I : ModelWithCorners ℝ V A}
  [TopologicalSpace M] [ChartedSpace A M]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma cutoffHamiltonian_plateau_derivative {H : M → ℝ} {ζ ξ : E → ℝ}
    {z : M × (E × E)} (hH : MDifferentiableAt I 𝓘(ℝ,ℝ) H z.1)
    (hζ : ζ =ᶠ[𝓝 z.2.1] fun _ => (1:ℝ))
    (hξ : ξ =ᶠ[𝓝 z.2.2] fun _ => (1:ℝ)) (v : V × (E × E)) :
    mfderiv (I.prod 𝓘(ℝ,E × E)) 𝓘(ℝ,ℝ) (cutoffHamiltonian H ζ ξ) z v =
      mfderiv I 𝓘(ℝ,ℝ) H z.1 v.1 := by
  have he : cutoffHamiltonian H ζ ξ =ᶠ[𝓝 z] fun y => H y.1 := by
    filter_upwards [hζ.comp_tendsto (continuous_fst.comp continuous_snd).continuousAt,
      hξ.comp_tendsto (continuous_snd.comp continuous_snd).continuousAt] with y hy hz
    change ζ y.2.1 = 1 at hy
    change ξ y.2.2 = 1 at hz
    simp only [cutoffHamiltonian,hy,hz,mul_one]
  rw [he.mfderiv_eq]
  have hd := mfderiv_comp z hH (mdifferentiableAt_fst (I:=I) (I':=𝓘(ℝ,E × E)))
  erw [hd,mfderiv_fst]
  rfl

theorem central_product_hamiltonian_curve
    {H : ℝ → M → ℝ} {ζ ξ : E → ℝ} {c : ℝ → M} {a : E}
    (hζ : ζ =ᶠ[𝓝 a] fun _ => (1:ℝ))
    (hξ : ξ =ᶠ[𝓝 (0:E)] fun _ => (1:ℝ))
    (form : M → V → V → ℝ) {s : Set ℝ} {t : ℝ}
    (hc : MDifferentiableWithinAt 𝓘(ℝ,ℝ) I c s t)
    (ht : UniqueMDiffWithinAt 𝓘(ℝ,ℝ) s t)
    (hH : MDifferentiableAt I 𝓘(ℝ,ℝ) (H t) (c t))
    (hham : ∀ v, form (c t) (mfderivWithin 𝓘(ℝ,ℝ) I c s t 1) v =
      -mfderiv I 𝓘(ℝ,ℝ) (H t) (c t) v) :
    ∀ v : V × (E × E),
      let d : ℝ → M × (E × E) := fun r => (c r,(a,0))
      let u := mfderivWithin 𝓘(ℝ,ℝ) (I.prod 𝓘(ℝ,E × E)) d s t 1
      form (c t) u.1 v.1 + inner ℝ u.2.2 v.2.1 - inner ℝ v.2.2 u.2.1 =
        -mfderiv (I.prod 𝓘(ℝ,E × E)) 𝓘(ℝ,ℝ) (cutoffHamiltonian (H t) ζ ξ)
          (c t,(a,0)) v := by
  intro v
  dsimp only
  rw [mfderivWithin_prodMk hc mdifferentiableWithinAt_const ht,mfderivWithin_const]
  rw [cutoffHamiltonian_plateau_derivative hH hζ hξ]
  change form (c t) (mfderivWithin 𝓘(ℝ,ℝ) I c s t 1) v.1 +
    inner ℝ (0:E) v.2.1 - inner ℝ v.2.2 (0:E) = _
  simp only [inner_zero_left,inner_zero_right,add_zero,sub_zero]
  convert hham v.1 using 1
  rfl

end NearbyLagrangian.RadialExtension

end

end OAI
