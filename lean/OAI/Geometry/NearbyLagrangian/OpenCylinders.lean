import Mathlib
import OAI.Geometry.NearbyLagrangian.RadialTrapping
import OAI.Geometry.NearbyLagrangian.HamiltonianCharts

namespace OAI

/-! Open cylinder coordinates and regular compact Hamiltonian extensions. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.RadialExtension
open scoped Manifold ContDiff Topology
open Set Filter Function TopologicalSpace ContinuousLinearMap
variable {V A M E : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace A] {I : ModelWithCorners ℝ V A}
  [TopologicalSpace M] [ChartedSpace A M]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def radialInclusion (U : Opens (E × E)) (z : M × U) : M × (E × E) :=
  (z.1,(z.2:E × E))

lemma contMDiff_radialInclusion (U : Opens (E × E)) :
    ContMDiff (I.prod 𝓘(ℝ,E × E)) (I.prod 𝓘(ℝ,E × E)) ∞ (radialInclusion (M:=M) U) :=
  contMDiff_fst.prodMk (contMDiff_subtype_val.comp contMDiff_snd)

lemma mfderiv_radialInclusion (U : Opens (E × E)) (z : M × U) :
    (mfderiv (I.prod 𝓘(ℝ,E × E)) (I.prod 𝓘(ℝ,E × E)) (radialInclusion (M:=M) U) z :
      (V × (E × E)) →L[ℝ] (V × (E × E))) = ContinuousLinearMap.id ℝ _ := by
  rw [show radialInclusion (M:=M) U = fun y : M × U =>
    (y.1, (Subtype.val ∘ Prod.snd) y) from rfl]
  rw [mfderiv_prodMk mdifferentiableAt_fst
    ((contMDiff_subtype_val (U:=U) (n:=∞)).mdifferentiableAt (by simp) |>.comp z mdifferentiableAt_snd)]
  rw [mfderiv_comp z ((contMDiff_subtype_val (U:=U) (n:=∞)).mdifferentiableAt (by simp))
    mdifferentiableAt_snd]
  erw [mfderiv_fst, mfderiv_snd, NearbyLagrangian.Transport.mfderiv_open_inclusion,
    ContinuousLinearMap.id_comp]
  rfl

lemma mfderiv_radial_restriction (U : Opens (E × E)) {H : M × (E × E) → ℝ}
    {z : M × U} (hH : MDifferentiableAt (I.prod 𝓘(ℝ,E × E)) 𝓘(ℝ,ℝ) H (radialInclusion U z)) :
    (mfderiv (I.prod 𝓘(ℝ,E × E)) 𝓘(ℝ,ℝ) (H ∘ radialInclusion U) z :
      (V × (E × E)) →L[ℝ] ℝ) =
      mfderiv (I.prod 𝓘(ℝ,E × E)) 𝓘(ℝ,ℝ) H (radialInclusion U z) := by
  rw [mfderiv_comp z hH ((contMDiff_radialInclusion U).mdifferentiableAt (by simp))]
  erw [mfderiv_radialInclusion,ContinuousLinearMap.comp_id]

lemma mfderivWithin_radial_curve (U : Opens (E × E)) {c : ℝ → M × U}
    {s : Set ℝ} {t : ℝ}
    (hc : MDifferentiableWithinAt 𝓘(ℝ,ℝ) (I.prod 𝓘(ℝ,E × E)) c s t)
    (ht : UniqueMDiffWithinAt 𝓘(ℝ,ℝ) s t) :
    (mfderivWithin 𝓘(ℝ,ℝ) (I.prod 𝓘(ℝ,E × E)) (radialInclusion U ∘ c) s t :
      ℝ →L[ℝ] (V × (E × E))) =
      mfderivWithin 𝓘(ℝ,ℝ) (I.prod 𝓘(ℝ,E × E)) c s t := by
  rw [mfderiv_comp_mfderivWithin t ((contMDiff_radialInclusion U).mdifferentiableAt (by simp)) hc ht]
  erw [mfderiv_radialInclusion,ContinuousLinearMap.id_comp]

theorem central_open_product_hamiltonian_curve (U : Opens (E × E))
    {H : ℝ → M → ℝ} {ζ ξ : E → ℝ} {c : ℝ → M} {a : E}
    (ha : (a,0) ∈ U) (hζ : ζ =ᶠ[𝓝 a] fun _ => (1:ℝ))
    (hξ : ξ =ᶠ[𝓝 (0:E)] fun _ => (1:ℝ))
    (form : M → V → V → ℝ) {s : Set ℝ} {t : ℝ}
    (hc : MDifferentiableWithinAt 𝓘(ℝ,ℝ) I c s t)
    (ht : UniqueMDiffWithinAt 𝓘(ℝ,ℝ) s t)
    (hH : MDifferentiableAt I 𝓘(ℝ,ℝ) (H t) (c t))
    (hham : ∀ v, form (c t) (mfderivWithin 𝓘(ℝ,ℝ) I c s t 1) v =
      -mfderiv I 𝓘(ℝ,ℝ) (H t) (c t) v) :
    ∀ v : V × (E × E),
      let d : ℝ → M × U := fun r => (c r,⟨(a,0),ha⟩)
      let u := mfderivWithin 𝓘(ℝ,ℝ) (I.prod 𝓘(ℝ,E × E)) d s t 1
      form (c t) u.1 v.1 + inner ℝ u.2.2 v.2.1 - inner ℝ v.2.2 u.2.1 =
        -mfderiv (I.prod 𝓘(ℝ,E × E)) 𝓘(ℝ,ℝ)
          (cutoffHamiltonian (H t) ζ ξ ∘ radialInclusion U) (c t,⟨(a,0),ha⟩) v := by
  intro v
  have hζd : DifferentiableAt ℝ ζ a := hζ.differentiableAt_iff.mpr (differentiableAt_const 1)
  have hξd : DifferentiableAt ℝ ξ (0:E) := hξ.differentiableAt_iff.mpr (differentiableAt_const 1)
  dsimp only
  erw [mfderiv_radial_restriction U (mdifferentiableAt_cutoffHamiltonian hH hζd hξd)]
  rw [mfderivWithin_prodMk hc mdifferentiableWithinAt_const ht,mfderivWithin_const]
  change form (c t) (mfderivWithin 𝓘(ℝ,ℝ) I c s t 1) v.1 +
    inner ℝ (0:E) v.2.1 - inner ℝ v.2.2 (0:E) =
      -mfderiv (I.prod 𝓘(ℝ,E × E)) 𝓘(ℝ,ℝ) (cutoffHamiltonian (H t) ζ ξ) (c t,(a,0)) v
  rw [cutoffHamiltonian_plateau_derivative hH hζ hξ]
  simp only [inner_zero_left,inner_zero_right,add_zero,sub_zero]
  convert hham v.1 using 1
  rfl

variable [CompleteSpace E]

theorem hamiltonian_open_radial_trapping (U : Opens (E × E))
    {H : ℝ → M → ℝ} {ζ ξ : E → ℝ} {c : ℝ → M × U}
    (hc : ∀ t ∈ Icc (0:ℝ) 1,
      MDifferentiableWithinAt 𝓘(ℝ,ℝ) (I.prod 𝓘(ℝ,E × E)) c (Icc (0:ℝ) 1) t)
    (hH : ∀ t ∈ Icc (0:ℝ) 1, MDifferentiableAt I 𝓘(ℝ,ℝ) (H t) (c t).1)
    (hζd : Differentiable ℝ ζ) (hξd : Differentiable ℝ ξ)
    (form : M → V → V → ℝ) (hω : ∀ x u, form x u 0 = 0)
    (hham : ∀ t ∈ Icc (0:ℝ) 1, ∀ v : V × (E × E),
      let u := mfderivWithin 𝓘(ℝ,ℝ) (I.prod 𝓘(ℝ,E × E)) c (Icc (0:ℝ) 1) t 1
      form (c t).1 u.1 v.1 + inner ℝ u.2.2 v.2.1 - inner ℝ v.2.2 u.2.1 =
        -mfderiv (I.prod 𝓘(ℝ,E × E)) 𝓘(ℝ,ℝ)
          (cutoffHamiltonian (H t) ζ ξ ∘ radialInclusion U) (c t) v)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hbound : ∀ t ∈ Icc (0:ℝ) 1, |H t (c t).1| ≤ B)
    (hζ : ∀ a, ‖gradient ζ a‖ ≤ C)
    (hξ : ∀ w, ξ w ∈ Icc (0:ℝ) 1)
    (hplateau : ∀ w, ‖w‖ ≤ B*C+1 → ξ w = 1)
    (hp0 : ((c 0).2:E × E).2 = 0) :
    ∀ t ∈ Icc (0:ℝ) 1, ‖((c t).2:E × E).2‖ ≤ B*C ∧
      ξ ((c t).2:E × E).2 = 1 ∧ gradient ξ ((c t).2:E × E).2 = 0 ∧
      ((c t).2:E × E).1 = ((c 0).2:E × E).1 := by
  apply hamiltonian_radial_trapping (c := radialInclusion U ∘ c) _ hH hζd hξd form hω _
    hB hC hbound hζ hξ hplateau hp0
  · intro t ht
    exact ((contMDiff_radialInclusion U).mdifferentiableAt (by simp)).comp_mdifferentiableWithinAt t (hc t ht)
  · intro t ht v
    dsimp only
    rw [mfderivWithin_radial_curve U (hc t ht)
      ((uniqueDiffOn_Icc (by norm_num : (0:ℝ)<1) t ht).uniqueMDiffWithinAt)]
    have h := hham t ht v
    dsimp only at h
    erw [mfderiv_radial_restriction U
      (mdifferentiableAt_cutoffHamiltonian (hH t ht) (hζd _) (hξd _))] at h
    exact h

end NearbyLagrangian.RadialExtension

namespace NearbyLagrangian.RadialExtension
open scoped Manifold ContDiff Topology
open Set Function TopologicalSpace
variable {V A M E : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace A] {I : ModelWithCorners ℝ V A}
  [TopologicalSpace M] [ChartedSpace A M]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma contMDiff_cutoffHamiltonian {H : ℝ → M → ℝ} {ζ ξ : E → ℝ}
    (hH : ContMDiff (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞ (fun z : ℝ × M => H z.1 z.2))
    (hζ : ContDiff ℝ ∞ ζ) (hξ : ContDiff ℝ ∞ ξ) :
    ContMDiff (𝓘(ℝ,ℝ).prod (I.prod 𝓘(ℝ,E × E))) 𝓘(ℝ,ℝ) ∞
      (fun z : ℝ × (M × (E × E)) => cutoffHamiltonian (H z.1) ζ ξ z.2) := by
  exact ((hH.comp (contMDiff_fst.prodMk (contMDiff_fst.comp contMDiff_snd))).mul
    (hζ.contMDiff.comp (contDiff_fst.contMDiff.comp (contMDiff_snd.comp contMDiff_snd)))).mul
      (hξ.contMDiff.comp (contDiff_snd.contMDiff.comp (contMDiff_snd.comp contMDiff_snd)))

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace A] [ChartedSpace A M]
  [InnerProductSpace ℝ E] in

theorem uniformCompactSupport_open_radial (U : Opens (E × E))
    {H : ℝ → M → ℝ} {ζ ξ : E → ℝ} {K : Set M} (hK : IsCompact K)
    (hH : ∀ t, Function.support (H t) ⊆ K)
    (hζ : HasCompactSupport ζ) (hξ : HasCompactSupport ξ)
    (hU : tsupport ζ ×ˢ tsupport ξ ⊆ (U:Set (E × E))) :
    ∃ C : Set (M × U), IsCompact C ∧ ∀ t,
      Function.support (cutoffHamiltonian (H t) ζ ξ ∘ radialInclusion U) ⊆ C := by
  let C := radialInclusion (M:=M) U ⁻¹' (K ×ˢ (tsupport ζ ×ˢ tsupport ξ))
  have he : Topology.IsEmbedding (radialInclusion (M:=M) U) :=
    Topology.IsEmbedding.id.prodMap Topology.IsEmbedding.subtypeVal
  have hr : K ×ˢ (tsupport ζ ×ˢ tsupport ξ) ⊆ range (radialInclusion (M:=M) U) := by
    intro z hz
    exact ⟨(z.1,⟨z.2,hU hz.2⟩),rfl⟩
  refine ⟨C,(he.isInducing.isCompact_preimage_iff hr).mpr (hK.prod (hζ.prod hξ)),?_⟩
  intro t z hz
  have hne : H t z.1 * ζ (z.2:E × E).1 * ξ (z.2:E × E).2 ≠ 0 := hz
  have h₁ := (mul_ne_zero_iff.mp hne).1
  exact ⟨hH t (mul_ne_zero_iff.mp h₁).1,
    subset_tsupport _ (mul_ne_zero_iff.mp h₁).2,subset_tsupport _ (mul_ne_zero_iff.mp hne).2⟩

end NearbyLagrangian.RadialExtension

namespace NearbyLagrangian.Transport
open Set Filter
open scoped Manifold ContDiff Topology
variable {V M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M] [ChartedSpace V M]

def manifoldFlatHamiltonian (H : ℝ → M → ℝ) (z : ℝ × M) : ℝ :=
  deriv Real.smoothTransition z.1 * H (Real.smoothTransition z.1) z.2

lemma contMDiff_flat_time {H : ℝ → M → ℝ}
    (hH : ContMDiffOn (𝓘(ℝ,ℝ).prod 𝓘(ℝ,V)) 𝓘(ℝ,ℝ) ∞
      (fun z : ℝ × M => H z.1 z.2) (Icc (0:ℝ) 1 ×ˢ univ)) :
    ContMDiff (𝓘(ℝ,ℝ).prod 𝓘(ℝ,V)) 𝓘(ℝ,ℝ) ∞
      (fun z : ℝ × M => H (Real.smoothTransition z.1) z.2) :=
  hH.comp_contMDiff
    ((Real.smoothTransition.contDiff.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)
    (fun z => ⟨smoothTime_mem z.1,mem_univ _⟩)

lemma contMDiff_manifoldFlatHamiltonian {H : ℝ → M → ℝ}
    (hH : ContMDiffOn (𝓘(ℝ,ℝ).prod 𝓘(ℝ,V)) 𝓘(ℝ,ℝ) ∞
      (fun z : ℝ × M => H z.1 z.2) (Icc (0:ℝ) 1 ×ˢ univ)) :
    ContMDiff (𝓘(ℝ,ℝ).prod 𝓘(ℝ,V)) 𝓘(ℝ,ℝ) ∞
      (manifoldFlatHamiltonian H) := by
  have hd : ContDiff ℝ ∞ (deriv Real.smoothTransition) :=
    (contDiff_infty_iff_deriv.mp Real.smoothTransition.contDiff).2
  exact (hd.contMDiff.comp contMDiff_fst).mul (contMDiff_flat_time hH)

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [ChartedSpace V M] in
lemma compactSupport_manifoldFlatHamiltonian [R1Space M] {H : ℝ → M → ℝ} {K : Set M}
    (hK : IsCompact K)
    (hs : ∀ t ∈ Icc (0:ℝ) 1, Function.support (H t) ⊆ K) :
    HasCompactSupport (manifoldFlatHamiltonian H) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc.prod hK)
  intro z hz
  change deriv Real.smoothTransition z.1 * H (Real.smoothTransition z.1) z.2 ≠ 0 at hz
  have ht : z.1 ∈ Icc (0:ℝ) 1 := by
    by_contra hn
    exact hz (by rw [smoothTime_deriv_zero hn,zero_mul])
  exact ⟨ht,hs _ (smoothTime_mem _) (right_ne_zero_of_mul hz)⟩

end NearbyLagrangian.Transport

namespace NearbyLagrangian.Transport
open Set Function TopologicalSpace
open scoped Manifold ContDiff Topology
variable {V M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M] [ChartedSpace V M]

def timeOpen (U : Opens M) : Opens (ℝ × M) :=
  ⟨univ ×ˢ (U:Set M),isOpen_univ.prod U.isOpen⟩

def timeOpenDiffeomorph (U : Opens M) :
    Diffeomorph (𝓘(ℝ,ℝ).prod 𝓘(ℝ,V)) (𝓘(ℝ,ℝ).prod 𝓘(ℝ,V))
      (ℝ × U) (timeOpen U) ∞ where
  toFun z := ⟨(z.1,(z.2:M)),⟨mem_univ _,z.2.property⟩⟩
  invFun z := (z.val.1,⟨z.val.2,z.property.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (timeOpen U) _).mp
    exact contMDiff_fst.prodMk (contMDiff_subtype_val.comp contMDiff_snd)
  contMDiff_invFun := by
    apply ContMDiff.prodMk (contMDiff_fst.comp contMDiff_subtype_val)
    apply (ContMDiff.subtypeVal_comp_iff U _).mp
    exact contMDiff_snd.comp contMDiff_subtype_val

def extendedFlatHamiltonian (U : Opens M) (H : ℝ → U → ℝ) : ℝ × M → ℝ :=
  Subtype.val.extend (manifoldFlatHamiltonian H ∘ (timeOpenDiffeomorph (V:=V) U).symm) 0

lemma extendedFlatHamiltonian_apply (U : Opens M) (H : ℝ → U → ℝ) (t : ℝ) (x : U) :
    extendedFlatHamiltonian (V:=V) U H (t,(x:M)) = manifoldFlatHamiltonian H (t,x) := by
  exact Subtype.val_injective.extend_apply _ _ ((timeOpenDiffeomorph (V:=V) U) (t,x))

lemma extendedFlatHamiltonian_eq_zero (U : Opens M) (H : ℝ → U → ℝ)
    (t : ℝ) {x : M} (hx : x ∉ U) : extendedFlatHamiltonian (V:=V) U H (t,x) = 0 := by
  unfold extendedFlatHamiltonian
  apply Function.extend_apply'
  rintro ⟨z,hz⟩
  exact hx (hz ▸ z.property).2

lemma compactSupport_extendedFlatHamiltonian [T2Space M]
    (U : Opens M) {H : ℝ → U → ℝ} {K : Set U} (hK : IsCompact K)
    (hs : ∀ t ∈ Icc (0:ℝ) 1, Function.support (H t) ⊆ K) :
    HasCompactSupport (extendedFlatHamiltonian (V:=V) U H) := by
  have h := (compactSupport_manifoldFlatHamiltonian hK hs).comp_homeomorph
    (timeOpenDiffeomorph (V:=V) U).symm.toHomeomorph
  exact h.extend_zero continuous_subtype_val

lemma contMDiff_extendedFlatHamiltonian [T2Space M]
    (U : Opens M) {H : ℝ → U → ℝ} {K : Set U} (hK : IsCompact K)
    (hs : ∀ t ∈ Icc (0:ℝ) 1, Function.support (H t) ⊆ K)
    (hH : ContMDiffOn (𝓘(ℝ,ℝ).prod 𝓘(ℝ,V)) 𝓘(ℝ,ℝ) ∞
      (fun z : ℝ × U => H z.1 z.2) (Icc (0:ℝ) 1 ×ˢ univ)) :
    ContMDiff (𝓘(ℝ,ℝ).prod 𝓘(ℝ,V)) 𝓘(ℝ,ℝ) ∞ (extendedFlatHamiltonian (V:=V) U H) := by
  have h := (compactSupport_manifoldFlatHamiltonian hK hs).comp_homeomorph
    (timeOpenDiffeomorph (V:=V) U).symm.toHomeomorph
  exact ContMDiff.extend_zero h ((contMDiff_manifoldFlatHamiltonian hH).comp
    (timeOpenDiffeomorph (V:=V) U).symm.contMDiff)

lemma uniformCompactSupport_extendedFlatHamiltonian [T2Space M]
    (U : Opens M) {H : ℝ → U → ℝ} {K : Set U} (hK : IsCompact K)
    (hs : ∀ t ∈ Icc (0:ℝ) 1, Function.support (H t) ⊆ K) :
    ∃ C : Set M, IsCompact C ∧ ∀ t : ℝ,
      Function.support (fun x => extendedFlatHamiltonian (V:=V) U H (t,x)) ⊆ C := by
  let C := Prod.snd '' tsupport (extendedFlatHamiltonian (V:=V) U H)
  refine ⟨C,(compactSupport_extendedFlatHamiltonian (V:=V) U hK hs).image continuous_snd,?_⟩
  intro t x hx
  exact ⟨(t,x),subset_tsupport _ hx,rfl⟩

end NearbyLagrangian.Transport

namespace NearbyLagrangian.RadialExtension
open scoped Manifold ContDiff Topology
open Set Function TopologicalSpace Transport
variable {V A M F G : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace A] {I : ModelWithCorners ℝ V A}
  [TopologicalSpace M] [ChartedSpace A M]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma contMDiffOn_open_cutoffHamiltonian (U : Opens (F × F))
    {H : ℝ → M → ℝ} {ζ ξ : F → ℝ}
    (hH : ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
      (fun z : ℝ × M => H z.1 z.2) (Icc (0:ℝ) 1 ×ˢ univ))
    (hζ : ContDiff ℝ ∞ ζ) (hξ : ContDiff ℝ ∞ ξ) :
    ContMDiffOn (𝓘(ℝ,ℝ).prod (I.prod 𝓘(ℝ,F × F))) 𝓘(ℝ,ℝ) ∞
      (fun z : ℝ × (M × U) => (cutoffHamiltonian (H z.1) ζ ξ ∘ radialInclusion U) z.2)
      (Icc (0:ℝ) 1 ×ˢ univ) := by
  have h₁ : ContMDiffOn (𝓘(ℝ,ℝ).prod (I.prod 𝓘(ℝ,F × F))) 𝓘(ℝ,ℝ) ∞
      (fun z : ℝ × (M × U) => H z.1 z.2.1) (Icc (0:ℝ) 1 ×ˢ univ) := hH.comp
    ((contMDiff_fst.prodMk (contMDiff_fst.comp contMDiff_snd)).contMDiffOn)
    (fun z hz => ⟨hz.1,mem_univ _⟩)
  have h₂ : ContMDiff (𝓘(ℝ,ℝ).prod (I.prod 𝓘(ℝ,F × F))) 𝓘(ℝ,ℝ) ∞
      (fun z : ℝ × (M × U) => ζ (z.2.2:F × F).1) :=
    hζ.contMDiff.comp (contDiff_fst.contMDiff.comp
      (contMDiff_subtype_val.comp (contMDiff_snd.comp contMDiff_snd)))
  have h₃ : ContMDiff (𝓘(ℝ,ℝ).prod (I.prod 𝓘(ℝ,F × F))) 𝓘(ℝ,ℝ) ∞
      (fun z : ℝ × (M × U) => ξ (z.2.2:F × F).2) :=
    hξ.contMDiff.comp (contDiff_snd.contMDiff.comp
      (contMDiff_subtype_val.comp (contMDiff_snd.comp contMDiff_snd)))
  exact (h₁.mul h₂.contMDiffOn).mul h₃.contMDiffOn

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace A] [ChartedSpace A M]
  [InnerProductSpace ℝ F] in
lemma uniformCompactSupport_open_radial_on (U : Opens (F × F))
    {H : ℝ → M → ℝ} {ζ ξ : F → ℝ} {K : Set M} (hK : IsCompact K)
    (hH : ∀ t ∈ Icc (0:ℝ) 1, Function.support (H t) ⊆ K)
    (hζ : HasCompactSupport ζ) (hξ : HasCompactSupport ξ)
    (hU : tsupport ζ ×ˢ tsupport ξ ⊆ (U:Set (F × F))) :
    ∃ C : Set (M × U), IsCompact C ∧ ∀ t ∈ Icc (0:ℝ) 1,
      Function.support (cutoffHamiltonian (H t) ζ ξ ∘ radialInclusion U) ⊆ C := by
  let C := radialInclusion (M:=M) U ⁻¹' (K ×ˢ (tsupport ζ ×ˢ tsupport ξ))
  have he : Topology.IsEmbedding (radialInclusion (M:=M) U) :=
    Topology.IsEmbedding.id.prodMap Topology.IsEmbedding.subtypeVal
  have hr : K ×ˢ (tsupport ζ ×ˢ tsupport ξ) ⊆ range (radialInclusion (M:=M) U) := by
    intro z hz
    exact ⟨(z.1,⟨z.2,hU hz.2⟩),rfl⟩
  refine ⟨C,(he.isInducing.isCompact_preimage_iff hr).mpr (hK.prod (hζ.prod hξ)),?_⟩
  intro t ht z hz
  have hne : H t z.1 * ζ (z.2:F × F).1 * ξ (z.2:F × F).2 ≠ 0 := hz
  have h₁ := (mul_ne_zero_iff.mp hne).1
  exact ⟨hH t ht (mul_ne_zero_iff.mp h₁).1,
    subset_tsupport _ (mul_ne_zero_iff.mp h₁).2,subset_tsupport _ (mul_ne_zero_iff.mp hne).2⟩

def cylinderHamiltonian (U : Opens (F × F)) (W : Opens G)
    (e : Diffeomorph (I.prod 𝓘(ℝ,F × F)) 𝓘(ℝ,G) (M × U) W ∞)
    (H : ℝ → M → ℝ) (ζ ξ : F → ℝ) : ℝ × G → ℝ :=
  extendedFlatHamiltonian (V:=G) W (fun t x =>
    (cutoffHamiltonian (H t) ζ ξ ∘ radialInclusion U) (e.symm x))

lemma cylinderHamiltonian_apply (U : Opens (F × F)) (W : Opens G)
    (e : Diffeomorph (I.prod 𝓘(ℝ,F × F)) 𝓘(ℝ,G) (M × U) W ∞)
    (H : ℝ → M → ℝ) (ζ ξ : F → ℝ) (t : ℝ) (z : W) :
    cylinderHamiltonian U W e H ζ ξ (t,(z:G)) =
      (cutoffHamiltonian (fun x => manifoldFlatHamiltonian H (t,x)) ζ ξ ∘ radialInclusion U)
        (e.symm z) := by
  rw [cylinderHamiltonian,extendedFlatHamiltonian_apply (V:=G)]
  dsimp only [manifoldFlatHamiltonian,cutoffHamiltonian,radialInclusion,Function.comp_def]
  ring

lemma contDiff_of_contMDiff_product {f : ℝ × G → ℝ}
    (h : ContMDiff (𝓘(ℝ,ℝ).prod 𝓘(ℝ,G)) 𝓘(ℝ,ℝ) ∞ f) : ContDiff ℝ ∞ f := by
  apply ContMDiff.contDiff
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact h

theorem cylinderHamiltonian_regular (U : Opens (F × F)) (W : Opens G)
    (e : Diffeomorph (I.prod 𝓘(ℝ,F × F)) 𝓘(ℝ,G) (M × U) W ∞)
    {H : ℝ → M → ℝ} {ζ ξ : F → ℝ} {K : Set M}
    (hK : IsCompact K) (hS : ∀ t ∈ Icc (0:ℝ) 1, Function.support (H t) ⊆ K)
    (hH : ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
      (fun z : ℝ × M => H z.1 z.2) (Icc (0:ℝ) 1 ×ˢ univ))
    (hζ : ContDiff ℝ ∞ ζ) (hξ : ContDiff ℝ ∞ ξ)
    (hζc : HasCompactSupport ζ) (hξc : HasCompactSupport ξ)
    (hU : tsupport ζ ×ˢ tsupport ξ ⊆ (U:Set (F × F))) :
    ContDiff ℝ ∞ (cylinderHamiltonian U W e H ζ ξ) ∧
      HasCompactSupport (cylinderHamiltonian U W e H ζ ξ) ∧
      ∃ C : Set G, IsCompact C ∧ C ⊆ (W:Set G) ∧ ∀ t,
        Function.support (fun x => cylinderHamiltonian U W e H ζ ξ (t,x)) ⊆ C := by
  obtain ⟨C,hC,hCs⟩ := uniformCompactSupport_open_radial_on U hK hS hζc hξc hU
  have hCp : IsCompact (e '' C) := hC.image e.continuous
  have hsp : ∀ t ∈ Icc (0:ℝ) 1,
      Function.support (fun x : W =>
        (cutoffHamiltonian (H t) ζ ξ ∘ radialInclusion U) (e.symm x)) ⊆ e '' C := by
    intro t ht x hx
    exact ⟨e.symm x,hCs t ht hx,e.apply_symm_apply x⟩
  have hh : ContMDiffOn (𝓘(ℝ,ℝ).prod 𝓘(ℝ,G)) 𝓘(ℝ,ℝ) ∞
      (fun z : ℝ × W => (cutoffHamiltonian (H z.1) ζ ξ ∘ radialInclusion U) (e.symm z.2))
      (Icc (0:ℝ) 1 ×ˢ univ) :=
    (contMDiffOn_open_cutoffHamiltonian U hH hζ hξ).comp
      ((contMDiff_fst.prodMk (e.symm.contMDiff.comp contMDiff_snd)).contMDiffOn)
      (fun z hz => ⟨hz.1,mem_univ _⟩)
  refine ⟨?_,compactSupport_extendedFlatHamiltonian (V:=G) W hCp hsp,?_⟩
  · have hd := contMDiff_extendedFlatHamiltonian (V:=G) W hCp hsp hh
    exact contDiff_of_contMDiff_product hd
  · refine ⟨Subtype.val '' (e '' C),hCp.image continuous_subtype_val,?_,?_⟩
    · rintro x ⟨y,_,rfl⟩
      exact y.property
    · intro t x hx
      by_cases hxW : x ∈ W
      · let z : W := ⟨x,hxW⟩
        refine ⟨z,?_,rfl⟩
        apply hsp (Real.smoothTransition t) (smoothTime_mem t)
        have hn : manifoldFlatHamiltonian
            (fun t (y : W) => (cutoffHamiltonian (H t) ζ ξ ∘ radialInclusion U) (e.symm y))
            (t,z) ≠ 0 := by
          rw [← extendedFlatHamiltonian_apply (V:=G) W _ t z]
          exact hx
        exact (mul_ne_zero_iff.mp hn).2
      · exact False.elim (hx (extendedFlatHamiltonian_eq_zero (V:=G) W _ t hxW))

end NearbyLagrangian.RadialExtension

end

end OAI
