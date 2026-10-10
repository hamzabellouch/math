import Mathlib
import OAI.Analysis.SymmetricDomains.AffineBand

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
namespace Release061
open Set Filter Topology
open scoped Classical

theorem exists_continuousLinearEquiv_prod_ker
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    (A : E →L[ℝ] X) (hA : Function.Surjective A) :
    ∃ e : E ≃L[ℝ] X × LinearMap.ker A.toLinearMap, ∀ v, (e v).1 = A v := by
  obtain ⟨R,hR⟩ := ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional hA
  let K := LinearMap.ker A.toLinearMap
  let L : E →ₗ[ℝ] X × K :=
    { toFun := fun v => (A v,⟨v-R (A v),by change A (v-R (A v)) = 0; rw [map_sub,hR,sub_self]⟩)
      map_add' := by intro v w; ext <;> simp [map_add]; abel
      map_smul' := by intro c v; ext <;> simp [map_smul,smul_sub] }
  have hinj : Function.Injective L := by
    intro v w he
    have h1 := congrArg Prod.fst he
    have h2 := congrArg (fun p : X × K => (p.2 : E)) he
    change A v = A w at h1
    change v-R (A v) = w-R (A w) at h2
    rw [h1] at h2
    exact sub_left_injective h2
  have hsurj : Function.Surjective L := by
    rintro ⟨x,k⟩
    refine ⟨R x+k,?_⟩
    have hk : A k = 0 := k.property
    have ha : A (R x+k) = x := by rw [map_add,hR,hk,add_zero]
    apply Prod.ext
    · exact ha
    · apply Subtype.ext
      change R x+(k : E)-R (A (R x+k)) = k
      rw [ha]
      abel
  exact ⟨(LinearEquiv.ofBijective L ⟨hinj,hsurj⟩).toContinuousLinearEquiv,fun _ => rfl⟩

theorem exists_continuousLinearEquiv_prod_fin
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    (A : E →L[ℝ] X) (hA : Function.Surjective A) :
    ∃ r : ℕ, ∃ e : E ≃L[ℝ] X × (Fin r → ℝ), ∀ v, (e v).1 = A v := by
  obtain ⟨e,he⟩ := exists_continuousLinearEquiv_prod_ker A hA
  let r := Module.finrank ℝ (LinearMap.ker A.toLinearMap)
  let v : LinearMap.ker A.toLinearMap ≃L[ℝ] (Fin r → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [r])
  refine ⟨r,e.trans ((ContinuousLinearEquiv.refl ℝ X).prodCongr v),?_⟩
  exact he

variable {E X K : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup K] [NormedSpace ℝ K] [FiniteDimensional ℝ K]

noncomputable def criticalBundleLinear (A : X → E →L[ℝ] X) (e : E ≃L[ℝ] X × K) (x : X) :
    E →L[ℝ] X × K := (A x).prod ((ContinuousLinearMap.snd ℝ X K).comp e.toContinuousLinearMap)

noncomputable def criticalBundleParam (A : X → E →L[ℝ] X) (e : E ≃L[ℝ] X × K)
    (b : X → X) (p : X × K) : E := (criticalBundleLinear A e p.1).inverse (b p.1,p.2)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ X] [FiniteDimensional ℝ K] in
lemma criticalBundleLinear_contDiffAt {A : X → E →L[ℝ] X} (e : E ≃L[ℝ] X × K)
    {x : X} (hA : ContDiffAt ℝ 1 A x) : ContDiffAt ℝ 1 (criticalBundleLinear A e) x := by
  have he : criticalBundleLinear A e = fun y =>
      (ContinuousLinearMap.inl ℝ X K).comp (A y) + (ContinuousLinearMap.inr ℝ X K).comp
        ((ContinuousLinearMap.snd ℝ X K).comp e.toContinuousLinearMap) := by
    funext y
    ext v <;> simp [criticalBundleLinear]
  rw [he]
  exact (contDiffAt_const.clm_comp hA).add contDiffAt_const

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ K] in
lemma criticalBundleParam_contDiffAt {A : X → E →L[ℝ] X} (e : E ≃L[ℝ] X × K)
    {b : X → X} {p : X × K} (hA : ContDiffAt ℝ 1 A p.1) (hb : ContDiffAt ℝ 1 b p.1)
    (hi : (criticalBundleLinear A e p.1).IsInvertible) :
    ContDiffAt ℝ 1 (criticalBundleParam A e b) p := by
  have h := hi.contDiffAt_map_inverse.comp p.1 (criticalBundleLinear_contDiffAt e hA)
  exact (h.comp p contDiffAt_fst).clm_apply ((hb.comp p contDiffAt_fst).prodMk contDiffAt_snd)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ X] [FiniteDimensional ℝ K] in
lemma criticalBundleParam_fibre {A : X → E →L[ℝ] X} (e : E ≃L[ℝ] X × K)
    {b : X → X} {x : X} (hi : (criticalBundleLinear A e x).IsInvertible) :
    range (fun k : K => criticalBundleParam A e b (x,k)) = {a | A x a = b x} := by
  ext a
  constructor
  · rintro ⟨k,rfl⟩
    exact congrArg Prod.fst (hi.self_apply_inverse (b x,k))
  · intro ha
    refine ⟨(e a).2,?_⟩
    have he : (b x,(e a).2) = criticalBundleLinear A e x a := by
      apply Prod.ext
      · exact ha.symm
      · rfl
    change (criticalBundleLinear A e x).inverse (b x,(e a).2) = a
    rw [he]
    exact hi.inverse_apply_self a

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ K] in

theorem critical_affine_bundle_neighborhood
    (A : X → E →L[ℝ] X) (B : Set X) (hB : IsOpen B)
    (hA : ∀ x ∈ B, ContDiffAt ℝ 1 A x) (b : X → X)
    (hb : ∀ x ∈ B, ContDiffAt ℝ 1 b x) {x₀ : X} (hx₀ : x₀ ∈ B)
    (e : E ≃L[ℝ] X × K) (he : ∀ v, (e v).1 = A x₀ v) :
    ∃ W : Set X, IsOpen W ∧ x₀ ∈ W ∧ W ⊆ B ∧
      (∀ x ∈ W, (criticalBundleLinear A e x).IsInvertible) ∧
      ContDiffOn ℝ 1 (criticalBundleParam A e b) (W ×ˢ univ) ∧
      ∀ x ∈ W, range (fun k : K => criticalBundleParam A e b (x,k)) = {a | A x a = b x} := by
  let C : X → E →L[ℝ] E := fun x => e.symm.toContinuousLinearMap.comp (criticalBundleLinear A e x)
  have hC (x : X) (hx : x ∈ B) : ContinuousAt C x :=
    (contDiffAt_const.clm_comp (criticalBundleLinear_contDiffAt e (hA x hx))).continuousAt
  have hC₀ : C x₀ = ContinuousLinearMap.id ℝ E := by
    ext v
    change e.symm (A x₀ v,(e v).2) = v
    rw [← he]
    exact e.symm_apply_apply v
  let W : Set X := {x | x ∈ B ∧ (C x).det ≠ 0}
  have hWo : IsOpen W := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    exact inter_mem (hB.mem_nhds hx.1)
      (((ContinuousLinearMap.continuous_det.continuousAt.comp (hC x hx.1)).eventually_ne hx.2))
  have hWi (x : X) (hx : x ∈ W) : (criticalBundleLinear A e x).IsInvertible := by
    let v := (C x).toContinuousLinearEquivOfDetNeZero hx.2
    refine ⟨v.trans e,?_⟩
    apply ContinuousLinearMap.ext
    intro a
    change e (C x a) = criticalBundleLinear A e x a
    exact e.apply_symm_apply _
  refine ⟨W,hWo,?_,fun _ hx => hx.1,hWi,?_,fun x hx => criticalBundleParam_fibre e (hWi x hx)⟩
  · exact ⟨hx₀,by rw [hC₀]; change LinearMap.det (LinearMap.id : E →ₗ[ℝ] E) ≠ 0; rw [LinearMap.det_id]; exact one_ne_zero⟩
  · intro p hp
    exact (criticalBundleParam_contDiffAt e (hA p.1 hp.1.1) (hb p.1 hp.1.1) (hWi p.1 hp.1)).contDiffWithinAt

end Release061

end

end OAI
