import Mathlib
import OAI.Geometry.BallPacking.Flows.FlowSmoothExtension

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

 theorem movingPrimitivePullback_exterior_comp
    {α : F → F →L[ℝ] ℝ} {g : ℝ × M → F} {A : G → F} {h : M → G}
    (hα : ContDiff ℝ ∞ α)
    (hg : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,F) ∞ g)
    (hA : ContDiff ℝ ∞ A) (hh : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,G) ∞ h)
    {t : ℝ} {x : M} (he : (fun y => g (t,y)) =ᶠ[𝓝 x] A ∘ h) :
    manifoldExteriorOneForm (movingPrimitivePullback (E := E) α g t) x=
      (euclideanExteriorOneForm (primitivePullback α A) (h x)).bilinearComp
        (manifoldMapDifferential (E := G) (F := E) h x)
        (manifoldMapDifferential (E := G) (F := E) h x) := by
  rw [movingPrimitivePullback_exterior hα hg,primitivePullback_exterior hα hA]
  have hd : manifoldMapDifferential (E := F) (F := E) (fun y => g (t,y)) x=
      (fderiv ℝ A (h x)).comp (manifoldMapDifferential (E := G) (F := E) h x) := by
    unfold manifoldMapDifferential
    rw [he.mfderiv_eq]
    rw [mfderiv_comp x (hA.contMDiff.mdifferentiable (by simp) (h x))
      (hh.mdifferentiable (by simp) x)]
    rw [mfderiv_eq_fderiv]
    rfl
  rw [hd,he.eq_of_nhds]
  ext u v
  rfl

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.NormalLift
open scoped ContDiff InnerProduct Topology
open Set Function
section

variable {E F P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [NormedAddCommGroup P] [NormedSpace ℝ P]

def adjointCLM : (E →L[ℝ] F) →L[ℝ] (F →L[ℝ] E) where
  toFun := ContinuousLinearMap.adjoint
  map_add' := map_add ContinuousLinearMap.adjoint
  map_smul' := by intro c A; simp
  cont := ContinuousLinearMap.adjoint.continuous

def gram (A : E →L[ℝ] F) : F →L[ℝ] F := A.comp (adjointCLM A)

def rightLift (A : E →L[ℝ] F) : F →L[ℝ] E :=
  (adjointCLM A).comp (gram A).inverse

theorem gram_invertible {A : E →L[ℝ] F} (hA : Surjective A) :
    (gram A).IsInvertible := by
  have ha : Injective (adjointCLM A) := by
    apply LinearMap.ker_eq_bot.mp
    change (ContinuousLinearMap.adjoint A).ker=⊥
    rw [← A.orthogonal_range]
    have hr : A.range=⊤ := LinearMap.range_eq_top.mpr hA
    rw [hr,Submodule.top_orthogonal_eq_bot]
  have hg : Injective (gram A) := A.self_comp_adjoint_injective_iff.mpr ha
  have hb : Bijective (gram A) := ⟨hg,LinearMap.surjective_of_injective hg⟩
  exact ⟨(LinearEquiv.ofBijective (gram A).toLinearMap hb).toContinuousLinearEquiv,rfl⟩

theorem rightLift_right_inverse {A : E →L[ℝ] F} (hA : Surjective A) (v : F) :
    A (rightLift A v)=v := (gram_invertible hA).self_apply_inverse v

theorem gram_contDiff : ContDiff ℝ ∞ (gram : (E →L[ℝ] F) → (F →L[ℝ] F)) :=
  contDiff_id.clm_comp (adjointCLM : (E →L[ℝ] F) →L[ℝ] (F →L[ℝ] E)).contDiff

theorem rightLift_contDiffAt {A : E →L[ℝ] F} (hA : Surjective A) :
    ContDiffAt ℝ ∞ rightLift A := by
  exact (adjointCLM : (E →L[ℝ] F) →L[ℝ] (F →L[ℝ] E)).contDiff.contDiffAt.clm_comp
    ((gram_invertible hA).contDiffAt_map_inverse.comp A gram_contDiff.contDiffAt)

theorem rightLift_family_contDiffAt {A : P → E →L[ℝ] F} {p : P}
    (hA : ContDiffAt ℝ ∞ A p) (hs : Surjective (A p)) :
    ContDiffAt ℝ ∞ (fun q => rightLift (A q)) p :=
  (rightLift_contDiffAt hs).comp p hA

end

variable (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

abbrev HilbertModel (E : Type*) [AddCommGroup E] [Module ℝ E] :=
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

def hilbertEquiv : E ≃L[ℝ] HilbertModel E :=
  (Module.finBasis ℝ E).equivFun.toContinuousLinearEquiv.trans
    (EuclideanSpace.equiv _ ℝ).symm

def hilbertArrow : (E →L[ℝ] F) ≃L[ℝ] (HilbertModel E →L[ℝ] HilbertModel F) :=
  (hilbertEquiv E).arrowCongr (hilbertEquiv F)

def finiteRightLift (A : E →L[ℝ] F) : F →L[ℝ] E :=
  (((hilbertEquiv F).symm).arrowCongr (hilbertEquiv E).symm)
    (rightLift (hilbertArrow E F A))

variable {E F}

theorem hilbertArrow_surjective {A : E →L[ℝ] F} (hA : Surjective A) :
    Surjective (hilbertArrow E F A) := by
  intro y
  obtain ⟨x,hx⟩ := hA ((hilbertEquiv F).symm y)
  refine ⟨hilbertEquiv E x,?_⟩
  change hilbertEquiv F (A ((hilbertEquiv E).symm (hilbertEquiv E x)))=y
  rw [ContinuousLinearEquiv.symm_apply_apply,hx,ContinuousLinearEquiv.apply_symm_apply]

theorem finiteRightLift_right_inverse {A : E →L[ℝ] F} (hA : Surjective A) (v : F) :
    A (finiteRightLift E F A v)=v := by
  apply (hilbertEquiv F).injective
  exact (rightLift_right_inverse (hilbertArrow_surjective hA) ((hilbertEquiv F) v))

theorem finiteRightLift_contDiffAt {A : E →L[ℝ] F} (hA : Surjective A) :
    ContDiffAt ℝ ∞ (finiteRightLift E F) A := by
  exact (((hilbertEquiv F).symm).arrowCongr (hilbertEquiv E).symm).contDiff.contDiffAt.comp A
    ((rightLift_contDiffAt (hilbertArrow_surjective hA)).comp A
      (hilbertArrow E F).contDiff.contDiffAt)

end PackingSufficiencySupport.NormalLift
end

section

open scoped Topology
open Set
namespace PackingSufficiencySupport.Hamiltonian
variable {M : Type*} [TopologicalSpace M]

theorem exists_uniform_short_transport
    {Φ : ℝ × M → M} (hΦ : Continuous Φ) (h0 : ∀ x, Φ (0,x) = x)
    {K O : Set M} (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ W : Set M, IsOpen W ∧ K ⊆ W ∧ W ⊆ O ∧
      ∀ t ∈ Icc (-ε) ε, ∀ x ∈ W, Φ (t,x) ∈ O := by
  have hsub : ({0} : Set ℝ) ×ˢ K ⊆ Φ ⁻¹' O := by
    rintro ⟨t,x⟩ ⟨ht,hx⟩
    rcases ht with rfl
    simpa only [mem_preimage,h0] using hKO hx
  obtain ⟨U,W,hU,hW,h0U,hKW,hUW⟩ :=
    generalized_tube_lemma isCompact_singleton hK (hO.preimage hΦ) hsub
  obtain ⟨δ,hδ,hδU⟩ := Metric.isOpen_iff.mp hU 0 (h0U (mem_singleton 0))
  refine ⟨δ/2,by positivity,W ∩ O,hW.inter hO,fun x hx => ⟨hKW hx,hKO hx⟩,
    inter_subset_right,?_⟩
  intro t ht x hx
  apply hUW
  refine ⟨hδU ?_,hx.1⟩
  rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_lt]
  constructor <;> linarith [ht.1,ht.2]

end PackingSufficiencySupport.Hamiltonian

end

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem exists_compact_localized_manifold_flow
    {v : (x : M) → TangentSpace 𝓘(ℝ,E) x}
    (hv : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E)).tangent ∞
      (fun x => (⟨x,v x⟩ : TangentBundle 𝓘(ℝ,E) M)))
    {K O : Set M} (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ Φ : ℝ × M → M, ∃ ε : ℝ, 0 < ε ∧ ∃ W : Set M,
      IsOpen W ∧ K ⊆ W ∧ W ⊆ O ∧
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Φ ∧
      (∀ x, Φ (0,x) = x) ∧
      (∀ s t x, Φ (s+t,x) = Φ (s,Φ (t,x))) ∧
      (∀ t ∈ Icc (-ε) ε, ∀ x ∈ W, Φ (t,x) ∈ O) ∧
      (∀ x ∈ W, ∀ t ∈ Icc (-ε) ε, HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E)
        (fun r => Φ (r,x)) t ((1 : ℝ →L[ℝ] ℝ).smulRight (v (Φ (t,x))))) := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  obtain ⟨C,hC,hKC,hCO⟩ := exists_compact_between hK hO hKO
  obtain ⟨χ,hχ1,hχ0,_⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (n := (⊤ : ℕ∞)) 𝓘(ℝ,E) hK.isClosed hKC
  obtain ⟨U,hU,hKU,hUχ⟩ := mem_nhdsSet_iff_exists.mp hχ1
  let v' : (x : M) → TangentSpace 𝓘(ℝ,E) x := fun x => χ x • v x
  have hv' : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E)).tangent ∞
      (fun x => (⟨x,v' x⟩ : TangentBundle 𝓘(ℝ,E) M)) :=
    χ.contMDiff.smul_section hv
  obtain ⟨Φ,hΦ,hΦ0,hΦa,hΦd,_⟩ := exists_smooth_global_manifold_flow hv' hC
    (fun x hx => by simp only [v',hχ0 x hx,zero_smul])
  obtain ⟨ε,hε,W,hW,hKW,hWO,hstay⟩ := exists_uniform_short_transport hΦ.continuous hΦ0
    hK (hU.inter hO) (fun x hx => ⟨hKU hx,hKO hx⟩)
  refine ⟨Φ,ε,hε,W,hW,hKW,fun x hx => (hWO hx).2,hΦ,hΦ0,hΦa,
    fun t ht x hx => (hstay t ht x hx).2,?_⟩
  intro x hx t ht
  have hd := hΦd x t
  have he : v' (Φ (t,x)) = v (Φ (t,x)) := by
    have hχx : χ (Φ (t,x)) = 1 := hUχ (hstay t ht x hx).1
    simp only [v',hχx,one_smul]
  simpa only [he] using hd

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.NormalLift
open scoped ContDiff Manifold Topology
open Set Function Manifold
open Hamiltonian

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
theorem curve_eq_add_of_hasDerivAt {γ : ℝ → F} {b : F} {ε : ℝ} (hε : 0<ε)
    (hd : ∀ t∈Icc (-ε) ε, HasDerivAt γ b t) {t : ℝ} (ht : t∈Icc (-ε) ε) :
    γ t=γ 0+t•b := by
  have hd0 (s : ℝ) (hs : s∈Icc (-ε) ε) :
      HasDerivAt (fun r => γ r-r•b) 0 s := by
    convert! (hd s hs).sub ((hasDerivAt_id s).smul_const b) using 1; simp
  have he := (convex_Icc (-ε) ε).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (hd0 s hs).hasDerivWithinAt)
    (fun _ _ => (by simp : ‖(0:F)‖≤(0:ℝ)))
    (show (0:ℝ)∈Icc (-ε) ε by constructor <;> linarith) ht
  have he' : γ t-t•b=γ 0 := by
    simpa only [zero_smul,sub_zero,zero_mul,norm_le_zero_iff,sub_eq_zero] using he
  exact sub_eq_iff_eq_add.mp he'

theorem exists_compact_normal_flow {f : E → F} (hf : ContDiff ℝ ∞ f)
    {B : E → F →L[ℝ] E} (hB : ContDiff ℝ ∞ B)
    {O : Set E} (hO : IsOpen O) (hproj : ∀ z∈O,∀ w,fderiv ℝ f z (B z w)=w)
    {K : Set E} {H : Set F} (hK : IsCompact K) (hH : IsCompact H) (hKO : K⊆O) :
    ∃ Φ : ℝ × (E × F) → E × F, ∃ ε : ℝ, 0<ε ∧ ∃ W : Set (E × F),
      IsOpen W ∧ K×ˢH⊆W ∧ W⊆O×ˢuniv ∧ ContDiff ℝ ∞ Φ ∧
      (∀ p,Φ (0,p)=p) ∧ (∀ s t p,Φ (s+t,p)=Φ (s,Φ (t,p))) ∧
      (∀ p∈W,∀ t∈Icc (-ε) ε,(Φ (t,p)).2=p.2) ∧
      (∀ p∈W,∀ t∈Icc (-ε) ε,f (Φ (t,p)).1=f p.1+t•p.2) ∧
      (∀ p∈W,∀ t∈Icc (-ε) ε,(Φ (t,p)).1∈O) ∧
      ∀ p∈W,∀ t∈Icc (-ε) ε,
        HasDerivAt (fun s => (Φ (s,p)).1) (B (Φ (t,p)).1 p.2) t := by
  let V : E × F → E × F := fun p => (B p.1 p.2,0)
  have hV : ContDiff ℝ ∞ V :=
    ((hB.comp contDiff_fst).clm_apply contDiff_snd).prodMk contDiff_const
  have hVm : ContMDiff 𝓘(ℝ,E×F) (𝓘(ℝ,E×F)).tangent ∞
      (fun p => (⟨p,V p⟩ : TangentBundle 𝓘(ℝ,E×F) (E×F))) :=
    contMDiff_vectorSpace_iff_contDiff.mpr hV
  obtain ⟨Φ,ε,hε,W,hW,hKW,hWO,hΦ,hΦ0,hΦa,hstay,hODE⟩ :=
    exists_compact_localized_manifold_flow hVm (hK.prod hH) (hO.prod isOpen_univ)
      (fun p hp => ⟨hKO hp.1,mem_univ _⟩)
  have hΦs : ContDiff ℝ ∞ Φ := by
    rw [← modelWithCornersSelf_prod,chartedSpaceSelf_prod] at hΦ
    exact contMDiff_iff_contDiff.mp hΦ
  have hd (p : E×F) (hp : p∈W) (t : ℝ) (ht : t∈Icc (-ε) ε) :
      HasDerivAt (fun s => Φ (s,p)) (V (Φ (t,p))) t := by
    rw [hasDerivAt_iff_hasFDerivAt]
    exact hasMFDerivAt_iff_hasFDerivAt.mp (hODE p hp t ht)
  have hparam (p : E×F) (hp : p∈W) (t : ℝ) (ht : t∈Icc (-ε) ε) :
      (Φ (t,p)).2=p.2 := by
    have hd2 (s : ℝ) (hs : s∈Icc (-ε) ε) :
        HasDerivAt (fun r => (Φ (r,p)).2) 0 s :=
      (ContinuousLinearMap.snd ℝ E F).hasFDerivAt.comp_hasDerivAt s (hd p hp s hs)
    simpa only [hΦ0,smul_zero,add_zero] using curve_eq_add_of_hasDerivAt hε hd2 ht
  have hd1 (p : E×F) (hp : p∈W) (t : ℝ) (ht : t∈Icc (-ε) ε) :
      HasDerivAt (fun s => (Φ (s,p)).1) (B (Φ (t,p)).1 p.2) t := by
    have hd' := (ContinuousLinearMap.fst ℝ E F).hasFDerivAt.comp_hasDerivAt t (hd p hp t ht)
    simpa only [V,ContinuousLinearMap.coe_fst',Function.comp_def,hparam p hp t ht] using hd'
  refine ⟨Φ,ε,hε,W,hW,hKW,hWO,hΦs,hΦ0,hΦa,hparam,?_,
    fun p hp t ht => (hstay t ht p hp).1,hd1⟩
  intro p hp t ht
  have hdf (s : ℝ) (hs : s∈Icc (-ε) ε) :
      HasDerivAt (fun r => f (Φ (r,p)).1) p.2 s := by
    have hc := (hf.differentiable (by simp) (Φ (s,p)).1).hasFDerivAt.comp_hasDerivAt s
      (hd1 p hp s hs)
    simpa only [hproj _ (hstay s hs p hp).1,Function.comp_def] using hc
  simpa only [hΦ0] using curve_eq_add_of_hasDerivAt hε hdf ht

abbrev zeroFibre (f : E → F) := {z : E // f z=0}
abbrev tubeDomain (f : E → F) (W : Set (E×F)) :=
  {p : zeroFibre f × F // ((p.1 : E),p.2)∈W}
def tubeSlice (Φ : ℝ × (E×F) → E×F) (t : ℝ) (f : E → F) (W : Set (E×F))
    (p : tubeDomain f W) : E := (Φ (t,((p.val.1 : E),p.val.2))).1

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in

theorem tubeSlice_isEmbedding {f : E → F} (hf : Continuous f)
    {Φ : ℝ × (E×F) → E×F} (hΦ : Continuous Φ)
    (hΦ0 : ∀ p,Φ (0,p)=p) (hΦa : ∀ s t p,Φ (s+t,p)=Φ (s,Φ (t,p)))
    {W : Set (E×F)} {t : ℝ} (ht : t≠0)
    (hp : ∀ p∈W,(Φ (t,p)).2=p.2)
    (he : ∀ p∈W,f (Φ (t,p)).1=f p.1+t•p.2) :
    Topology.IsEmbedding (tubeSlice Φ t f W) := by
  let ι : tubeDomain f W → E×F := fun p => ((p.val.1 : E),p.val.2)
  have hι : Topology.IsEmbedding ι :=
    (Topology.IsEmbedding.subtypeVal.prodMap Topology.IsEmbedding.id).comp
      Topology.IsEmbedding.subtypeVal
  have hs : Continuous (tubeSlice Φ t f W) :=
    (hΦ.comp (continuous_const.prodMk hι.continuous)).fst
  let R : E → E×F := fun z => ((Φ (-t,(z,t⁻¹•f z))).1,t⁻¹•f z)
  have hR : Continuous R :=
    (hΦ.comp (continuous_const.prodMk (continuous_id.prodMk
      (continuous_const.smul hf)))).fst.prodMk (continuous_const.smul hf)
  have hRi : R ∘ tubeSlice Φ t f W=ι := by
    funext p
    have hn : t⁻¹ • f (Φ (t,ι p)).1=p.val.2 := by
      rw [he _ p.property,p.val.1.property,zero_add,smul_smul,inv_mul_cancel₀ ht,one_smul]
    have hg : Φ (-t,Φ (t,ι p))=ι p := by rw [← hΦa,neg_add_cancel,hΦ0]
    have hparam := hp (ι p) p.property
    have hinput : ((Φ (t,ι p)).1,t⁻¹•f (Φ (t,ι p)).1)=Φ (t,ι p) := by
      rw [hn,← hparam]
    change ((Φ (-t,((Φ (t,ι p)).1,t⁻¹•f (Φ (t,ι p)).1))).1,
      t⁻¹•f (Φ (t,ι p)).1)=ι p
    rw [hinput,hg,hn]
  exact Topology.IsEmbedding.of_comp hs hR (hRi ▸ hι)

end PackingSufficiencySupport.NormalLift

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology
open Set Function Manifold
open NormalLift Hamiltonian DiagonalQuadrics DiagonalQuadrics.Explicit

def regularLocus : Set PlaneBase := {z | gradV z≠0 ∨ gradW z≠0}

theorem regularLocus_isOpen : IsOpen regularLocus := by
  have hv : Continuous gradV := by unfold gradV; fun_prop
  have hw : Continuous gradW := by unfold gradW; fun_prop
  exact (isOpen_ne_fun hv continuous_const).union (isOpen_ne_fun hw continuous_const)

theorem regular_jacobian_surjective {z : PlaneBase} (hz : z∈regularLocus) :
    Surjective (jacobian z) := by
  rcases hz with hv | hw
  · intro w
    refine ⟨(w/gradV z,0),?_⟩
    simp [jacobian,mul_div_cancel₀ _ hv]
  · intro w
    refine ⟨(0,w/gradW z),?_⟩
    simp [jacobian,mul_div_cancel₀ _ hw]

def realJacobian (z : PlaneBase) : PlaneBase →L[ℝ] ℂ :=
  (jacobian z).restrictScalars ℝ

theorem realJacobian_contDiff : ContDiff ℝ ∞ realJacobian := by
  have he : realJacobian=fderiv ℝ polynomial :=
    funext fun z => ((polynomial_hasFDerivAt z).restrictScalars ℝ).fderiv.symm
  rw [he]
  exact (polynomial_contDiff.restrict_scalars ℝ).fderiv_right (by simp)

def normalLift (z : PlaneBase) : ℂ →L[ℝ] PlaneBase :=
  finiteRightLift _ _ (realJacobian z)

theorem normalLift_projects {z : PlaneBase} (hz : z∈regularLocus) (w : ℂ) :
    realJacobian z (normalLift z w)=w :=
  finiteRightLift_right_inverse (regular_jacobian_surjective hz) w

theorem normalLift_contDiffOn : ContDiffOn ℝ ∞ normalLift regularLocus := by
  intro z hz
  exact ((finiteRightLift_contDiffAt (regular_jacobian_surjective hz)).comp z
    realJacobian_contDiff.contDiffAt).contDiffWithinAt

theorem exists_compact_normal_lift {K : Set PlaneBase} (hK : IsCompact K)
    (hK0 : ∀ z∈K,polynomial z=0) :
    ∃ B : PlaneBase → ℂ →L[ℝ] PlaneBase,
      ContDiff ℝ ∞ B ∧ HasCompactSupport B ∧ ∃ O : Set PlaneBase,
      IsOpen O ∧ K⊆O ∧ O⊆regularLocus ∧
      ∀ z∈O,∀ w,realJacobian z (B z w)=w := by
  have hKr : K⊆regularLocus := fun z hz => gradient_nonzero (hK0 z hz)
  obtain ⟨χ,_hχ,_hχc,_hχU,_hr,_hχ1,hB,hBc,hBe⟩ := exists_smooth_compact_extension
    hK regularLocus_isOpen hKr normalLift_contDiffOn
  obtain ⟨O,hO,hKO,hOB⟩ := mem_nhdsSet_iff_exists.mp hBe
  refine ⟨fun z => χ z • normalLift z,hB,hBc,O∩regularLocus,
    hO.inter regularLocus_isOpen,fun z hz => ⟨hKO hz,hKr hz⟩,inter_subset_right,?_⟩
  intro z hz w
  change realJacobian z ((χ z • normalLift z) w)=w
  rw [hOB hz.1]
  exact normalLift_projects hz.2 w

theorem inclusion_real_contMDiff : ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,PlaneBase) ∞ inclusion :=
  (projection_contDiff.restrict_scalars ℝ).contMDiff.comp
    (real_inclusion_contMDiff (parameters 0))

theorem exists_actual_cubic_normal_tube {K : Set BaseCurve} {H : Set ℂ}
    (hK : IsCompact K) (hH : IsCompact H) :
    ∃ Ψ : ℝ × (BaseCurve × ℂ) → PlaneBase, ∃ ε : ℝ, 0<ε ∧
      ∃ U : Set (BaseCurve × ℂ),IsOpen U ∧ K×ˢH⊆U ∧
      ContMDiff ((𝓘(ℝ,ℝ)).prod ((𝓘(ℝ,RealModel)).prod 𝓘(ℝ,ℂ)))
        𝓘(ℝ,PlaneBase) ∞ Ψ ∧
      (∀ p,Ψ (0,p)=inclusion p.1) ∧
      (∀ p∈U,∀ t∈Icc (-ε) ε,polynomial (Ψ (t,p))=t•p.2) ∧
      ∀ t∈Icc (-ε) ε,t≠0 → Topology.IsEmbedding (fun p : U => Ψ (t,p.val)) := by
  obtain ⟨B,hB,_hBc,O,hO,hKO,_hOr,hproj⟩ := exists_compact_normal_lift
    (hK.image inclusion_isEmbedding.continuous)
    (by rintro _ ⟨z,_hz,rfl⟩; exact inclusion_polynomial z)
  have hdf z : fderiv ℝ polynomial z=realJacobian z :=
    ((polynomial_hasFDerivAt z).restrictScalars ℝ).fderiv
  obtain ⟨Φ,ε,hε,W,hW,hKW,_hWO,hΦ,hΦ0,hΦa,hparam,he,_hst,_hd⟩ :=
    exists_compact_normal_flow (polynomial_contDiff.restrict_scalars ℝ)
      hB hO (by simpa only [hdf] using hproj)
      (hK.image inclusion_isEmbedding.continuous) hH hKO
  let ι : BaseCurve × ℂ → PlaneBase × ℂ := fun p => (inclusion p.1,p.2)
  have hι : ContMDiff ((𝓘(ℝ,RealModel)).prod 𝓘(ℝ,ℂ))
      𝓘(ℝ,PlaneBase × ℂ) ∞ ι := by
    exact (inclusion_real_contMDiff.comp contMDiff_fst).prodMk_space contMDiff_snd
  let Ψ : ℝ × (BaseCurve × ℂ) → PlaneBase := fun p => (Φ (p.1,ι p.2)).1
  have hΨ : ContMDiff ((𝓘(ℝ,ℝ)).prod ((𝓘(ℝ,RealModel)).prod 𝓘(ℝ,ℂ)))
      𝓘(ℝ,PlaneBase) ∞ Ψ := by
    exact contDiff_fst.contMDiff.comp (hΦ.contMDiff.comp
      (contMDiff_fst.prodMk_space (hι.comp contMDiff_snd)))
  refine ⟨Ψ,ε,hε,ι ⁻¹' W,hW.preimage hι.continuous,?_,hΨ,?_,?_,?_⟩
  · intro p hp
    exact hKW ⟨⟨p.1,hp.1,rfl⟩,hp.2⟩
  · intro p
    exact congrArg Prod.fst (hΦ0 (ι p))
  · intro p hp t ht
    change polynomial (Φ (t,ι p)).1=t•p.2
    rw [he _ hp _ ht,inclusion_polynomial,zero_add]
  · intro t ht ht0
    let S := ι ⁻¹' W
    let I : S → PlaneBase × ℂ := fun p => ι p.val
    have hI : Topology.IsEmbedding I :=
      (inclusion_isEmbedding.prodMap Topology.IsEmbedding.id).comp
        Topology.IsEmbedding.subtypeVal
    have hs : Continuous (fun p : S => Ψ (t,p.val)) :=
      (hΦ.continuous.comp (continuous_const.prodMk hI.continuous)).fst
    let R : PlaneBase → PlaneBase × ℂ := fun z => ((Φ (-t,(z,t⁻¹•polynomial z))).1,t⁻¹•polynomial z)
    have hc : Continuous (fun z => t⁻¹•polynomial z) :=
      (continuous_const : Continuous (fun _ : PlaneBase => (t⁻¹ : ℝ))).smul
        polynomial_contDiff.continuous
    have hR : Continuous R :=
      (hΦ.continuous.comp (continuous_const.prodMk (continuous_id.prodMk hc))).fst.prodMk hc
    have hRi : R ∘ (fun p : S => Ψ (t,p.val))=I := by
      funext p
      have hn : t⁻¹•polynomial (Φ (t,I p)).1=p.val.2 := by
        rw [he _ p.property _ ht,inclusion_polynomial,zero_add,smul_smul,
          inv_mul_cancel₀ ht0,one_smul]
      have hg : Φ (-t,Φ (t,I p))=I p := by rw [← hΦa,neg_add_cancel,hΦ0]
      have hpar := hparam (I p) p.property t ht
      have hin : ((Φ (t,I p)).1,t⁻¹•polynomial (Φ (t,I p)).1)=Φ (t,I p) := by
        rw [hn,← hpar]
      change ((Φ (-t,((Φ (t,I p)).1,t⁻¹•polynomial (Φ (t,I p)).1))).1,
        t⁻¹•polynomial (Φ (t,I p)).1)=I p
      rw [hin,hg,hn]
    exact Topology.IsEmbedding.of_comp hs hR (hRi ▸ hI)

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem primitivePullback_smoothAt {α : F → F →L[ℝ] ℝ} {g : E → F} {x : E}
    (hα : ContDiffAt ℝ ∞ α (g x)) (hg : ContDiffAt ℝ ∞ g x) :
    ContDiffAt ℝ ∞ (primitivePullback α g) x :=
  (hα.comp x hg).clm_comp (hg.fderiv_right (by simp))

theorem primitivePullback_exteriorAt {α : F → F →L[ℝ] ℝ} {g : E → F} {x : E}
    (hα : ContDiffAt ℝ ∞ α (g x)) (hg : ContDiffAt ℝ ∞ g x) :
    euclideanExteriorOneForm (primitivePullback α g) x=
      (euclideanExteriorOneForm α (g x)).bilinearComp (fderiv ℝ g x) (fderiv ℝ g x) := by
  have hh := manifold_pullback_exterior_at (α := α) (g := g)
    (by rw [show chartOneForm α (g x)=α from funext (vector_chartOneForm α (g x))]
        simpa only [extChartAt_model_space_eq_id,PartialEquiv.refl_coe,id_eq] using hα) hg.contMDiffAt
  have he : manifoldPullbackOneForm (fun _ => α) g 0=primitivePullback α g := by
    funext z
    simp [manifoldPullbackOneForm,manifoldMapDifferential,mfderiv_eq_fderiv,primitivePullback]
  rw [he] at hh
  simpa only [vector_exteriorOneForm,manifoldPullbackOneForm,manifoldPullbackTwoForm,
    manifoldMapDifferential,mfderiv_eq_fderiv,primitivePullback] using hh

end PackingSufficiencySupport.Hamiltonian
end

end OAI
