import Mathlib
import OAI.Geometry.BallPacking.BallMaps.QuadricRelativeShellFlow

namespace OAI

noncomputable section

namespace PackingSufficiencySupport
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
open Hamiltonian DiagonalQuadrics DiagonalQuadrics.Explicit

 theorem actual_complement_packing (m : ℕ) {N : ℕ} [Nonempty (Fin N)]
    (r r' : Fin N → ℝ) (hr : ∀ i,0<r i) (hr' : ∀ i,0≤r' i)
    (hrr : ∀ i,r' i<r i) {a₀ : ℝ} (ha₀ : 0<a₀) (ha₁ : a₀<1)
    (hrs : ∀ i,r i<1-a₀) (hhalf : ∀ i,r i<1/2)
    (hvol : ∑ i,r i^(m+4)<1-a₀^(m+4)) :
    ∃ b : ℝ,b<1-a₀ ∧ ∃ f : Fin N → Ambient (m+4) → Ambient (m+4),
      (∀ i,IsBallEmbedding (r' i) (f i)) ∧
      (∀ i,f i '' closedBall (m+4) (r' i)⊆openBall (m+4) 1) ∧
      (∀ i,∀ x∈closedBall (m+4) (r' i),Real.pi*Complex.normSq (f i x 0)<b) ∧
      Pairwise (fun i j => Disjoint (f i '' closedBall (m+4) (r' i))
        (f j '' closedBall (m+4) (r' j))) := by
  obtain ⟨b,d,t,hb,hd,hdhalf,_ht,φ,hφ,hφb,hdisj⟩ :=
    actual_large_polynomial_packing m r r' hr hr' hrr ha₀ ha₁ hrs hhalf hvol
  obtain ⟨g,hg,hgemb,hgmem,hgfirst,hgform⟩ :=
    exists_polynomial_first_line_target (parameters m) t hd.le hdhalf
  have hφdom (i : Fin N) : MapsTo (φ i) (closedBall (m+4) (r' i)) firstDiskDomain := by
    intro x hx
    exact (hφb i x hx).trans (by linarith : b<1)
  have hform (x : Affine (m+2) × Plane) (hx : x∈firstDiskDomain) (v w) :
      successorStandardForm (m+3)
        (mfderiv 𝓘(ℝ,Affine (m+2) × Plane) 𝓘(ℝ,Ambient (m+4)) g x v)
        (mfderiv 𝓘(ℝ,Affine (m+2) × Plane) 𝓘(ℝ,Ambient (m+4)) g x w)=
      euclideanExteriorOneForm (firstLinePrimitive
        (normalAmbientPrimitive (parameters m) (1/Real.pi) d t)) x v w := by
    rw [mfderiv_eq_fderiv]
    exact (successorStandardForm_apply _ _ _).trans (hgform x hx v w)
  obtain ⟨hf,hdj⟩ := postcompose_form_packing (fun i => closedBall (m+4) (r' i))
    (fun _ => successorStandardForm (m+3))
    (euclideanExteriorOneForm (firstLinePrimitive
      (normalAmbientPrimitive (parameters m) (1/Real.pi) d t)))
    (fun _ => successorStandardForm (m+3)) firstDiskDomain_open g
    hg.contMDiffOn hgemb hform φ hφ hφdom hdisj
  refine ⟨b,hb,fun i => g ∘ φ i,
    fun i => isBallEmbedding_iff_formNeighborhoodEmbedding.mpr (hf i),?_,?_,hdj⟩
  · intro i y hy
    obtain ⟨x,hx,rfl⟩ := hy
    exact hgmem _ (hφdom i hx)
  · intro i x hx
    change Real.pi*Complex.normSq (g (φ i x) 0)<b
    rw [hgfirst]
    exact hφb i x hx

end PackingSufficiencySupport

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function

 theorem exists_shifted_planar_embedding {A δ b : ℝ} (hA : 0≤A) (hδ : 0<δ) (hb : 0≤b) :
    ∃ p : Plane → Plane,
      (∀ x,radialArea x≤A → ContDiffAt ℝ ∞ p x) ∧
      InjOn p {x | radialArea x≤A} ∧
      (∀ x,radialArea x≤A → ∀ v w,
        planarArea (fderiv ℝ p x v) (fderiv ℝ p x w)=planarArea v w) ∧
      ∀ x,radialArea x≤A → b<radialArea (p x) ∧ radialArea (p x)<radialArea x+b+δ := by
  obtain ⟨q,hq,_hqi,hqform,hqbound⟩ := exists_thin_planar_embedding hA hδ
  let l : Plane → Plane := fun x => q x+(b,0)
  have hl : ContDiff ℝ ∞ l := hq.add contDiff_const
  have hlD (x v : Plane) : fderiv ℝ l x v=fderiv ℝ q x v := by
    rw [show l=(fun x => q x+(b,0)) from rfl,fderiv_add_const]
  let p : Plane → Plane := areaPolar ∘ l
  have hldom {x : Plane} (hx : radialArea x≤A) : l x∈areaPolarDomain := by
    obtain ⟨hx0,_hxu,hxθ⟩ := hqbound x hx
    exact ⟨by change 0<(q x).1+b; linarith,by simpa only [l,Prod.snd_add,add_zero] using hxθ⟩
  refine ⟨p,fun x hx => (areaPolar_smoothAt (hldom hx).1).comp x hl.contDiffAt,?_,?_,?_⟩
  · intro x hx y hy he
    have hh := areaPolar_injOn (hldom hx) (hldom hy) he
    exact q.injective (add_right_cancel hh)
  · intro x hx v w
    rw [show p=areaPolar ∘ l from rfl,
      fderiv_comp x ((areaPolar_smoothAt (hldom hx).1).differentiableAt (by simp))
        (hl.differentiable (by simp) x)]
    change planarArea (fderiv ℝ areaPolar (l x) (fderiv ℝ l x v))
      (fderiv ℝ areaPolar (l x) (fderiv ℝ l x w))=_
    rw [planarArea_map,areaPolar_det (hldom hx).1,one_mul,hlD,hlD,hqform]
  · intro x hx
    have hc : radialArea (p x)=(q x).1+b := areaPolar_capacity (hldom hx).1.le
    rw [hc]
    obtain ⟨hq0,hqδ,_⟩ := hqbound x hx
    constructor <;> linarith

 def headPlanarMap (n : ℕ) (p : Plane → Plane) : Ambient (n+1) → Ambient (n+1) :=
  headComplexAmbient n ∘ (fun x => (x.1,p x.2)) ∘ (headComplexAmbient n).symm

 theorem headComplexAmbient_split_capacity (n : ℕ) (x : Ambient (n+1)) :
    capacity ((headComplexAmbient n).symm x).1+radialArea ((headComplexAmbient n).symm x).2=capacity x := by
  rw [← headComplexAmbient_capacity,(headComplexAmbient n).apply_symm_apply]

 theorem headComplexAmbient_head_le {n : ℕ} {A : ℝ} {x : Ambient (n+1)}
    (hx : x∈closedBall (n+1) A) : radialArea ((headComplexAmbient n).symm x).2≤A := by
  have hc := capacity_nonneg ((headComplexAmbient n).symm x).1
  have hs := headComplexAmbient_split_capacity n x
  change capacity x≤A at hx
  linarith

 theorem headPlanarMap_capacity (n : ℕ) (p : Plane → Plane) (x : Ambient (n+1)) :
    capacity (headPlanarMap n p x)=
      capacity ((headComplexAmbient n).symm x).1+radialArea (p ((headComplexAmbient n).symm x).2) :=
  headComplexAmbient_capacity n _

 theorem headPlanarMap_first (n : ℕ) (p : Plane → Plane) (x : Ambient (n+1)) :
    Real.pi*Complex.normSq (headPlanarMap n p x 0)=radialArea (p ((headComplexAmbient n).symm x).2) := by
  change Real.pi*Complex.normSq (⟨(p ((headComplexAmbient n).symm x).2).1,
    (p ((headComplexAmbient n).symm x).2).2⟩ : ℂ)=_
  simp only [Complex.normSq_apply,radialArea,radiusSq,pow_two]

 theorem headPlanarMap_smoothAt {n : ℕ} {p : Plane → Plane} {x : Ambient (n+1)}
    (hp : ContDiffAt ℝ ∞ p ((headComplexAmbient n).symm x).2) :
    ContDiffAt ℝ ∞ (headPlanarMap n p) x :=
  (headComplexAmbient n).contDiff.contDiffAt.comp _
    ((contDiffAt_fst.prodMk (hp.comp _ contDiffAt_snd)).comp x
      (headComplexAmbient n).symm.contDiff.contDiffAt)

 theorem headPlanarMap_fderiv {n : ℕ} {p : Plane → Plane} {x : Ambient (n+1)}
    (hp : ContDiffAt ℝ ∞ p ((headComplexAmbient n).symm x).2) (v : Ambient (n+1)) :
    fderiv ℝ (headPlanarMap n p) x v=headComplexAmbient n
      (((headComplexAmbient n).symm v).1,
        fderiv ℝ p ((headComplexAmbient n).symm x).2 ((headComplexAmbient n).symm v).2) := by
  let e := headComplexAmbient n
  have hdF := (hasFDerivAt_fst (𝕜 := ℝ) (p := e.symm x)).prodMk
    ((hp.differentiableAt (by simp)).hasFDerivAt.comp _ (hasFDerivAt_snd (𝕜 := ℝ) (p := e.symm x)))
  have hdf := e.hasFDerivAt.comp x (hdF.comp x e.symm.hasFDerivAt)
  change HasFDerivAt (headPlanarMap n p) _ x at hdf
  rw [hdf.fderiv]
  rfl

 theorem headPlanarMap_injOn {n : ℕ} {p : Plane → Plane} {A : ℝ}
    (hp : InjOn p {x | radialArea x≤A}) : InjOn (headPlanarMap n p) (closedBall (n+1) A) := by
  intro x hx y hy he
  let e := headComplexAmbient n
  have hF : ((e.symm x).1,p (e.symm x).2)=((e.symm y).1,p (e.symm y).2) := e.injective he
  have hfst := congrArg (fun z : Ambient n × Plane => z.1) hF
  have hsnd := congrArg (fun z : Ambient n × Plane => z.2) hF
  apply e.symm.injective
  exact Prod.ext hfst (hp (headComplexAmbient_head_le hx) (headComplexAmbient_head_le hy) hsnd)

 theorem headPlanarMap_form {n : ℕ} {p : Plane → Plane} {x : Ambient (n+1)}
    (hp : ContDiffAt ℝ ∞ p ((headComplexAmbient n).symm x).2)
    (hf : ∀ v w,planarArea (fderiv ℝ p ((headComplexAmbient n).symm x).2 v)
      (fderiv ℝ p ((headComplexAmbient n).symm x).2 w)=planarArea v w) (v w : Ambient (n+1)) :
    standardForm (fderiv ℝ (headPlanarMap n p) x v) (fderiv ℝ (headPlanarMap n p) x w)=standardForm v w := by
  rw [headPlanarMap_fderiv hp,headPlanarMap_fderiv hp,headComplexAmbient_form,hf]
  change standardForm ((headComplexAmbient n).symm v).1 ((headComplexAmbient n).symm w).1+
    planarArea ((headComplexAmbient n).symm v).2 ((headComplexAmbient n).symm w).2=_
  rw [← headComplexAmbient_form]
  simp only [(headComplexAmbient n).apply_symm_apply]

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport
open scoped ContDiff Topology
open Set Function
open Hamiltonian

 theorem exists_distinguished_ball_embedding (n : ℕ) {A b : ℝ}
    (hA : 0≤A) (hb : 0≤b) (hAb : A+b<1) :
    ∃ f : Ambient (n+1) → Ambient (n+1),IsBallEmbedding A f ∧
      f '' closedBall (n+1) A ⊆ openBall (n+1) 1 ∧
      ∀ x∈closedBall (n+1) A,b<Real.pi*Complex.normSq (f x 0) := by
  obtain ⟨A',hAA',hA'b⟩ := exists_between (show A<1-b by linarith)
  obtain ⟨δ,hδ,hδb⟩ := exists_between (show (0:ℝ)<1-b-A' by linarith)
  obtain ⟨p,hp,hpInj,hpform,hpcap⟩ := exists_shifted_planar_embedding (hA.trans hAA'.le) hδ hb
  let f := headPlanarMap n p
  have hf {x : Ambient (n+1)} (hx : x∈closedBall (n+1) A') : ContDiffAt ℝ ∞ f x :=
    headPlanarMap_smoothAt (hp _ (headComplexAmbient_head_le hx))
  have hfemb : Topology.IsEmbedding (fun x : closedBall (n+1) A' => f x.val) := by
    let : CompactSpace (closedBall (n+1) A') := isCompact_iff_compactSpace.mp (closedBall_isCompact _ _)
    have hc : ContinuousOn f (closedBall (n+1) A') := fun x hx => (hf hx).continuousAt.continuousWithinAt
    exact (hc.domRestrict.isClosedEmbedding (fun x y he =>
      Subtype.ext (headPlanarMap_injOn hpInj x.property y.property he))).isEmbedding
  refine ⟨f,⟨openBall (n+1) A',openBall_isOpen _ _,?_,?_,?_,?_⟩,?_,?_⟩
  · intro x hx
    exact (show capacity x≤A from hx).trans_lt hAA'
  · intro x hx
    exact (hf (show capacity x≤A' from le_of_lt hx)).contDiffWithinAt
  · exact hfemb.comp (Topology.IsEmbedding.inclusion (fun x hx => (show capacity x<A' from hx).le))
  · intro x hx v w
    have hh := headComplexAmbient_head_le (show capacity x≤A' from (show capacity x<A' from hx).le)
    exact headPlanarMap_form (hp _ hh) (hpform _ hh) v w
  · rintro y ⟨x,hx,rfl⟩
    have hx' : x∈closedBall (n+1) A' := (show capacity x≤A from hx).trans hAA'.le
    change capacity (headPlanarMap n p x)<1
    rw [headPlanarMap_capacity]
    have hbq := (hpcap _ (headComplexAmbient_head_le hx')).2
    have hs := headComplexAmbient_split_capacity n x
    change capacity x≤A at hx
    linarith
  · intro x hx
    have hx' : x∈closedBall (n+1) A' := (show capacity x≤A from hx).trans hAA'.le
    change b<Real.pi*Complex.normSq (headPlanarMap n p x 0)
    rw [headPlanarMap_first]
    exact (hpcap _ (headComplexAmbient_head_le hx')).1

end PackingSufficiencySupport

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Manifold
open Hamiltonian

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

 theorem exists_actual_normal_transfer {d : ℝ} (hd : 0<d) (hdhalf : d<1/2)
    {K : Set (NormalSpace a)} (hK : IsCompact K)
    (hKd : ∀ p∈K,phaseSq p.2<d/Real.pi) :
    ∃ t : ℝ,0<t ∧ ∃ g : NormalSpace a → Affine m,∃ W : Set (NormalSpace a),
      IsOpen W ∧ K⊆W ∧ ContMDiff 𝓘(ℝ,NormalModel m) 𝓘(ℝ,Affine m) ∞ g ∧
      Topology.IsEmbedding (fun x : W => g x.val) ∧
      ∀ x∈W,∀ v w,normalAmbientForm a (1/Real.pi) d t (g x)
        (manifoldMapDifferential (E := Affine m) (F := NormalModel m) g x v)
        (manifoldMapDifferential (E := Affine m) (F := NormalModel m) g x w)=
        globalHorizontalCoupling phaseArea (normalHorizontalPrimitive (q := m) a 2 ∘ planeMoments) x v w := by
  let : SigmaCompactSpace (locus a) := IsClosed.sigmaCompactSpace (locus_isClosed a)
  obtain ⟨Ξ,hΞ,D,hD,hKD,hDd,hΞemb,hΞeq⟩ := exists_compact_radial_bridge a hd hK hKd
  have hIK : IsCompact (Ξ '' K) := hK.image hΞ.continuous
  obtain ⟨Ψ,Γ,δ,hδ,U,hU,hUK,hΨ,hΓ,hΓ0,hΨemb,hΓform⟩ :=
    exists_actual_normal_exact_family a (hIK.image continuous_fst) (hIK.image continuous_snd) (1/Real.pi) d
  have hKU : MapsTo Ξ K U := by
    intro x hx
    exact hUK ⟨⟨Ξ x,⟨x,hx,rfl⟩,rfl⟩,⟨Ξ x,⟨x,hx,rfl⟩,rfl⟩⟩
  let Δ : ℝ → ManifoldOneForm (NormalModel m) (NormalSpace a) := manifoldPullbackOneForm Γ Ξ
  have hΔ : SmoothOneFormFamily Δ := manifoldPullbackOneForm_smooth hΞ hΓ
  have hΔ0 (x : NormalSpace a) (hx : x∈D) : Δ 0 x=normalCouplingPrimitive a x := by
    change manifoldPullbackOneForm Γ Ξ 0 x=_
    have h := cone_radial_primitive a hd hΞ (hDd x hx)
      (hΞeq.eventuallyEq_of_mem (hD.mem_nhds hx))
    simpa only [manifoldPullbackOneForm,hΓ0] using h
  have hΔext (x : NormalSpace a) (hx : x∈D) :
      manifoldExteriorOneForm (Δ 0) x=manifoldExteriorOneForm (normalCouplingPrimitive a) x := by
    apply manifoldExteriorOneForm_congr_germ
    filter_upwards [hD.mem_nhds hx] with y hy
    exact hΔ0 y hy
  have hinv (x : NormalSpace a) (hx : x∈K) : (manifoldExteriorOneForm (Δ 0) x).IsInvertible := by
    rw [hΔext x (hKD hx)]
    apply normalCoupling_invertible a hdhalf
    simpa only [mul_comm] using ((lt_div_iff₀ Real.pi_pos).mp (hKd x hx)).le
  let A : ℝ × NormalSpace a → Affine m := fun p => Ψ (p.1,Ξ p.2)
  have hA : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,NormalModel m)) 𝓘(ℝ,Affine m) ∞ A :=
    hΨ.comp (contMDiff_fst.prodMk (hΞ.comp contMDiff_snd))
  let V := D∩Ξ ⁻¹' U
  have hV : IsOpen V := hD.inter (hU.preimage hΞ.continuous)
  have hKV : K⊆V := fun x hx => ⟨hKD hx,hKU hx⟩
  have htI {t : ℝ} (ht : t∈Ioc (0:ℝ) δ) : t∈Icc (-δ) δ := ⟨by linarith [ht.1],ht.2⟩
  have hAemb (t : ℝ) (ht : t∈Ioc (0:ℝ) δ) : Topology.IsEmbedding (fun x : V => A (t,x.val)) := by
    exact (hΨemb t (htI ht) (ne_of_gt ht.1)).comp
      (((hΞemb.comp (Topology.IsEmbedding.inclusion inter_subset_left)).codRestrict U)
        (fun x : V => x.property.2))
  have hAform (t : ℝ) (ht : t∈Ioc (0:ℝ) δ) (x : NormalSpace a) (hx : x∈V) :
      manifoldExteriorOneForm (Δ t) x=(normalAmbientForm a (1/Real.pi) d t (A (t,x))).bilinearComp
        (manifoldMapDifferential (E := Affine m) (F := NormalModel m) (fun y => A (t,y)) x)
        (manifoldMapDifferential (E := Affine m) (F := NormalModel m) (fun y => A (t,y)) x) := by
    have hs := hΨ.comp (contMDiff_const.prodMk contMDiff_id) (f := fun y : ConeSpace a => (t,y))
    have he := manifold_pullback_exterior (fun c y hy => (hΓ.spatial_smooth t c hy).contDiffWithinAt) hΞ x
    change manifoldExteriorOneForm (Δ t) x=
      (manifoldExteriorOneForm (Γ t) (Ξ x)).bilinearComp
        (manifoldMapDifferential (E := ConeModel m) (F := NormalModel m) Ξ x)
        (manifoldMapDifferential (E := ConeModel m) (F := NormalModel m) Ξ x) at he
    rw [he,hΓform t (htI ht) (ne_of_gt ht.1) (Ξ x) hx.2]
    have hdiff := manifoldMapDifferential_comp
      (hs.mdifferentiable (by simp) (Ξ x)) (hΞ.mdifferentiable (by simp) x)
    change manifoldMapDifferential (E := Affine m) (F := NormalModel m) (fun y => A (t,y)) x=_ at hdiff
    rw [hdiff]
    rfl
  obtain ⟨t,ht,g,W,hW,hKW,hg,hgemb,hgform⟩ := exists_compact_exact_fibre_embedding
    hΔ hK hinv hV hKV hδ hA hAemb (fun t => normalAmbientForm a (1/Real.pi) d t) hAform
  refine ⟨t,ht.1,g,W∩D,hW.inter hD,fun x hx => ⟨hKW hx,hKD hx⟩,hg,
    hgemb.comp (Topology.IsEmbedding.inclusion inter_subset_left),?_⟩
  intro x hx v w
  have he := hgform x hx.1 v w
  rw [hΔext x hx.2,normalCouplingPrimitive_exterior] at he
  exact he

end PackingSufficiencySupport.DiagonalQuadrics

namespace PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
open Hamiltonian MomentPolytope

 theorem actual_small_polynomial_packing (m : ℕ) {N : ℕ} [Nonempty (Fin N)]
    (r r' : Fin N → ℝ) (hr : ∀ i,0<r i) (hr' : ∀ i,0≤r' i)
    (hrr : ∀ i,r' i<r i) (hhalf : ∀ i,r i<1/2)
    (hvol : ∑ i,r i^(m+3)<1) :
    ∃ d t : ℝ,0<d ∧ d<1/2 ∧ 0<t ∧
      ∃ f : Fin N → Ambient (m+3) → Affine (m+2),
        (∀ i,FormNeighborhoodEmbedding (closedBall (m+3) (r' i))
          (fun _ => successorStandardForm (m+2))
          (normalAmbientForm (parameters m) (1/Real.pi) d t) (f i)) ∧
        Pairwise (fun i j => Disjoint (f i '' closedBall (m+3) (r' i))
          (f j '' closedBall (m+3) (r' j))) := by
  classical
  obtain ⟨h,d,hrh,hhd,hdhalf,ℓ,φ,hφ,hφK,hdisj⟩ :=
    actual_small_normal_packing m r r' hr hr' hrr hhalf hvol
  let K : Set (NormalSpace (parameters m)) := ⋃ i,φ i '' closedBall (m+3) (r' i)
  have hK : IsCompact K := by
    apply isCompact_iUnion
    intro i
    obtain ⟨U,_hU,hKU,hs,_he,_hf⟩ := hφ i
    exact (closedBall_isCompact (m+3) (r' i)).image_of_continuousOn (hs.continuousOn.mono hKU)
  have hhdR : (h:ℝ)<d := by exact_mod_cast hhd
  have hd : 0<(d:ℝ) := by
    obtain ⟨i⟩ := ‹Nonempty (Fin N)›
    exact ((hr i).trans (hrh i)).trans hhdR
  have hKd (p : NormalSpace (parameters m)) (hp : p∈K) : phaseSq p.2<(d:ℝ)/Real.pi := by
    obtain ⟨i,x,hx,rfl⟩ := mem_iUnion.mp hp
    have hm := (interior_subset (hφK i hx)).2.2
    have he : (∑ j,planeMoments (φ i x).2 j)=Real.pi*phaseSq (φ i x).2 := by
      simp only [planeMoments,radialArea,radiusSq,phaseSq,phaseDot_apply,pow_two,← Finset.mul_sum]
    rw [he] at hm
    exact (lt_div_iff₀ Real.pi_pos).mpr (by simpa only [mul_comm] using hm.trans_lt hhdR)
  obtain ⟨t,ht,g,W,hW,hKW,hg,hgemb,hgform⟩ :=
    exists_actual_normal_transfer (parameters m) hd hdhalf hK hKd
  obtain ⟨hf,hdj⟩ := postcompose_form_packing (fun i => closedBall (m+3) (r' i))
    (fun _ => successorStandardForm (m+2))
    (globalHorizontalCoupling phaseArea (normalHorizontalPrimitive (parameters m) 2 ∘ planeMoments))
    (normalAmbientForm (parameters m) (1/Real.pi) d t)
    hW g hg.contMDiffOn hgemb hgform φ hφ
    (fun i x hx => hKW (mem_iUnion.mpr ⟨i,x,hx,rfl⟩)) hdisj
  exact ⟨d,t,hd,hdhalf,ht,fun i => g ∘ φ i,hf,hdj⟩

end PackingSufficiencySupport.DiagonalQuadrics.Explicit

namespace PackingSufficiencySupport
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
open Hamiltonian DiagonalQuadrics DiagonalQuadrics.Explicit
open CubicModel

 theorem hasPacking_small_enlarged (m : ℕ) {N : ℕ} [Nonempty (Fin N)]
    (r r' : Fin N → ℝ) (hr : ∀ i,0<r i) (hr' : ∀ i,0≤r' i)
    (hrr : ∀ i,r' i<r i) (hhalf : ∀ i,r i<1/2)
    (hvol : ∑ i,r i^(m+3)<1) : HasPacking (m+3) N 1 r' := by
  obtain ⟨d,t,hd,hdhalf,_ht,φ,hφ,hdisj⟩ :=
    actual_small_polynomial_packing m r r' hr hr' hrr hhalf hvol
  obtain ⟨g,hg,hgemb,hgmem,hgform⟩ :=
    exists_polynomial_target_embedding (parameters m) t
      (one_div_pos.mpr Real.pi_pos) hd.le hdhalf
  have hform (x : Affine (m+2)) (_hx : x∈(univ : Set (Affine (m+2)))) (v w) :
      successorStandardForm (m+2) (mfderiv 𝓘(ℝ,Affine (m+2)) 𝓘(ℝ,Ambient (m+3)) g x v)
        (mfderiv 𝓘(ℝ,Affine (m+2)) 𝓘(ℝ,Ambient (m+3)) g x w)=
      normalAmbientForm (parameters m) (1/Real.pi) d t x v w := by
    rw [mfderiv_eq_fderiv]
    exact (successorStandardForm_apply _ _ _).trans (hgform x v w)
  obtain ⟨hf,hdj⟩ := postcompose_form_packing (fun i => closedBall (m+3) (r' i))
    (fun _ => successorStandardForm (m+2))
    (normalAmbientForm (parameters m) (1/Real.pi) d t)
    (fun _ => successorStandardForm (m+2)) isOpen_univ g hg.contMDiff.contMDiffOn
    (hgemb.comp Topology.IsEmbedding.subtypeVal) hform φ hφ
    (fun _ _ _ => mem_univ _) hdisj
  refine ⟨fun i => g ∘ φ i,fun i => isBallEmbedding_iff_formNeighborhoodEmbedding.mpr (hf i),?_,?_⟩
  · intro i y hy
    obtain ⟨x,_hx,rfl⟩ := hy
    simpa only [mul_one_div_cancel Real.pi_ne_zero,Function.comp_apply] using hgmem (φ i x)
  · intro i j hij
    exact hdj hij

 theorem hasPacking_small_normalized {n N : ℕ} (hn : 3≤n) (hN : 1≤N)
    (r : Fin N → ℝ) (hr : ∀ i,0<r i) (hhalf : ∀ i,r i<1/2)
    (hvol : ∑ i,r i^n<1) : HasPacking n N 1 r := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hn
  have hs : 3+m=m+3 := Nat.add_comm _ _
  simp only [hs] at hvol ⊢
  let : NeZero N := ⟨by omega⟩
  obtain ⟨q,hq,hqhalf,hqvol⟩ := rational_small_slack (m+3) r hhalf hvol
  exact hasPacking_small_enlarged m (fun i => (q i:ℝ)) r
    (fun i => (hr i).trans (hq i)) (fun i => (hr i).le) hq hqhalf hqvol

 theorem hasPacking_small {n N : ℕ} (hn : 3≤n) (hN : 1≤N)
    {R : ℝ} (hR : 0<R) (r : Fin N → ℝ) (hr : ∀ i,0<r i)
    (hhalf : ∀ i,r i<R/2) (hvol : ∑ i,r i^n<R^n) :
    HasPacking n N R r := by
  apply (hasPacking_normalize hR).mpr
  apply hasPacking_small_normalized hn hN (fun i => r i/R)
    (fun i => div_pos (hr i) hR)
  · intro i
    apply (div_lt_iff₀ hR).mpr
    nlinarith [hhalf i]
  · simp only [div_pow,←Finset.sum_div]
    exact (div_lt_one (pow_pos hR n)).mpr hvol

 theorem hasPacking_large_enlarged (m : ℕ) {N : ℕ} [Nonempty (Fin N)]
    (r r' : Fin (N+1) → ℝ) (hr : ∀ i,0<r i) (hr' : ∀ i,0≤r' i)
    (hrr : ∀ i,r' i<r i) (hlarge : 1/2≤r 0)
    (hvol : ∑ i,r i^(m+4)<1) (hpair : ∀ i j,i≠j → r i+r j<1) :
    HasPacking (m+4) (N+1) 1 r' := by
  have ha : r 0<1 := by
    obtain ⟨i⟩ := ‹Nonempty (Fin N)›
    have hp := hpair 0 i.succ (Fin.succ_ne_zero i).symm
    linarith [hr i.succ]
  have htail (i : Fin N) : r i.succ<1-r 0 := by
    have := hpair 0 i.succ (Fin.succ_ne_zero i).symm
    linarith
  have htvol : ∑ i : Fin N,r i.succ^(m+4)<1-r 0^(m+4) := by
    rw [Fin.sum_univ_succ] at hvol
    linarith
  obtain ⟨b,hb,f,hf,hfmem,hfb,hfd⟩ := actual_complement_packing m
    (fun i => r i.succ) (fun i => r' i.succ) (fun i => hr i.succ)
    (fun i => hr' i.succ) (fun i => hrr i.succ) (hr 0) ha htail
    (fun i => by linarith [htail i]) htvol
  have hb0 : 0≤b := by
    obtain ⟨i⟩ := ‹Nonempty (Fin N)›
    have hzero : (0 : Ambient (m+4))∈closedBall (m+4) (r' i.succ) := by
      simpa only [closedBall,mem_ofPred_eq,capacity,Pi.zero_apply,Complex.normSq_zero,
        Finset.sum_const_zero,mul_zero] using hr' i.succ
    have h := hfb i 0 hzero
    exact (mul_nonneg Real.pi_pos.le (Complex.normSq_nonneg _)).trans h.le
  obtain ⟨g,hg,hgmem,hgb⟩ := exists_distinguished_ball_embedding (m+3) (hr' 0) hb0
    (by linarith [hrr 0])
  let F : Fin (N+1) → Ambient (m+4) → Ambient (m+4) := Fin.cons g f
  refine ⟨F,?_,?_,?_⟩
  · intro i
    exact Fin.cases hg hf i
  · intro i
    exact Fin.cases hgmem hfmem i
  · have hgf (i : Fin N) : Disjoint (g '' closedBall (m+4) (r' 0))
        (f i '' closedBall (m+4) (r' i.succ)) := by
      apply Set.disjoint_left.mpr
      rintro y ⟨x,hx,rfl⟩ ⟨z,hz,he⟩
      have hl := hgb x hx
      have hu := hfb i z hz
      rw [he] at hu
      exact (not_lt_of_ge hl.le) hu
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro j
      refine Fin.cases ?_ (fun j _ => hgf j) j
      intro hij
      exact False.elim (hij rfl)
    · intro j
      refine Fin.cases (fun _ => Disjoint.symm (hgf i)) (fun j hij => ?_) j
      apply hfd
      intro he
      exact hij (congrArg Fin.succ he)

 theorem HasPacking.reindex {n N : ℕ} {R : ℝ} {r : Fin N → ℝ}
    (hp : HasPacking n N R r) (e : Equiv.Perm (Fin N)) :
    HasPacking n N R (r ∘ e) := by
  obtain ⟨f,hf,hm,hd⟩ := hp
  exact ⟨f ∘ e,fun i => hf (e i),fun i => hm (e i),
    fun i j hij => hd (e i) (e j) (fun h => hij (e.injective h))⟩

 theorem hasPacking_large_normalized (m : ℕ) {N : ℕ} [Nonempty (Fin N)]
    (r : Fin (N+1) → ℝ) (hr : ∀ i,0<r i) (hlarge : 1/2≤r 0)
    (hvol : ∑ i,r i^(m+4)<1) (hpair : ∀ i j,i≠j → r i+r j<1) :
    HasPacking (m+4) (N+1) 1 r := by
  obtain ⟨q,hq,hqvol,hqpair⟩ := rational_packing_slack (m+4) 1 r (by simpa using hvol) hpair
  exact hasPacking_large_enlarged m (fun i => (q i:ℝ)) r (fun i => (hr i).trans (hq i))
    (fun i => (hr i).le) hq (hlarge.trans (hq 0).le) (by simpa using hqvol) hqpair

 theorem hasPacking_dim_ge_four_normalized {n N : ℕ} (hn : 4≤n) (hN : 1≤N)
    (r : Fin N → ℝ) (hr : ∀ i,0<r i)
    (hvol : ∑ i,r i^n<1) (hpair : ∀ i j,i≠j → r i+r j<1) : HasPacking n N 1 r := by
  classical
  by_cases hsmall : ∀ i,r i<1/2
  · exact hasPacking_small_normalized (by omega) hN r hr hsmall hvol
  obtain ⟨j,hj⟩ := not_forall.mp hsmall
  have hj : 1/2≤r j := le_of_not_gt hj
  obtain ⟨m,hm⟩ := Nat.exists_eq_add_of_le hn
  have hn' : n=m+4 := by omega
  clear hm
  subst n
  cases N with
  | zero => omega
  | succ K =>
    cases K with
    | zero =>
      have heqr : r=(fun _ => r 0) := funext fun i => congrArg r (Fin.eq_zero i)
      rw [heqr] at hvol ⊢
      apply (hasPacking_one_iff (by omega) zero_lt_one (hr 0)).mpr
      exact lt_of_pow_lt_pow_left₀ (m+4) zero_le_one (by simpa using hvol)
    | succ K =>
      let e : Equiv.Perm (Fin (K+1+1)) := Equiv.swap 0 j
      have hrvol : ∑ i,(r (e i))^(m+4)<1 := by
        rw [show (∑ i,r (e i)^(m+4))=(∑ i,r i^(m+4)) from
          Equiv.sum_comp e (fun i => r i^(m+4))]
        exact hvol
      have hrlarge : 1/2≤(r ∘ e) 0 := by
        simpa only [Function.comp_apply,e,Equiv.swap_apply_left] using hj
      have hp := hasPacking_large_normalized m (r ∘ e) (fun i => hr (e i))
        hrlarge hrvol (fun i j hij => hpair (e i) (e j) (fun h => hij (e.injective h)))
      have hh := hp.reindex e.symm
      simpa only [Function.comp_def,Equiv.apply_symm_apply] using hh

 theorem hasPacking_dim_ge_four {n N : ℕ} (hn : 4≤n) (hN : 1≤N)
    {R : ℝ} (hR : 0<R) (r : Fin N → ℝ) (hr : ∀ i,0<r i)
    (hvol : ∑ i,r i^n<R^n) (hpair : ∀ i j,i≠j → r i+r j<R) : HasPacking n N R r := by
  apply (hasPacking_normalize hR).mpr
  apply hasPacking_dim_ge_four_normalized hn hN (fun i => r i/R) (fun i => div_pos (hr i) hR)
  · simp only [div_pow,← Finset.sum_div]
    exact (div_lt_one (pow_pos hR n)).mpr hvol
  · intro i j hij
    rw [← add_div]
    exact (div_lt_one hR).mpr (hpair i j hij)

 theorem hasPacking_six_large_normalized {N : ℕ} [Nonempty (Fin N)]
    (r : Fin (N+1) → ℝ) (hr : ∀ i,0<r i) (hlarge : 1/2≤r 0)
    (hvol : ∑ i,r i^3<1) (hpair : ∀ i j,i≠j → r i+r j<1) :
    HasPacking 3 (N+1) 1 r := by
  obtain ⟨q,hq,hqvol,hqpair⟩ := rational_packing_slack 3 1 r (by simpa using hvol) hpair
  have ha : (1:ℚ)/2<q 0 := by
    have hh : (1:ℝ)/2<(q 0:ℝ) := hlarge.trans_lt (hq 0)
    apply (Rat.cast_lt (K := ℝ)).mp
    simpa using hh
  have ha1 : q 0<1 := by
    obtain ⟨i⟩ := ‹Nonempty (Fin N)›
    have hh := hqpair 0 i.succ (Fin.succ_ne_zero i).symm
    have hp := (hr i.succ).trans (hq i.succ)
    have h : (q 0:ℝ)<1 := by linarith
    exact_mod_cast h
  have htail (i : Fin N) : (q i.succ:ℝ)<1-(q 0:ℝ) := by
    have hh := hqpair 0 i.succ (Fin.succ_ne_zero i).symm
    linarith
  have htvol : ∑ i : Fin N,(q i.succ:ℝ)^3<1-(q 0:ℝ)^3 := by
    rw [Fin.sum_univ_succ] at hqvol
    norm_num at hqvol
    linarith
  have hp := actual_six_standard_packing (fun i => (q i.succ:ℝ)) (fun i => r i.succ)
    (fun i => (hr i.succ).trans (hq i.succ)) (fun i => (hr i.succ).le)
    (fun i => hq i.succ) ha ha1 htail htvol (hr 0).le (hq 0)
  have he : Fin.cons (r 0) (fun i => r i.succ)=r := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rwa [he] at hp

 theorem hasPacking_six_normalized {N : ℕ} (hN : 1≤N)
    (r : Fin N → ℝ) (hr : ∀ i,0<r i)
    (hvol : ∑ i,r i^3<1) (hpair : ∀ i j,i≠j → r i+r j<1) : HasPacking 3 N 1 r := by
  classical
  by_cases hsmall : ∀ i,r i<1/2
  · exact hasPacking_small_normalized (by omega) hN r hr hsmall hvol
  obtain ⟨j,hj⟩ := not_forall.mp hsmall
  have hj : 1/2≤r j := le_of_not_gt hj
  cases N with
  | zero => omega
  | succ K =>
    cases K with
    | zero =>
      have heqr : r=(fun _ => r 0) := funext fun i => congrArg r (Fin.eq_zero i)
      rw [heqr] at hvol ⊢
      apply (hasPacking_one_iff (by omega) zero_lt_one (hr 0)).mpr
      exact lt_of_pow_lt_pow_left₀ 3 zero_le_one (by simpa using hvol)
    | succ K =>
      let e : Equiv.Perm (Fin (K+1+1)) := Equiv.swap 0 j
      have hrvol : ∑ i,(r (e i))^3<1 := by
        rw [show (∑ i,r (e i)^3)=(∑ i,r i^3) from Equiv.sum_comp e (fun i => r i^3)]
        exact hvol
      have hrlarge : 1/2≤(r ∘ e) 0 := by
        simpa only [Function.comp_apply,e,Equiv.swap_apply_left] using hj
      have hp := hasPacking_six_large_normalized (r ∘ e) (fun i => hr (e i))
        hrlarge hrvol (fun i j hij => hpair (e i) (e j) (fun h => hij (e.injective h)))
      have hh := hp.reindex e.symm
      simpa only [Function.comp_def,Equiv.apply_symm_apply] using hh

 theorem hasPacking_of_inequalities {n N : ℕ} (hn : 3≤n) (hN : 1≤N)
    {R : ℝ} (hR : 0<R) (r : Fin N → ℝ) (hr : ∀ i,0<r i)
    (hvol : ∑ i,r i^n<R^n) (hpair : ∀ i j,i≠j → r i+r j<R) : HasPacking n N R r := by
  by_cases hfour : 4≤n
  · exact hasPacking_dim_ge_four hfour hN hR r hr hvol hpair
  have hn3 : n=3 := by omega
  subst n
  apply (hasPacking_normalize hR).mpr
  apply hasPacking_six_normalized hN (fun i => r i/R) (fun i => div_pos (hr i) hR)
  · simp only [div_pow,← Finset.sum_div]
    exact (div_lt_one (pow_pos hR 3)).mpr hvol
  · intro i j hij
    rw [← add_div]
    exact (div_lt_one hR).mpr (hpair i j hij)

end PackingSufficiencySupport

namespace HigherDimensionalBallPacking
open scoped ContDiff Topology
open Set Function
open scoped BigOperators

 theorem HasPacking.subfamily {n k ℓ : ℕ} {R : ℝ} {r : Fin k → ℝ}
    (hp : HasPacking n k R r) (e : Fin ℓ ↪ Fin k) :
    HasPacking n ℓ R (r ∘ e) := by
   obtain ⟨U,f,hf,hd⟩ := hp
   exact ⟨U ∘ e,f ∘ e,fun i => hf (e i),
     fun i j hij => hd (e i) (e j) (fun he => hij (e.injective he))⟩

 theorem HasPacking.two_balls {n k : ℕ} {R : ℝ} {r : Fin k → ℝ}
    (hp : HasPacking n k R r) {i j : Fin k} (hij : i≠j) :
    HasPacking n 2 R ![r i,r j] := by
   let e : Fin 2 ↪ Fin k := ⟨![i,j],by
     intro a b he
     fin_cases a <;> fin_cases b
     · rfl
     · exact False.elim (hij he)
     · exact False.elim (hij he.symm)
     · rfl⟩
   have he : r ∘ e=![r i,r j] := by
     funext a
     fin_cases a <;> rfl
   simpa only [he] using hp.subfamily e

 theorem HasPacking.two_balls_smaller_target {n k : ℕ} {R : ℝ} {r : Fin k → ℝ}
    (hp : HasPacking n k R r) (hR : 0<R) {i j : Fin k} (hij : i≠j) :
    ∃ σ,0<σ ∧ σ<R ∧ HasPacking n 2 σ ![r i,r j] := by
   obtain ⟨σ,hσ,hσR,hpσ⟩ := (hasPacking_iff_support.mp hp).exists_smaller_target hR
   exact ⟨σ,hσ,hσR,(hasPacking_iff_support.mpr hpσ).two_balls hij⟩

 theorem HasPacking.unit_pair_counterexample {n k : ℕ} {R : ℝ} {r : Fin k → ℝ}
    (hp : HasPacking n k R r) (hR : 0<R) (hr : ∀ i,0<r i)
    {i j : Fin k} (hij : i≠j) (hbad : R≤r i+r j) :
    ∃ a b : ℝ,0<a ∧ 0<b ∧ 1<a+b ∧ HasPacking n 2 1 ![a,b] := by
   obtain ⟨σ,hσ,hσR,hpσ⟩ := hp.two_balls_smaller_target hR hij
   have hp' := (PackingSufficiencySupport.hasPacking_normalize hσ).mp
     (hasPacking_iff_support.mp hpσ)
   have he : (fun l : Fin 2 => (![r i,r j] : Fin 2 → ℝ) l/σ)=![r i/σ,r j/σ] := by
     funext l
     fin_cases l <;> rfl
   refine ⟨r i/σ,r j/σ,div_pos (hr i) hσ,div_pos (hr j) hσ,?_,?_⟩
   · rw [←add_div]
     exact (one_lt_div hσ).mpr (hσR.trans_le hbad)
   · apply hasPacking_iff_support.mpr
     simpa only [he] using hp'

theorem hasPacking_of_inequalities_dim_ge_four {n k : ℕ} (hn : 4≤n) (hk : 1≤k)
    {R : ℝ} {r : Fin k → ℝ} (hR : 0<R) (hr : ∀ i,0<r i)
    (h : PackingInequalities n k R r) : HasPacking n k R r := by
  exact hasPacking_iff_support.mpr
    (PackingSufficiencySupport.hasPacking_dim_ge_four hn hk hR r hr h.1 h.2)

theorem hasPacking_all_small {n k : ℕ} (hn : 3≤n) (hk : 1≤k)
    {R : ℝ} {r : Fin k → ℝ} (hR : 0<R) (hr : ∀ i,0<r i)
    (hsmall : ∀ i,r i<R/2) (hvol : ∑ i,r i^n<R^n) : HasPacking n k R r := by
  exact hasPacking_iff_support.mpr
    (PackingSufficiencySupport.hasPacking_small hn hk hR r hr hsmall hvol)

theorem hasPacking_of_inequalities {n k : ℕ} (hn : 3≤n) (hk : 1≤k)
    {R : ℝ} {r : Fin k → ℝ} (hR : 0<R) (hr : ∀ i,0<r i)
    (h : PackingInequalities n k R r) : HasPacking n k R r := by
  exact hasPacking_iff_support.mpr
    (PackingSufficiencySupport.hasPacking_of_inequalities hn hk hR r hr h.1 h.2)

theorem one_ball_main {n : ℕ} (hn : 3≤n) {R : ℝ} {r : Fin 1 → ℝ}
    (hR : 0<R) (hr : ∀ i,0<r i) :
    HasPacking n 1 R r ↔ PackingInequalities n 1 R r := by
  constructor
  · intro hp
    refine ⟨hp.volume_lt (by omega) hR hr,?_⟩
    intro i j hij
    exact False.elim (hij (Subsingleton.elim i j))
  · intro h
    have hn0 : 0<n := by omega
    have hrR : r 0<R := by
      apply lt_of_pow_lt_pow_left₀ n hR.le
      simpa using h.1
    have heqr : r=(fun _ => r 0) := funext (fun i => congrArg r (Fin.eq_zero i))
    apply hasPacking_iff_support.mpr
    rw [heqr]
    exact (PackingSufficiencySupport.hasPacking_one_iff hn0 hR (hr 0)).mpr hrR

end HigherDimensionalBallPacking
end

end OAI
