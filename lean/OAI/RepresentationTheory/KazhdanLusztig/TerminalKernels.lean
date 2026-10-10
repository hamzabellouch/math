import OAI.RepresentationTheory.KazhdanLusztig.PositiveTransfer

namespace OAI

/-!
All-section transport, terminal kernels, scalar quotients, height-one membership in free targets and scaled edge-image inclusion.
-/

section

namespace KLInvariance.MomentGraph.Sheaf.Iso
universe ur uv ue uz uz'
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} {G : OrderedGraph V E}
  {B : Sheaf.{ur,uv,ue,uz} (R := R) G} {C : Sheaf.{ur,uv,ue,uz'} (R := R) G}
  (j : Iso B C)

include j in
 theorem scaledImages (e : E) (F : Set (Outgoing (G := G) (G.source e)))
    (H : Set (Outgoing (G := G) (G.target e))) (r : R)
    (h : B.ScaledImages e F H r) : C.ScaledImages e F H r := by
  intro z
  constructor
  · rintro ⟨v,hv,he⟩
    have hv' : (j.vertex (G.source e)).symm v ∈ B.upwardKernel (G.source e) F := by
      apply (j.upwardKernel_iff _ _ _).mp
      simpa only [LinearEquiv.apply_symm_apply] using hv
    have he' : B.lower e ((j.vertex (G.source e)).symm v)=(j.edge e).symm z := by
      apply (j.edge e).injective
      rw [j.lower,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply,he]
    obtain ⟨w,hw,hew⟩ := (h ((j.edge e).symm z)).mp ⟨_,hv',he'⟩
    refine ⟨j.vertex (G.target e) w,(j.upwardKernel_iff _ _ _).mpr hw,?_⟩
    rw [← j.upper,← map_smul,hew,LinearEquiv.apply_symm_apply]
  · rintro ⟨w,hw,he⟩
    have hw' : (j.vertex (G.target e)).symm w ∈ B.upwardKernel (G.target e) H := by
      apply (j.upwardKernel_iff _ _ _).mp
      simpa only [LinearEquiv.apply_symm_apply] using hw
    have he' : r • B.upper e ((j.vertex (G.target e)).symm w)=(j.edge e).symm z := by
      apply (j.edge e).injective
      rw [map_smul,j.upper,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply,he]
    obtain ⟨v,hv,hev⟩ := (h ((j.edge e).symm z)).mpr ⟨_,hw',he'⟩
    refine ⟨j.vertex (G.source e) v,(j.upwardKernel_iff _ _ _).mpr hv,?_⟩
    rw [← j.lower,hev,LinearEquiv.apply_symm_apply]

end KLInvariance.MomentGraph.Sheaf.Iso

end


section

namespace KLInvariance.MomentGraph.Sheaf
open scoped Pointwise
universe ur uv ue
variable {R : Type ur} [CommRing R] [DecompositionMonoid R]
  {V : Type uv} [PartialOrder V] {E : Type ue} [Fintype E]
  (G : OrderedGraph V E) (α : E → R) (c : V)
noncomputable section

/-- A quotient-product equality gives the actual two embedded model images.
The common quotient is the edge module's coefficient ring. -/
 theorem structure_scaledImages (e : E)
    (F : Set (Outgoing (G := G) (G.source e)))
    (H : Set (Outgoing (G := G) (G.target e))) (r : R)
    (hF : (supportedOutgoing G c (G.source e) F : Set (Outgoing (G := G) (G.source e))).Pairwise
      (Function.onFun IsRelPrime (fun a => α a.val)))
    (hH : (supportedOutgoing G c (G.target e) H : Set (Outgoing (G := G) (G.target e))).Pairwise
      (Function.onFun IsRelPrime (fun a => α a.val)))
    (h : Associated
      (algebraMap R (R ⧸ Ideal.span {α e}) (kernelProduct G α c (G.source e) F))
      (algebraMap R (R ⧸ Ideal.span {α e}) (r*kernelProduct G α c (G.target e) H))) :
    (structureSheaf G α c).ScaledImages e F H r := by
  rw [scaledImages_iff,structure_lower_image (G := G) α c e F hF,
    structure_upper_image (G := G) α c e H hH,← mul_smul]
  let S := R ⧸ Ideal.span {α e}
  let : Module S ((structureSheaf G α c).edge e) :=
    inferInstanceAs (Module S (PLift (G.target e ≤ c) → S))
  let : IsScalarTower R S ((structureSheaf G α c).edge e) :=
    inferInstanceAs (IsScalarTower R S (PLift (G.target e ≤ c) → S))
  exact LocalProducts.smul_top_eq_of_map_associated (S := S) h

 theorem structure_scaledImages_of_count (e : E)
    (F : Set (Outgoing (G := G) (G.source e)))
    (H : Set (Outgoing (G := G) (G.target e))) (r : R) (p : R ⧸ Ideal.span {α e}) (k : ℕ)
    (hF : (supportedOutgoing G c (G.source e) F : Set (Outgoing (G := G) (G.source e))).Pairwise
      (Function.onFun IsRelPrime (fun a => α a.val)))
    (hH : (supportedOutgoing G c (G.target e) H : Set (Outgoing (G := G) (G.target e))).Pairwise
      (Function.onFun IsRelPrime (fun a => α a.val)))
    (ha : ∀ i ∈ supportedOutgoing G c (G.source e) F,
      Associated (algebraMap R (R ⧸ Ideal.span {α e}) (α i.val)) p)
    (hb : ∀ i ∈ supportedOutgoing G c (G.target e) H,
      Associated (algebraMap R (R ⧸ Ideal.span {α e}) (α i.val)) p)
    (hr : Associated (algebraMap R (R ⧸ Ideal.span {α e}) r) (p^k))
    (hc : (supportedOutgoing G c (G.source e) F).card=
      (supportedOutgoing G c (G.target e) H).card+k) :
    (structureSheaf G α c).ScaledImages e F H r := by
  apply structure_scaledImages G α c e F H r hF hH
  simpa only [kernelProduct,map_prod,map_mul] using
    LocalProducts.associated_prod_scale _ _ _ _ p _ k ha hb hr hc

end
end KLInvariance.MomentGraph.Sheaf

end


section

namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v us u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {a₀ u b : W} {u' b' : W'}
  (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 theorem scheduledLower_root_ne (e : B.CosetEdge a₀ b)
    (hx : BruhatLE cs u ((e.val.1.val:W)*a₀))
    (f : Outgoing (G := B.cosetGraph a₀ b) e.val.1)
    (hf : f ∈ B.scheduledLower hmin φ e hx) :
    B.edgeRoot f.val.property ≠ B.edgeRoot e.property := by
  intro he
  have hroot : BruhatGraph.root cs 1 b (B.cosetEdgeAmbient a₀ b hmin f.val) =
      BruhatGraph.root cs 1 b (B.cosetEdgeAmbient a₀ b hmin e) := by
    rwa [B.cosetRoot_eq a₀ b hmin f.val,B.cosetRoot_eq a₀ b hmin e]
  have hh : f.val=e := B.cosetEdgeAmbient_injective a₀ b hmin
    (eq_of_label_source_eq cs 1 b (root_injective_on_labels cs 1 b hroot)
      (congrArg (B.cosetAmbient a₀ b) f.property))
  have hff : f=(⟨e,rfl⟩ : Outgoing (G := B.cosetGraph a₀ b) e.val.1) := Subtype.ext hh
  exact B.scheduledLower_self hmin φ e hx (hff ▸ hf)

 theorem outgoingUpper_root_ne (e : B.CosetEdge a₀ b)
    (f : Outgoing (G := B.cosetGraph a₀ b) e.val.2) :
    B.edgeRoot f.val.property ≠ B.edgeRoot e.property := by
  rcases f with ⟨⟨⟨s,t⟩,hst⟩,hs⟩
  change s=e.val.2 at hs
  subst s
  exact (B.edgeRoot_ne_of_path e.property hst).symm

 theorem coset_structure_scaledImages [Fintype (B.CosetEdge a₀ b)]
    (e : B.CosetEdge a₀ b) (hx : BruhatLE cs u ((e.val.1.val:W)*a₀))
    (c : B.CosetVertex a₀ b) :
    (structureSheaf (B.cosetGraph a₀ b) (B.cosetLabel basis a₀ b hmin) c).ScaledImages
      e (B.scheduledLower hmin φ e hx) (B.scheduledUpper hmin φ e hx)
      (algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P)
        (edgeFactorLift cs basis ((e.val.1.val:W)*a₀) (B.edgeRoot e.property))) := by
  classical
  by_cases hyc : e.val.2 ≤ c
  · let α := B.edgeRoot e.property
    obtain ⟨β,hαβ,hβ⟩ : ∃ β : PositiveRoot M cs, α ≠ β ∧ β.val ∈ P := by
      by_cases h : α=B.left
      · exact ⟨B.right,h ▸ B.distinct,B.right_mem⟩
      · exact ⟨B.left,h,B.left_mem⟩
    have hplane : rootPlane α β=P :=
      (rootPlane_eq_of_mem B.left B.right α β B.distinct
        (B.plane_eq.ge (B.edgeRoot_plane e.property)) (B.plane_eq.ge hβ) hαβ).trans B.plane_eq
    apply structure_scaledImages_of_count (B.cosetGraph a₀ b) (B.cosetLabel basis a₀ b hmin) c
      e _ _ _ (B.reducedCosetRoot basis a₀ b hmin e β)
      ((planeWeight ((e.val.1.val:W)*a₀) α P).toNat)
      (B.coset_supported_pairwise basis a₀ b hmin c e.val.1 _)
      (B.coset_supported_pairwise basis a₀ b hmin c e.val.2 _)
    · intro f hf
      exact B.cosetLabel_reduction_associated basis a₀ b hmin e f.val β hplane
        (B.scheduledLower_root_ne hmin φ e hx f (Finset.mem_filter.mp hf).2.1)
    · intro f _
      exact B.cosetLabel_reduction_associated basis a₀ b hmin e f.val β hplane
        (B.outgoingUpper_root_ne e f)
    · exact B.cosetFactor_reduction_associated basis a₀ b hmin e β hαβ hplane
    · exact B.supported_count_difference hmin φ e hx c hyc
  · let := structureSheaf_edge_subsingleton (B.cosetGraph a₀ b)
        (B.cosetLabel basis a₀ b hmin) c e hyc
    intro z
    constructor <;> intro _ <;> exact ⟨0,Submodule.zero_mem _,Subsingleton.elim _ _⟩

end
end KLInvariance.TitsSpace.PlaneBasis

end


section


namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {σ : Type (max us v)} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (a₀ b : W) (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
noncomputable section

 theorem localized_boundary_decomposition :
    ∃ C : Sheaf.{max us v,v,v,max us v} (R := PlaneRing basis P) (B.cosetGraph a₀ b),
      ModelSum (B.cosetModels basis a₀ b hmin).sheaf Set.univ C ∧
      Nonempty (Iso (B.localizedCoset basis a₀ b hmin
        (boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.forget) C) := by
  let D := boundarySheaf cs 1 b basis (one_bruhat cs b)
  apply exists_modelSumIso (B.cosetModels basis a₀ b hmin)
    (B.localizedCoset basis a₀ b hmin D.sheaf.forget)
  · intro x
    let : Module.Free (MvPolynomial σ ℝ)
        (D.sheaf.forget.vertex ((B.cosetGraphMap a₀ b hmin).vertex x)) :=
      D.free (B.cosetAmbient a₀ b x)
    exact D.sheaf.forget.baseChange_vertex_free (PlaneRing basis P) _
  · intro x
    let : Module.Finite (MvPolynomial σ ℝ)
        (D.sheaf.forget.vertex ((B.cosetGraphMap a₀ b hmin).vertex x)) :=
      (D.sheaf.vertex (B.cosetAmbient a₀ b x)).finite
    exact D.sheaf.forget.baseChange_vertex_finite (PlaneRing basis P) _
  · exact B.localizedCoset_quotient basis a₀ b hmin D.sheaf.forget D.quotient
  · exact B.localizedCoset_flabby basis a₀ b hmin D.sheaf.forget D.quotient D.flabby.flabby
  · exact B.localizedCoset_generated basis a₀ b hmin D.sheaf.forget D.generated

end
end KLInvariance.TitsSpace.PlaneBasis

end


section


namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v us u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {σ : Type (max us v)} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {a₀ u b : W} {u' b' : W'}
  (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 theorem localized_boundary_scaledImages (e : B.CosetEdge a₀ b)
    (hx : BruhatLE cs u ((e.val.1.val:W)*a₀)) :
    (B.localizedCoset basis a₀ b hmin
      (boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.forget).ScaledImages
      e (B.scheduledLower hmin φ e hx) (B.scheduledUpper hmin φ e hx)
      (algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P)
        (edgeFactorLift cs basis ((e.val.1.val:W)*a₀) (B.edgeRoot e.property))) := by
  classical
  let := Fintype.ofFinite (B.CosetVertex a₀ b)
  let : Finite (B.CosetEdge a₀ b) := Finite.of_injective
    (fun e : B.CosetEdge a₀ b => e.val) Subtype.val_injective
  let := Fintype.ofFinite (B.CosetEdge a₀ b)
  obtain ⟨C,hC,⟨j⟩⟩ := B.localized_boundary_decomposition basis a₀ b hmin
  apply j.symm.scaledImages
  apply hC.scaledImages
  intro c _
  exact B.coset_structure_scaledImages basis hmin φ e hx c

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

/-! Flat scalar extension of actual embedded kernel and image modules. -/
namespace KLInvariance.FlatSubmodule
open TensorProduct
universe ur us um un
variable {R : Type ur} [CommRing R] (S : Type us) [CommRing S] [Algebra R S]
  {M : Type um} [AddCommGroup M] [Module R M]
  {N : Type un} [AddCommGroup N] [Module R N]

 theorem baseChange_ker [Module.Flat R S] (f : M →ₗ[R] N) :
    (LinearMap.ker f).baseChange S = LinearMap.ker (f.baseChange S) := by
  ext z
  exact (Module.Flat.lTensor_exact S f.exact_subtype_ker_map z).symm

 theorem baseChange_map (p : Submodule R M) (f : M →ₗ[R] N) :
    (p.map f).baseChange S = (p.baseChange S).map (f.baseChange S) := by
  apply le_antisymm
  · rintro z ⟨k,rfl⟩
    induction k using TensorProduct.inductionOn with
    | tmul s x =>
      obtain ⟨m,hm,hx⟩ := x.property
      refine ⟨s ⊗ₜ m,Submodule.tmul_mem_baseChange_of_mem s hm,?_⟩
      change s ⊗ₜ[R] f m = s ⊗ₜ[R] (x : N)
      rw [hx]
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  · rintro z ⟨w,⟨k,hk⟩,rfl⟩
    subst w
    induction k using TensorProduct.inductionOn with
    | tmul s x =>
      exact Submodule.tmul_mem_baseChange_of_mem s (show f x ∈ p.map f from ⟨x,x.property,rfl⟩)
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy

end KLInvariance.FlatSubmodule

end


section

namespace KLInvariance.MomentGraph.Sheaf
open TensorProduct
universe ur us uv ue um
variable {R : Type ur} [CommRing R] (S : Type us) [CommRing S] [Algebra R S]
  {V : Type uv} [PartialOrder V] {E : Type ue} {G : OrderedGraph V E}
  (B : Sheaf.{ur,uv,ue,um} (R := R) G)
noncomputable section

 def kernelConstraint (x : V) (F : Set (Outgoing (G := G) x)) :
    B.vertex x →ₗ[R] (∀ e : F, B.edge e.val.val) :=
  LinearMap.pi (fun e => (LinearMap.proj e.val).comp (B.stalkMap x))

 theorem ker_kernelConstraint (x : V) (F : Set (Outgoing (G := G) x)) :
    LinearMap.ker (B.kernelConstraint x F) = B.upwardKernel x F := by
  ext v
  constructor
  · intro h e he
    exact congrFun (LinearMap.mem_ker.mp h) ⟨e,he⟩
  · intro h
    exact LinearMap.mem_ker.mpr (funext fun e => h e.val e.property)

 theorem kernelConstraint_tensor (x : V) (F : Set (Outgoing (G := G) x))
    (z : S ⊗[R] B.vertex x) :
    (B.baseChange S).kernelConstraint x F z =
      TensorProduct.piRightHom R S S (fun e : F => B.edge e.val.val)
        ((B.kernelConstraint x F).baseChange S z) := by
  let k : (S ⊗[R] B.vertex x) →ₗ[S] (∀ e : F, S ⊗[R] B.edge e.val.val) :=
    (B.baseChange S).kernelConstraint x F
  change k z = _
  induction z using TensorProduct.inductionOn with
  | tmul s v =>
    funext e
    rcases e with ⟨⟨e,he⟩,heF⟩
    subst x
    rfl
  | add z t hz ht =>
    simp only [map_add,hz,ht]

 theorem baseChange_upwardKernel [Finite E] [Module.Flat R S]
    (x : V) (F : Set (Outgoing (G := G) x)) :
    (B.upwardKernel x F).baseChange S = (B.baseChange S).upwardKernel x F := by
  classical
  let := Fintype.ofFinite E
  rw [← B.ker_kernelConstraint x F,FlatSubmodule.baseChange_ker,
    ← (B.baseChange S).ker_kernelConstraint x F]
  ext z
  change (B.kernelConstraint x F).baseChange S z = 0 ↔
    (B.baseChange S).kernelConstraint x F z = 0
  rw [B.kernelConstraint_tensor S]
  exact ((TensorProduct.piRight R S S (fun e : F => B.edge e.val.val)).map_eq_zero_iff).symm

 theorem baseChange_lowerImage [Finite E] [Module.Flat R S]
    (e : E) (F : Set (Outgoing (G := G) (G.source e))) :
    ((B.upwardKernel (G.source e) F).map (B.lower e)).baseChange S =
      ((B.baseChange S).upwardKernel (G.source e) F).map ((B.baseChange S).lower e) := by
  rw [FlatSubmodule.baseChange_map,B.baseChange_upwardKernel S]
  rfl

 theorem baseChange_upperImage [Finite E] [Module.Flat R S]
    (e : E) (F : Set (Outgoing (G := G) (G.target e))) :
    ((B.upwardKernel (G.target e) F).map (B.upper e)).baseChange S =
      ((B.baseChange S).upwardKernel (G.target e) F).map ((B.baseChange S).upper e) := by
  rw [FlatSubmodule.baseChange_map,B.baseChange_upwardKernel S]
  rfl

end
end KLInvariance.MomentGraph.Sheaf

end


section

namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v us um u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
  {a₀ b : W}
  (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
noncomputable section

 theorem localizedCoset_kernel
    (C : Sheaf.{us,v,v,um} (R := MvPolynomial σ ℝ) (graph cs 1 b))
    (hq : C.UpperQuotient (polynomialLabel cs 1 b basis))
    (x : B.CosetVertex a₀ b) (T : Set (Edge cs 1 b)) :
    (B.localizedCoset basis a₀ b hmin C).upwardKernel x
      {e | B.cosetEdgeAmbient a₀ b hmin e.val ∈ T} =
    (C.baseChange (PlaneRing basis P)).upwardKernel (B.cosetAmbient a₀ b x) {e | e.val ∈ T} := by
  apply (C.baseChange (PlaneRing basis P)).pullback_kernel (B.cosetGraphMap a₀ b hmin) x T
    {e | label cs 1 b e ∈ planeSubgroup M cs P}
  · intro e he
    exact (C.baseChange (PlaneRing basis P)).edge_subsingleton_of_unit _
      (C.baseChange_upperQuotient (PlaneRing basis P) _ hq) e
      ((polynomialLabel_unit_iff (P := P) basis b e).mpr he)
  · intro e he hx
    exact B.coset_lift_live a₀ b hmin e he x hx

end

variable {σ : Type (max us v)} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u : W} {u' b' : W'}
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 theorem ambient_boundary_scaledImages (e : B.CosetEdge a₀ b)
    (hx : BruhatLE cs u ((e.val.1.val:W)*a₀)) :
    let D := (boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.forget
    let T := ambientLater φ (B.mappedCosetRoot hmin φ e hx)
    (D.baseChange (PlaneRing basis P)).ScaledImages (B.cosetEdgeAmbient a₀ b hmin e)
      {f | f.val ∈ T} {f | f.val ∈ T}
      (algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P)
        (edgeFactorLift cs basis ((e.val.1.val:W)*a₀) (B.edgeRoot e.property))) := by
  let D := boundarySheaf cs 1 b basis (one_bruhat cs b)
  have h := B.localized_boundary_scaledImages basis hmin φ e hx
  dsimp only
  intro z
  have hh := h z
  change (∃ v ∈ (B.localizedCoset basis a₀ b hmin D.sheaf.forget).upwardKernel e.val.1
      (B.scheduledOutgoing hmin φ _ e.val.1 hx), _) ↔
    ∃ w ∈ (B.localizedCoset basis a₀ b hmin D.sheaf.forget).upwardKernel e.val.2
      (B.scheduledOutgoing hmin φ _ e.val.2 (B.cosetEdge_target_upper hmin e hx)), _ at hh
  rw [B.scheduledOutgoing_eq hmin φ,B.scheduledOutgoing_eq hmin φ,
    B.localizedCoset_kernel basis hmin D.sheaf.forget D.quotient,
    B.localizedCoset_kernel basis hmin D.sheaf.forget D.quotient] at hh
  exact hh

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

/-! The local embedded image identity at every actual root-plane prime.
The edge is arbitrary in [1,b], with source in the comparison interval. -/
namespace KLInvariance.BruhatGraph
open Module TitsSpace MomentGraph MomentGraph.Sheaf
universe u v us u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {σ : Type (max us v)} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'}
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 theorem boundary_plane_scaledImages (e : Edge cs 1 b)
    (hx : BruhatLE cs u (source cs 1 b e).val)
    (β : PositiveRoot M cs) (hβ : root cs 1 b e ≠ β) :
    let P := rootPlane (root cs 1 b e) β
    let D := (boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.forget
    let T := ambientLater φ (mappedEdgeRoot φ e hx)
    (D.baseChange (PlaneRing basis P)).ScaledImages e {f | f.val ∈ T} {f | f.val ∈ T}
      (algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P)
        (edgeFactorLift cs basis (source cs 1 b e).val (root cs 1 b e))) := by
  classical
  let P := rootPlane (root cs 1 b e) β
  let B := (nonempty_planeBasis (root cs 1 b e) β hβ).some
  obtain ⟨a₀,hmin,d,hd⟩ := B.exists_coset_edge e (Submodule.subset_span (by simp))
  have hdx : BruhatLE cs u ((d.val.1.val:W)*a₀) := by
    change BruhatLE cs u (source cs 1 b (B.cosetEdgeAmbient a₀ b hmin d)).val
    rwa [hd]
  have h := B.ambient_boundary_scaledImages hmin basis φ d hdx
  dsimp only at h ⊢
  rw [B.mappedCosetRoot_eq hmin φ d hdx,
    show B.edgeRoot d.property=root cs 1 b (B.cosetEdgeAmbient a₀ b hmin d) from
      (B.cosetRoot_eq a₀ b hmin d).symm] at h
  change ((boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.forget.baseChange
    (PlaneRing basis P)).ScaledImages (B.cosetEdgeAmbient a₀ b hmin d)
    {f | f.val ∈ ambientLater φ (mappedEdgeRoot φ (B.cosetEdgeAmbient a₀ b hmin d) hdx)}
    {f | f.val ∈ ambientLater φ (mappedEdgeRoot φ (B.cosetEdgeAmbient a₀ b hmin d) hdx)}
    (algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P)
      (edgeFactorLift cs basis (source cs 1 b (B.cosetEdgeAmbient a₀ b hmin d)).val
        (root cs 1 b (B.cosetEdgeAmbient a₀ b hmin d)))) at h
  have h' := h
  simp only [hd] at h'
  exact Eq.mp (congrArg (fun z : Edge cs 1 b =>
    ((boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.forget.baseChange
      (PlaneRing basis P)).ScaledImages z
      {f | f.val ∈ ambientLater φ (mappedEdgeRoot φ e hx)}
      {f | f.val ∈ ambientLater φ (mappedEdgeRoot φ e hx)}
      (algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P)
        (edgeFactorLift cs basis (source cs 1 b e).val (root cs 1 b e)))) hd) h'

end
end KLInvariance.BruhatGraph

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace EdgeAlgebra
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 abbrev EdgeRing (a : PositiveRoot M cs) :=
   MvPolynomial σ ℝ ⧸ Ideal.span {polynomialRoot cs basis a}

 def edgeRingEquiv (a : PositiveRoot M cs) : EdgeRing cs basis a ≃ₐ[ℝ] EdgeCoefficient a :=
   (Ideal.quotientEquivAlg (rootIdeal (k := ℝ) (embed M a.val))
     (Ideal.span {polynomialRoot cs basis a}) (SymmetricAlgebra.equivMvPolynomial basis)
     (by simp only [rootIdeal,Ideal.map_span,Set.image_singleton,polynomialRoot]; rfl)).symm

 @[simp] theorem edgeRingEquiv_root (a β : PositiveRoot M cs) :
    edgeRingEquiv cs basis a (Ideal.Quotient.mk _ (polynomialRoot cs basis β)) =
      Ideal.Quotient.mk _ (SymmetricAlgebra.ι ℝ (Extended M) (embed M β.val)) := by
  apply (edgeRingEquiv cs basis a).symm.injective
  simp only [AlgEquiv.symm_apply_apply]
  rfl

 instance edgeRing_isDomain (a : PositiveRoot M cs) : IsDomain (EdgeRing cs basis a) := by
   let : (Ideal.span {polynomialRoot cs basis a}).IsPrime :=
     Ideal.isPrime_span_singleton_of_prime (polynomialRoot_prime cs basis a)
   infer_instance

 instance edgeRing_ufm (a : PositiveRoot M cs) : UniqueFactorizationMonoid (EdgeRing cs basis a) :=
   ((edgeRingEquiv cs basis a).trans (edgePolynomial a)).toMulEquiv.symm.uniqueFactorizationMonoid inferInstance

 theorem reducedPolynomialRoot_prime (a β : PositiveRoot M cs) (hne : a≠β) :
    Prime (Ideal.Quotient.mk (Ideal.span {polynomialRoot cs basis a})
      (polynomialRoot cs basis β)) := by
  apply (MulEquiv.prime_iff (edgeRingEquiv cs basis a)).mp
  rw [edgeRingEquiv_root]
  exact reducedRoot_prime _ _ (embed_not_rootLine a β hne.symm)

 theorem planePrime_span (a β : PositiveRoot M cs) :
    planePrime basis (rootPlane a β) =
      Ideal.span {polynomialRoot cs basis a,polynomialRoot cs basis β} := by
  simp only [planePrime,rootPlane,Submodule.map_span,Set.image_insert_eq,
    Set.image_singleton,SymmetricPlaneIdeal.ideal_span_eq,Ideal.map_span,
    polynomialRoot,embedLinear]
  rfl

end
end KLInvariance.BruhatGraph

end


section

/-! The scalar quotient of an actual finite free presentation is free over
its quotient coefficient ring. There is no quotient-freeness hypothesis. -/
namespace KLInvariance.ScalarQuotient
open Module
universe ur um un ui
variable {R : Type ur} [CommRing R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {N : Type un} [AddCommGroup N] [Module R N]
  {ι : Type ui} [Fintype ι]
noncomputable section

 def coordinateReduction (b : Basis ι R M) (a : R) :
    M →ₗ[R] (ι → R ⧸ Ideal.span {a}) :=
  (LinearMap.pi fun i => (Ideal.span ({a} : Set R)).mkQ.comp
    ((LinearMap.proj i).comp b.equivFun.toLinearMap))

 theorem coordinateReduction_surjective (b : Basis ι R M) (a : R) :
    Function.Surjective (coordinateReduction b a) := by
  intro v
  choose w hw using fun i => Ideal.Quotient.mk_surjective (v i)
  exact ⟨b.equivFun.symm w,funext fun i => by
    change Ideal.Quotient.mk (Ideal.span {a}) (b.equivFun (b.equivFun.symm w) i)=v i
    simpa only [LinearEquiv.apply_symm_apply] using hw i⟩

 theorem coordinateReduction_kernel (b : Basis ι R M) (a : R) (v : M) :
    coordinateReduction b a v=0 ↔ ∃ w, v=a • w := by
  have h : (∃ w, v=a • w) ↔ ∀ i, a ∣ b.equivFun v i :=
    (exists_congr fun _ => eq_comm).trans (FiniteFreeScalar.exists_smul_iff b a v)
  rw [h]
  simp only [coordinateReduction,LinearMap.pi_apply,LinearMap.comp_apply,
    LinearMap.proj_apply,LinearEquiv.coe_coe,funext_iff,Pi.zero_apply]
  exact forall_congr' fun i => (Ideal.Quotient.eq_zero_iff_mem).trans Ideal.mem_span_singleton

 theorem free_of_scalar_presentation (a : R)
    [Module (R ⧸ Ideal.span {a}) N] [IsScalarTower R (R ⧸ Ideal.span {a}) N]
    (b : Basis ι R M) (q : M →ₗ[R] N) (hq : Function.Surjective q)
    (hk : ∀ v, q v=0 ↔ ∃ w, v=a • w) :
    Module.Free (R ⧸ Ideal.span {a}) N := by
  obtain ⟨j,_⟩ := QuotientEdge.exists_scalar_iso q (coordinateReduction b a) a
    hq (coordinateReduction_surjective b a) hk (coordinateReduction_kernel b a)
    (LinearEquiv.refl R M)
  let k : N ≃ₗ[R ⧸ Ideal.span {a}] (ι → R ⧸ Ideal.span {a}) :=
    { j.toAddEquiv with
      map_smul' := by
        intro c v
        obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective c
        change j ((algebraMap R (R ⧸ Ideal.span {a}) r) • v) =
          (algebraMap R (R ⧸ Ideal.span {a}) r) • j v
        simpa only [algebraMap_smul] using j.map_smul r v }
  exact Module.Free.of_equiv k.symm

 def submodule (a : R) [Module (R ⧸ Ideal.span {a}) N]
    [IsScalarTower R (R ⧸ Ideal.span {a}) N] (S : Submodule R N) :
    Submodule (R ⧸ Ideal.span {a}) N where
  carrier := S
  add_mem' := S.add_mem
  zero_mem' := S.zero_mem
  smul_mem' c v hv := by
    obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective c
    change (algebraMap R (R ⧸ Ideal.span {a}) r) • v ∈ S
    simpa only [algebraMap_smul] using S.smul_mem r hv

 theorem saturated_image_free (a : R)
    [Module (R ⧸ Ideal.span {a}) N] [IsScalarTower R (R ⧸ Ideal.span {a}) N]
    (q : M →ₗ[R] N) (hk : ∀ v, q v=0 ↔ ∃ w, v=a • w)
    (L : Submodule R M) [Module.Free R L] [Module.Finite R L]
    (hsat : ∀ v, a • v ∈ L → v ∈ L) :
    Module.Free (R ⧸ Ideal.span {a}) (submodule a (L.map q)) := by
  let f : L →ₗ[R] submodule a (L.map q) :=
    (q.comp L.subtype).codRestrict ((submodule a (L.map q)).restrictScalars R)
      (fun v => ⟨v.val,v.property,rfl⟩)
  apply free_of_scalar_presentation a (Module.Free.chooseBasis R L) f
  · rintro ⟨v,hv⟩
    obtain ⟨w,hw,rfl⟩ := hv
    exact ⟨⟨w,hw⟩,rfl⟩
  · intro v
    constructor
    · intro hv
      obtain ⟨w,hw⟩ := (hk v.val).mp (congrArg Subtype.val hv)
      exact ⟨⟨w,hsat w (hw ▸ v.property)⟩,Subtype.ext hw⟩
    · rintro ⟨w,rfl⟩
      exact Subtype.ext ((hk _).mpr ⟨w.val,rfl⟩)

end
end KLInvariance.ScalarQuotient

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)
noncomputable section

omit [Fintype σ] in
 theorem edgeTorsion (e : Edge cs u b) :
    Module.IsTorsionBy (MvPolynomial σ ℝ) (B.sheaf.edge e) (polynomialRoot cs basis (root cs u b e)) :=
   fun v => GradedSheaf.UpperQuotient.annihilates B.sheaf B.quotient e v

 @[instance_reducible] def edgeModule (e : Edge cs u b) :
    Module (EdgeRing cs basis (root cs u b e)) (B.sheaf.edge e) :=
   (edgeTorsion cs u b basis hub B e).module

omit [Fintype σ] in
 theorem edgeModule_tower (e : Edge cs u b) :
    let _ := edgeModule cs u b basis hub B e
    IsScalarTower (MvPolynomial σ ℝ) (EdgeRing cs basis (root cs u b e)) (B.sheaf.edge e) := by
   dsimp only [edgeModule,Module.IsTorsionBy.module]
   exact Module.IsTorsionBySet.isScalarTower _

omit [Fintype σ] in
 theorem edgeModule_free (e : Edge cs u b) :
    let _ := edgeModule cs u b basis hub B e
    Module.Free (EdgeRing cs basis (root cs u b e)) (B.sheaf.edge e) := by
   let _ := edgeModule cs u b basis hub B e
   let _ := edgeModule_tower cs u b basis hub B e
   let _ := B.free (target cs u b e)
   exact ScalarQuotient.free_of_scalar_presentation _
     (Module.Free.chooseBasis (MvPolynomial σ ℝ) (B.sheaf.vertex (target cs u b e)))
     (B.sheaf.upper e).map (B.quotient e).1 (B.quotient e).2

 theorem upperImage_free (e : Edge cs u b)
    (F : Set (Sheaf.Outgoing (G := graph cs u b) (target cs u b e)))
    [Module.Free (MvPolynomial σ ℝ) (B.sheaf.upwardSubmodule (target cs u b e) F)] :
    let _ := edgeModule cs u b basis hub B e
    let _ := edgeModule_tower cs u b basis hub B e
    Module.Free (EdgeRing cs basis (root cs u b e))
      (ScalarQuotient.submodule (polynomialRoot cs basis (root cs u b e))
        ((B.sheaf.upwardSubmodule (target cs u b e) F).map (B.sheaf.upper e).map)) := by
   let _ := edgeModule cs u b basis hub B e
   let _ := edgeModule_tower cs u b basis hub B e
   let _ : Module.Finite (MvPolynomial σ ℝ) (B.sheaf.vertex (target cs u b e)) :=
     (B.sheaf.vertex (target cs u b e)).finite
   let hfinite : Module.Finite (MvPolynomial σ ℝ) (B.sheaf.upwardSubmodule (target cs u b e) F) :=
     Module.Finite.of_injective (B.sheaf.upwardSubmodule (target cs u b e) F).subtype Subtype.val_injective
   dsimp only
   let hfree := (inferInstance : Module.Free (MvPolynomial σ ℝ) (B.sheaf.upwardSubmodule (target cs u b e) F))
   exact @ScalarQuotient.saturated_image_free (MvPolynomial σ ℝ) _
     (B.sheaf.vertex (target cs u b e)) _ _ (B.sheaf.edge e) _ _
     (polynomialRoot cs basis (root cs u b e)) _ _
     (B.sheaf.upper e).map (B.quotient e).2 (B.sheaf.upwardSubmodule (target cs u b e) F)
     hfree hfinite (by

     exact B.sheaf.upwardSubmodule_saturated (target cs u b e) F _
            (fun f _ => incoming_label_regular_outgoing cs u b basis hub B e f.val f.property))

end
end KLInvariance.BruhatGraph

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace EdgeAlgebra
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem reducedRoot_dvd_iff_mem_plane (a β : PositiveRoot M cs) (z : MvPolynomial σ ℝ) :
    Ideal.Quotient.mk (Ideal.span {polynomialRoot cs basis a}) (polynomialRoot cs basis β) ∣
      Ideal.Quotient.mk (Ideal.span {polynomialRoot cs basis a}) z ↔
    z ∈ planePrime basis (rootPlane a β) := by
  rw [← Ideal.mem_span_singleton]
  change z ∈ Ideal.comap (Ideal.Quotient.mk (Ideal.span {polynomialRoot cs basis a}))
    (Ideal.span {Ideal.Quotient.mk (Ideal.span {polynomialRoot cs basis a})
      (polynomialRoot cs basis β)}) ↔ _
  have hi : Ideal.map (Ideal.Quotient.mk (Ideal.span {polynomialRoot cs basis a}))
      (Ideal.span {polynomialRoot cs basis β}) =
      Ideal.span {Ideal.Quotient.mk (Ideal.span {polynomialRoot cs basis a})
        (polynomialRoot cs basis β)} := by rw [Ideal.map_span,Set.image_singleton]
  rw [← hi,Ideal.comap_map_quotientMk,← Ideal.span_union,Set.singleton_union,planePrime_span]

 theorem reducedFactor_ne_zero (x : W) (a : PositiveRoot M cs) :
    Ideal.Quotient.mk (Ideal.span {polynomialRoot cs basis a})
      (edgeFactorLift cs basis x a) ≠ 0 := by
  simpa only [ne_eq,Ideal.Quotient.eq_zero_iff_mem,Ideal.mem_span_singleton] using
    edgeFactorLift_not_dvd cs basis x a

 theorem prime_dvd_reducedFactor (x : W) (a : PositiveRoot M cs)
    (p : EdgeRing cs basis a) (hp : Prime p)
    (hd : p ∣ Ideal.Quotient.mk _ (edgeFactorLift cs basis x a)) :
    ∃ β : PositiveRoot M cs, a ≠ β ∧
      Associated p (Ideal.Quotient.mk _ (polynomialRoot cs basis β)) := by
  classical
  simp only [edgeFactorLift,map_prod,map_pow] at hd
  obtain ⟨P,_,hP⟩ := (hp.dvd_finsetProd_iff _).mp hd
  exact ⟨planeRoot x a P,(planeRoot_ne x a P).symm,
    hp.irreducible.associated_of_dvd
      (reducedPolynomialRoot_prime cs basis a _ (planeRoot_ne x a P).symm).irreducible
      (hp.dvd_of_dvd_pow hP)⟩

end
end KLInvariance.BruhatGraph

end


section

namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue um
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} [Finite E] {G : OrderedGraph V E}
  (B : Sheaf.{ur,uv,ue,um} (R := R) G)
noncomputable section
open scoped Classical

 def outgoingLabelProduct (α : E → R) (x : V) (F : Set (Outgoing (G := G) x)) : R :=
   ∏ f ∈ F.toFinite.toFinset, α f.val

 theorem outgoingLabelProduct_dvd (α : E → R) (x : V) (F : Set (Outgoing (G := G) x))
    (f : Outgoing (G := G) x) (hf : f ∈ F) : α f.val ∣ outgoingLabelProduct α x F := by
   exact Finset.dvd_prod_of_mem _ (F.toFinite.mem_toFinset.mpr hf)

 theorem outgoingLabelProduct_smul_mem (α : E → R) (hα : ∀ e (v : B.edge e), α e • v=0)
    (x : V) (F : Set (Outgoing (G := G) x)) (v : B.vertex x) :
    outgoingLabelProduct α x F • v ∈ B.upwardKernel x F := by
   intro f hf
   obtain ⟨r,hr⟩ := outgoingLabelProduct_dvd α x F f hf
   rw [map_smul,hr,mul_comm,mul_smul]
   have h := hα f.val (B.stalkMap x v f)
   change r • (α f.val • B.stalkMap x v f) = 0
   rw [h,smul_zero]

 theorem outgoingLabelProduct_smul_upperImage (α : E → R) (hα : ∀ e (v : B.edge e), α e • v=0)
    (e : E) (hq : Function.Surjective (B.upper e))
    (F : Set (Outgoing (G := G) (G.target e))) (v : B.edge e) :
    outgoingLabelProduct α (G.target e) F • v ∈
      (B.upwardKernel (G.target e) F).map (B.upper e) := by
   obtain ⟨w,rfl⟩ := hq v
   exact ⟨_,B.outgoingLabelProduct_smul_mem α hα _ F w,(B.upper e).map_smul _ w⟩

end
end KLInvariance.MomentGraph.Sheaf

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace MomentGraph MomentGraph.Sheaf
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem incoming_root_ne_outgoing (e f : Edge cs u b)
    (h : source cs u b f=target cs u b e) : root cs u b e ≠ root cs u b f := by
  intro hr
  exact source_ne_target_of_label_eq cs u b (root_injective_on_labels cs u b hr.symm) h

 theorem reducedKernelProduct_ne_zero (e : Edge cs u b)
    (F : Set (Outgoing (G := graph cs u b) (target cs u b e))) :
    Ideal.Quotient.mk (Ideal.span {polynomialRoot cs basis (root cs u b e)})
      (outgoingLabelProduct (polynomialLabel cs u b basis) (target cs u b e) F) ≠ 0 := by
  classical
  rw [outgoingLabelProduct,map_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro f _
  exact (reducedPolynomialRoot_prime cs basis _ _
    (incoming_root_ne_outgoing cs u b e f.val f.property)).ne_zero

 theorem prime_dvd_reducedKernelProduct (e : Edge cs u b)
    (F : Set (Outgoing (G := graph cs u b) (target cs u b e)))
    (p : EdgeRing cs basis (root cs u b e)) (hp : Prime p)
    (hd : p ∣ Ideal.Quotient.mk _
      (outgoingLabelProduct (polynomialLabel cs u b basis) (target cs u b e) F)) :
    ∃ β : PositiveRoot M cs, root cs u b e ≠ β ∧
      Associated p (Ideal.Quotient.mk _ (polynomialRoot cs basis β)) := by
  classical
  rw [outgoingLabelProduct,map_prod] at hd
  obtain ⟨f,_,hf⟩ := (hp.dvd_finsetProd_iff _).mp hd
  exact ⟨root cs u b f.val,incoming_root_ne_outgoing cs u b e f.val f.property,
    hp.irreducible.associated_of_dvd
      (reducedPolynomialRoot_prime cs basis _ _
        (incoming_root_ne_outgoing cs u b e f.val f.property)).irreducible hf⟩

end
end KLInvariance.BruhatGraph

end


section

namespace KLInvariance.ScalarQuotient
universe ur un
variable {R : Type ur} [CommRing R]
  {N : Type un} [AddCommGroup N] [Module R N]
noncomputable section

 theorem scalarImage (a z : R)
    [Module (R ⧸ Ideal.span {a}) N] [IsScalarTower R (R ⧸ Ideal.span {a}) N]
    (S : Submodule R N) :
    submodule a (S.map (LinearMap.lsmul R N z)) =
      (submodule a S).map
        (LinearMap.lsmul (R ⧸ Ideal.span {a}) N (Ideal.Quotient.mk _ z)) := by
  ext v
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨w,hw,by simp only [LinearMap.lsmul_apply]; exact algebraMap_smul _ _ w⟩
  · rintro ⟨w,hw,rfl⟩
    exact ⟨w,hw,by simp only [LinearMap.lsmul_apply]; exact (algebraMap_smul _ _ w).symm⟩

 theorem free_scalarImage (a z : R)
    [Module (R ⧸ Ideal.span {a}) N] [IsScalarTower R (R ⧸ Ideal.span {a}) N]
    (S : Submodule R N) [Module.Free (R ⧸ Ideal.span {a}) (submodule a S)]
    (hz : Function.Injective (fun v : N => z • v)) :
    Module.Free (R ⧸ Ideal.span {a}) (submodule a (S.map (LinearMap.lsmul R N z))) := by
  rw [scalarImage]
  apply Module.Free.of_equiv (Submodule.equivMapOfInjective _ ?_ (submodule a S))
  intro v w h
  apply hz
  change (algebraMap R (R ⧸ Ideal.span {a}) z) • v =
    (algebraMap R (R ⧸ Ideal.span {a}) z) • w at h
  simpa only [algebraMap_smul] using h

end
end KLInvariance.ScalarQuotient

end


section

namespace KLInvariance.TensorLocalMembership
open TensorProduct
universe ur us um
variable {R : Type ur} [CommRing R] (S : Type us) [CommRing S] [Algebra R S]
  {M : Type um} [AddCommGroup M] [Module R M]
  (P : Submonoid R) [IsLocalization P S]
noncomputable section

 theorem baseChange_eq_localized (L : Submodule R M) :
    L.baseChange S = L.localized' S P (TensorProduct.mk R S M 1) := by
  rw [Submodule.baseChange_eq_span,Submodule.localized'_eq_span]
  rfl

 theorem denominator (L : Submodule R M) (x : M)
    (hx : 1 ⊗ₜ[R] x ∈ L.baseChange S) :
    ∃ a : P, (a:R) • x ∈ L := by
  rw [baseChange_eq_localized S P L] at hx
  obtain ⟨m,hm,s,hs⟩ := hx
  have he := (IsLocalizedModule.mk'_eq_iff).mp hs
  change (TensorProduct.mk R S M 1) m = (s:R) • (TensorProduct.mk R S M 1) x at he
  rw [← map_smul] at he
  obtain ⟨t,ht⟩ := (IsLocalizedModule.eq_iff_exists P (TensorProduct.mk R S M 1)).mp he
  refine ⟨t*s,?_⟩
  have hh := L.smul_mem (t:R) hm
  change (t:R) • m ∈ L at hh
  change (t:R) • m = (t:R) • ((s:R) • x) at ht
  simpa only [Submonoid.coe_mul,mul_smul,← ht] using hh

end
end KLInvariance.TensorLocalMembership

end


section

namespace KLInvariance.MomentGraph.Sheaf
open TensorProduct
universe ur us uv ue um
variable {R : Type ur} [CommRing R] (S : Type us) [CommRing S] [Algebra R S]
  {V : Type uv} [PartialOrder V] {E : Type ue} [Finite E] {G : OrderedGraph V E}
  (B : Sheaf.{ur,uv,ue,um} (R := R) G)
  (P : Submonoid R) [IsLocalization P S]
noncomputable section

 theorem scaledImages_denominator
    (e : E) (F : Set (Outgoing (G := G) (G.source e)))
    (H : Set (Outgoing (G := G) (G.target e))) (a : R)
    (h : (B.baseChange S).ScaledImages e F H (algebraMap R S a))
    (x : B.edge e) (hx : x ∈ (B.upwardKernel (G.source e) F).map (B.lower e)) :
    ∃ s : P, (s:R) • x ∈ ((B.upwardKernel (G.target e) H).map (B.upper e)).map
      (LinearMap.lsmul R (B.edge e) a) := by
  let _ : Module.Flat R S := IsLocalization.flat S P
  apply TensorLocalMembership.denominator S P _ x
  rw [FlatSubmodule.baseChange_map,B.baseChange_upperImage S]
  have hx' : 1 ⊗ₜ[R] x ∈ ((B.baseChange S).upwardKernel (G.source e) F).map
      ((B.baseChange S).lower e) := by
    rw [← B.baseChange_lowerImage S]
    exact Submodule.tmul_mem_baseChange_of_mem 1 hx
  obtain ⟨v,hv,he⟩ := hx'
  obtain ⟨w,hw,hwx⟩ := (h (1 ⊗ₜ[R] x)).mp ⟨v,hv,he⟩
  refine ⟨(B.baseChange S).upper e w,⟨w,hw,rfl⟩,?_⟩
  change (LinearMap.lsmul R (B.edge e) a).baseChange S ((B.baseChange S).upper e w) = _
  have hg : (LinearMap.lsmul R (B.edge e) a).baseChange S =
      LinearMap.lsmul S (S ⊗[R] B.edge e) (algebraMap R S a) := by
    apply LinearMap.restrictScalars_injective R
    apply TensorProduct.ext'
    intro r v
    change (LinearMap.lsmul R (B.edge e) a).baseChange S (r ⊗ₜ[R] v) =
      (algebraMap R S a) • (r ⊗ₜ[R] v)
    simp only [LinearMap.baseChange_tmul,LinearMap.lsmul_apply,
      algebraMap_smul,TensorProduct.tmul_smul,TensorProduct.smul_tmul']
  rw [hg]
  exact hwx

end
end KLInvariance.MomentGraph.Sheaf

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace
universe u v us un
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem mem_of_plane_denominators (a : PositiveRoot M cs)
    {N : Type un} [AddCommGroup N] [Module (MvPolynomial σ ℝ) N]
    [Module (EdgeRing cs basis a) N] [IsScalarTower (MvPolynomial σ ℝ) (EdgeRing cs basis a) N]
    [Module.IsTorsionFree (EdgeRing cs basis a) N]
    (S : Submodule (MvPolynomial σ ℝ) N)
    [Module.Free (EdgeRing cs basis a) (ScalarQuotient.submodule (polynomialRoot cs basis a) S)]
    (z : N) (c : MvPolynomial σ ℝ)
    (hc : Ideal.Quotient.mk (Ideal.span {polynomialRoot cs basis a}) c ≠ 0)
    (hcz : c • z ∈ S)
    (hprime : ∀ p : EdgeRing cs basis a, Prime p → p ∣ Ideal.Quotient.mk _ c →
      ∃ β : PositiveRoot M cs, a≠β ∧ Associated p (Ideal.Quotient.mk _ (polynomialRoot cs basis β)))
    (hlocal : ∀ β : PositiveRoot M cs, a≠β →
      ∃ s : MvPolynomial σ ℝ, s ∉ planePrime basis (rootPlane a β) ∧ s • z ∈ S) :
    z ∈ S := by
  apply EdgeLattice.mem_of_prime_local_membership
    (ScalarQuotient.submodule (polynomialRoot cs basis a) S) z
  · refine ⟨Ideal.Quotient.mk _ c,hc,?_⟩
    change (algebraMap (MvPolynomial σ ℝ) (EdgeRing cs basis a) c) • z ∈ S
    simpa only [algebraMap_smul] using hcz
  · intro p hp
    by_cases hpc : p ∣ Ideal.Quotient.mk (Ideal.span {polynomialRoot cs basis a}) c
    · obtain ⟨β,hβ,hpβ⟩ := hprime p hp hpc
      obtain ⟨s,hs,hsz⟩ := hlocal β hβ
      refine ⟨Ideal.Quotient.mk _ s,?_,?_⟩
      · rw [hpβ.dvd_iff_dvd_left,reducedRoot_dvd_iff_mem_plane]
        exact hs
      · change (algebraMap (MvPolynomial σ ℝ) (EdgeRing cs basis a) s) • z ∈ S
        simpa only [algebraMap_smul] using hsz
    · refine ⟨Ideal.Quotient.mk _ c,hpc,?_⟩
      change (algebraMap (MvPolynomial σ ℝ) (EdgeRing cs basis a) c) • z ∈ S
      simpa only [algebraMap_smul] using hcz

end
end KLInvariance.BruhatGraph

end


section


namespace KLInvariance.BruhatGraph
open Module TitsSpace MomentGraph MomentGraph.Sheaf
universe u v us u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {σ : Type (max us v)} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'}
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 theorem boundary_edge_image_le (e : Edge cs 1 b)
    (hx : BruhatLE cs u (source cs 1 b e).val)
    [Module.Free (MvPolynomial σ ℝ)
      ((boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.upwardSubmodule
        (target cs 1 b e) {f | f.val ∈ ambientLater φ (mappedEdgeRoot φ e hx)})] :
    let D := (boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.forget
    let T := ambientLater φ (mappedEdgeRoot φ e hx)
    (D.upwardKernel (source cs 1 b e) {f | f.val ∈ T}).map (D.lower e) ≤
      ((D.upwardKernel (target cs 1 b e) {f | f.val ∈ T}).map (D.upper e)).map
        (LinearMap.lsmul (MvPolynomial σ ℝ) (D.edge e)
          (edgeFactorLift cs basis (source cs 1 b e).val (root cs 1 b e))) := by
  classical
  let B := boundarySheaf cs 1 b basis (one_bruhat cs b)
  let D := B.sheaf.forget
  let F : Set (Outgoing (G := graph cs 1 b) (source cs 1 b e)) :=
    {f | f.val ∈ ambientLater φ (mappedEdgeRoot φ e hx)}
  let G : Set (Outgoing (G := graph cs 1 b) (target cs 1 b e)) :=
    {f | f.val ∈ ambientLater φ (mappedEdgeRoot φ e hx)}
  let a := root cs 1 b e
  let f := edgeFactorLift cs basis (source cs 1 b e).val a
  let J := (D.upwardKernel (target cs 1 b e) G).map (D.upper e)
  let S := J.map (LinearMap.lsmul (MvPolynomial σ ℝ) (D.edge e) f)
  let pG := outgoingLabelProduct (polynomialLabel cs 1 b basis) (target cs 1 b e) G
  let _ : Module (EdgeRing cs basis a) (D.edge e) :=
    edgeModule cs 1 b basis (one_bruhat cs b) B e
  let _ : IsScalarTower (MvPolynomial σ ℝ) (EdgeRing cs basis a) (D.edge e) :=
    edgeModule_tower cs 1 b basis (one_bruhat cs b) B e
  let _ : Module.Free (EdgeRing cs basis a) (D.edge e) :=
    edgeModule_free cs 1 b basis (one_bruhat cs b) B e
  let _ : Module.Free (EdgeRing cs basis a)
      (ScalarQuotient.submodule (polynomialRoot cs basis a) J) :=
    upperImage_free cs 1 b basis (one_bruhat cs b) B e G
  let _ : Module.Free (EdgeRing cs basis a) (ScalarQuotient.submodule (polynomialRoot cs basis a) S) :=
    ScalarQuotient.free_scalarImage (polynomialRoot cs basis a) f J
      (edgeFactorLift_regular cs basis 1 b (one_bruhat cs b) B e)
  change (D.upwardKernel (source cs 1 b e) F).map (D.lower e) ≤ S
  intro z hz
  apply mem_of_plane_denominators cs basis a S z (f*pG)
  · rw [map_mul]
    exact mul_ne_zero (reducedFactor_ne_zero cs basis _ a)
      (reducedKernelProduct_ne_zero cs 1 b basis e G)
  · refine ⟨pG • z,?_,?_⟩
    · exact D.outgoingLabelProduct_smul_upperImage (polynomialLabel cs 1 b basis)
        (GradedSheaf.UpperQuotient.annihilates B.sheaf B.quotient) e (B.quotient e).1 G z
    · change f • (pG • z) = (f*pG) • z
      rw [mul_smul]
  · intro p hp hd
    rw [map_mul] at hd
    rcases hp.dvd_mul.mp hd with hf | hG
    · exact prime_dvd_reducedFactor cs basis _ a p hp hf
    · exact prime_dvd_reducedKernelProduct cs 1 b basis e G p hp hG
  · intro β hβ
    obtain ⟨s,hs⟩ := D.scaledImages_denominator (PlaneRing basis (rootPlane a β))
      (planePrime basis (rootPlane a β)).primeCompl e F G f
      (boundary_plane_scaledImages basis φ e hx β hβ) z hz
    exact ⟨s,s.property,hs⟩

end
end KLInvariance.BruhatGraph

end


section


namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph SchedulePaths
universe u v us u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {σ : Type (max us v)} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'} (hub : BruhatLE cs u b)
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 def intervalBoundary := restrictBoundary cs u b basis hub
  (boundarySheaf cs 1 b basis (one_bruhat cs b))

 theorem schedule_edge_image_le {e : Edge cs u b} {q : List (Edge cs u b)}
    (hq : e::q <:+ chronologicalSchedule φ)
    [hF : Module.Free (Coefficient (σ := σ))
      ((intervalBoundary basis hub).sheaf.upwardSubmodule (target cs u b e)
        (remainingConditions cs u b q (target cs u b e)))] :
    (intervalBoundary basis hub).sheaf.lowerImage e
        (remainingConditions cs u b q (source cs u b e)) ≤
      ((intervalBoundary basis hub).sheaf.upperImage e
        (remainingConditions cs u b q (target cs u b e))).map
        (edgeFactorMap cs basis u b hub (intervalBoundary basis hub) e) := by
  let B := boundarySheaf cs 1 b basis (one_bruhat cs b)
  let a := (upperInclusion cs u b).edge e
  let r := AdaptedDyer.rootLabel cs' (transportedEdge φ e)
  have hr : mappedEdgeRoot φ a (source cs u b e).property.1 = r := rfl
  have hk (x : Interval cs u b) :=
    restrictBoundary_kernel cs u b basis hub B x (ambientLater φ r)
  have hs : (intervalBoundary basis hub).sheaf.upwardSubmodule (source cs u b e)
      (remainingConditions cs u b q (source cs u b e)) =
      B.sheaf.upwardSubmodule (source cs 1 b a) {f | f.val ∈ ambientLater φ r} :=
    (congrArg ((intervalBoundary basis hub).sheaf.upwardSubmodule (source cs u b e))
      (remainingConditions_source_ambient φ hq)).trans (hk (source cs u b e))
  have ht : (intervalBoundary basis hub).sheaf.upwardSubmodule (target cs u b e)
      (remainingConditions cs u b q (target cs u b e)) =
      B.sheaf.upwardSubmodule (target cs 1 b a) {f | f.val ∈ ambientLater φ r} :=
    (congrArg ((intervalBoundary basis hub).sheaf.upwardSubmodule (target cs u b e))
      (remainingConditions_target_ambient φ hq)).trans (hk (target cs u b e))
  have hfree : Module.Free (Coefficient (σ := σ))
      (B.sheaf.upwardSubmodule (target cs 1 b a) {f | f.val ∈ ambientLater φ r}) :=
    (congrArg (fun N : Submodule (Coefficient (σ := σ)) (B.sheaf.vertex (target cs 1 b a)) =>
      Module.Free (Coefficient (σ := σ)) N) ht).mp hF
  let hf : Module.Free (Coefficient (σ := σ))
      (B.sheaf.upwardSubmodule (target cs 1 b a)
        {f | f.val ∈ ambientLater φ (mappedEdgeRoot φ a (source cs u b e).property.1)}) := by
    rw [hr]
    exact hfree
  have h := boundary_edge_image_le basis φ a (source cs u b e).property.1
  dsimp only at h
  rw [hr] at h
  have hs' := congrArg (fun N : Submodule (Coefficient (σ := σ)) (B.sheaf.vertex (source cs 1 b a)) =>
    N.map (B.sheaf.lower a).map) hs
  have ht' := congrArg (fun N : Submodule (Coefficient (σ := σ)) (B.sheaf.vertex (target cs 1 b a)) =>
    (N.map (B.sheaf.upper a).map).map
      (edgeFactorMap cs basis u b hub (intervalBoundary basis hub) e)) ht
  exact hs'.le.trans (h.trans ht'.symm.le)

 theorem schedule_comparison_of_upper_freeness
    (hfree : ∀ e q, e::q <:+ chronologicalSchedule φ →
      Module.Free (Coefficient (σ := σ))
        ((intervalBoundary basis hub).sheaf.upwardSubmodule (target cs u b e)
          (remainingConditions cs u b q (target cs u b e))))
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    scheduleState cs u b basis hub (intervalBoundary basis hub) t [] ≤
      dispatch (source cs u b) (target cs u b) (t⁻¹-t)
        (scheduleState cs u b basis hub (intervalBoundary basis hub) t (chronologicalSchedule φ))
        (transportedSchedule φ) := by
  have h := scheduleState_le cs u b basis hub (intervalBoundary basis hub) (chronologicalSchedule φ)
    (fun e q hq => by
      let _ := hfree e q hq
      exact schedule_edge_image_le basis hub φ hq) ht ht1
  simpa only [chronologicalSchedule,List.reverse_reverse] using h

end
end KLInvariance.BruhatGraph

end


section


namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph SchedulePaths
universe u v u' v' us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {σ : Type (max us v)} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'} (hub : BruhatLE cs u b)
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 theorem schedule_final_of_character
    (hc : StalkCharacterObligation cs 1 b basis (one_bruhat cs b))
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) (x : Interval cs u b) :
    scheduleState cs u b basis hub (intervalBoundary basis hub) t [] x =
      scaledKL cs t x.val b := by
  have he : remainingConditions cs u b [] x = ∅ := by
    ext e
    simp [remainingConditions]
  rw [scheduleState,he]
  unfold intervalBoundary
  rw [normalized_emptyKernel_restrictBoundary]
  exact normalized_emptyKernel_of_character cs 1 b basis (one_bruhat cs b)
    (boundarySheaf cs 1 b basis (one_bruhat cs b))
    ((upperInclusion cs u b).vertex x) (hc _) ht ht1

omit [Fintype I] [Fintype σ] in
 theorem schedule_all_conditions (x : Interval cs u b) :
    remainingConditions cs u b (chronologicalSchedule φ) x = Set.univ := by
  ext e
  simp only [remainingConditions,Set.mem_ofPred_eq,Set.mem_univ,iff_true]
  exact chronologicalSchedule_full φ e.val

variable [Fintype (Edge cs 1 b)] [Fintype (Interval cs 1 b)] [DecidableEq (Interval cs 1 b)]

 theorem schedule_initial_of_duality_character
    (d : SectionDuality cs 1 b basis (one_bruhat cs b)
      (boundarySheaf cs 1 b basis (one_bruhat cs b)))
    (hd : ∀ i j (m n : (boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.sections Set.univ),
      m ∈ ((boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.sections Set.univ).piece i →
      n ∈ ((boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.sections Set.univ).piece j →
      d.pairing m n ∈ polynomialGrading ℝ σ (i+j-(cs.length b : ℤ)))
    (hc : StalkCharacterObligation cs 1 b basis (one_bruhat cs b))
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) (x : Interval cs u b) :
    scheduleState cs u b basis hub (intervalBoundary basis hub) t (chronologicalSchedule φ) x =
      scaledKL cs t⁻¹ x.val b := by
  rw [scheduleState,schedule_all_conditions φ]
  unfold intervalBoundary
  rw [normalized_fullKernel_restrictBoundary]
  exact normalized_fullKernel_of_duality_character cs b basis
    (boundarySheaf cs 1 b basis (one_bruhat cs b)) d hd
    ((upperInclusion cs u b).vertex x) (hc _) ht ht1

end
end KLInvariance.BruhatGraph

end


section

/-! Native endpoint normalization from the ACTUAL stalk characters. Unlike the
KL-labelled endpoints, these need neither character recognition nor Hodge. -/
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial SchedulePaths
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section
local instance actualInterval : Fintype (Interval cs 1 b) := by
  let := interval_finite cs 1 b
  exact Fintype.ofFinite _
local instance actualEdges : Fintype (Edge cs 1 b) := Fintype.ofFinite _
local instance (a : Type*) : DecidableEq a := Classical.decEq a

 theorem normalized_emptyKernel_scaledStalk (x : Interval cs 1 b)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    normalizedKernel cs 1 b basis (one_bruhat cs b) (ActualBoundary cs b basis) t x ∅=
      scaledStalk cs b basis t x := by
  rw [normalizedKernel,emptyKernel_hilbert cs 1 b basis (one_bruhat cs b)
    (ActualBoundary cs b basis) x (sq_pos_of_pos ht) (by nlinarith)]
  dsimp only [stateScale,scaledStalk]
  have hne : 1-t^2≠0 := ne_of_gt (by nlinarith : 0<1-t^2)
  rw [inv_pow]
  field_simp [hne,inv_pow]

 theorem normalized_fullKernel_scaledStalk (x : Interval cs 1 b)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    normalizedKernel cs 1 b basis (one_bruhat cs b) (ActualBoundary cs b basis) t x Set.univ=
      scaledStalk cs b basis t⁻¹ x := by
  let C := ActualBoundary cs b basis
  let := C.free x
  let c := (exists_nonnegativeBasis (σ := σ) (C.sheaf.vertex x).piece
    (C.sheaf.vertex x).nonneg).some
  have hcp : c.polynomial=stalkCharacter cs 1 b basis (one_bruhat cs b) x := by
    rw [stalkCharacter_eq_character cs 1 b basis (one_bruhat cs b) C x,
      character_eq (C.sheaf.vertex x).piece (C.sheaf.vertex x).nonneg c]
  rw [normalizedKernel,GradedSheaf.kernelHilbert,
    fullKernel_eq cs 1 b basis (one_bruhat cs b) C x,
    costalk_hilbert_of_duality cs 1 b basis (one_bruhat cs b) C (actualSectionDuality cs b basis)
      (cs.length b) (actualSectionDuality_homogeneous cs b basis) x c
      (sq_pos_of_pos ht) (by nlinarith),hcp,incoming_card cs b x]
  dsimp only [stateScale,scaledStalk]
  have hscale : t^((cs.length x.val : ℤ)-cs.length b)*
      (t^2)^((cs.length b : ℤ)-cs.length x.val)=
      (t⁻¹)^((cs.length x.val : ℤ)-cs.length b) := by
    rw [show (t^2)^((cs.length b : ℤ)-cs.length x.val)=
      t^(2*((cs.length b : ℤ)-cs.length x.val)) by rw [zpow_mul]; norm_num,
      ←zpow_add₀ ht.ne',inv_zpow,←zpow_neg]
    congr 1
    omega
  rw [show (t^2)⁻¹=(t⁻¹)^2 by rw [inv_pow]]
  have hne : 1-t^2≠0 := ne_of_gt (by nlinarith : 0<1-t^2)
  calc
    _ = (t^((cs.length x.val : ℤ)-cs.length b)*
      (t^2)^((cs.length b : ℤ)-cs.length x.val))*
      eval₂ (Int.castRingHom ℝ) ((t⁻¹)^2) (stalkCharacter cs 1 b basis (one_bruhat cs b) x) := by
      have hcancel : (1-t^2)^(Fintype.card σ)*((1-t^2)⁻¹)^(Fintype.card σ)=1 := by
        rw [←mul_pow,mul_inv_cancel₀ hne,one_pow]
      calc
        _ = ((1-t^2)^(Fintype.card σ)*((1-t^2)⁻¹)^(Fintype.card σ))*
            ((t^((cs.length x.val : ℤ)-cs.length b)*(t^2)^((cs.length b : ℤ)-cs.length x.val))*
            eval₂ (Int.castRingHom ℝ) ((t⁻¹)^2) (stalkCharacter cs 1 b basis (one_bruhat cs b) x)) := by ring
        _ = _ := by rw [hcancel,one_mul]
    _ = _ := by rw [hscale]

 theorem schedule_final_scaledStalk (a : W) (hab : BruhatLE cs a b)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) (x : Interval cs a b) :
    scheduleState cs a b basis hab (intervalBoundary basis hab) t [] x=
      scaledStalk cs b basis t ((upperInclusion cs a b).vertex x) := by
  have he : remainingConditions cs a b [] x=∅ := by
    ext e
    simp [remainingConditions]
  rw [scheduleState,he]
  unfold intervalBoundary
  rw [normalized_emptyKernel_restrictBoundary]
  exact normalized_emptyKernel_scaledStalk cs b basis _ ht ht1

 theorem schedule_initial_scaledStalk (a : W) (hab : BruhatLE cs a b)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) (x : Interval cs a b) :
    scheduleState cs a b basis hab (intervalBoundary basis hab) t
      (chronologicalSchedule (OrderIso.refl (Interval cs a b))) x=
      scaledStalk cs b basis t⁻¹ ((upperInclusion cs a b).vertex x) := by
  rw [scheduleState,schedule_all_conditions (OrderIso.refl (Interval cs a b))]
  unfold intervalBoundary
  rw [normalized_fullKernel_restrictBoundary]
  exact normalized_fullKernel_scaledStalk cs b basis _ ht ht1

 theorem native_endpoint_eq (a : W) (hab : BruhatLE cs a b)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    scheduleState cs a b basis hab (intervalBoundary basis hab) t []=
      dispatch (source cs a b) (target cs a b) (t⁻¹-t)
        (scheduleState cs a b basis hab (intervalBoundary basis hab) t
           (chronologicalSchedule (OrderIso.refl (Interval cs a b))))
        (chronologicalSchedule (OrderIso.refl (Interval cs a b))).reverse := by
  have hf := funext (schedule_final_scaledStalk cs b basis a hab ht ht1)
  have hi := funext (schedule_initial_scaledStalk cs b basis a hab ht ht1)
  rw [hf,hi,chronologicalSchedule,List.reverse_reverse]
  funext x
  rw [transported_dispatch_matrix (OrderIso.refl (Interval cs a b)) _ (Int.castRingHom ℝ)]
  exact scaledStalk_reciprocity_upper cs b basis t ht.ne' a x

end
end KLInvariance.BruhatGraph

end


section

namespace KLInvariance.SchedulePaths
universe u v
variable {E : Type u} {Λ : Type v} [LinearOrder Λ]

 theorem exists_suffix_score_gt (score : E → Λ) (r : Λ) (p : List E)
    (hp : p.Pairwise (fun a b => score a ≤ score b)) :
    ∃ q, q <:+ p ∧ ∀ e, e ∈ q ↔ e ∈ p ∧ r < score e := by
  induction p with
  | nil => exact ⟨[],List.suffix_refl _,fun e => by simp⟩
  | cons a p ih =>
    have hs := List.pairwise_cons.mp hp
    by_cases ha : r < score a
    · refine ⟨a::p,List.suffix_refl _,?_⟩
      intro e
      constructor
      · intro he
        refine ⟨he,?_⟩
        rcases List.mem_cons.mp he with rfl | he
        · exact ha
        · exact lt_of_lt_of_le ha (hs.1 e he)
      · exact And.left
    · obtain ⟨q,hq,hmem⟩ := ih hs.2
      refine ⟨q,hq.trans (List.suffix_cons a p),?_⟩
      intro e
      rw [hmem,List.mem_cons]
      constructor
      · exact fun h => ⟨Or.inr h.1,h.2⟩
      · rintro ⟨he,hr⟩
        rcases he with rfl | he
        · exact (ha hr).elim
        · exact ⟨he,hr⟩

end KLInvariance.SchedulePaths

end


section


end

end OAI
