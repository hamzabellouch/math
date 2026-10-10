import OAI.Geometry.KahlerSplitting.GermTransport

namespace OAI

section

noncomputable section
open Set Metric Filter Topology
open scoped Manifold unitInterval
namespace UniversalCoverSplitting
namespace FirstGerm
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

noncomputable def initial (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) (x : X.Carrier) :
    HolomorphicEtale.Germs X X :=
  projection (exists_splittingChart S h₁ h₂ x).choose x
    (exists_splittingChart S h₁ h₂ x).choose_spec.1

lemma initial_base (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) (x : X.Carrier) :
    HolomorphicEtale.base X X (initial h₁ h₂ x)=x := rfl

lemma initial_first (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) (x : X.Carrier) :
    IsFirst (S := S) (initial h₁ h₂ x).val := projection_first _ _ _

lemma initial_eq (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) (e : SplittingChart S)
    (x : X.Carrier) (hx : x ∈ e.chart.source) :
    initial h₁ h₂ x=projection e x hx := projection_eq _ _ _ _ _

lemma continuous_horizontal {A : Type*} [TopologicalSpace A]
    (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S))
    {α : A → X.Carrier} (hα : ProductBoxTopology.IsHorizontal (splittingAtlas S) α) :
    Continuous (fun a ↦ initial h₁ h₂ (α a)) := by
  apply continuous_induced_rng.mpr
  apply FunctionEtale.continuous_of_local (by change Continuous α; exact hα.1)
  intro a
  obtain ⟨e,hea,_⟩ := exists_splittingChart S h₁ h₂ (α a)
  let W := α ⁻¹' e.chart.source
  have hW : IsOpen W := e.chart.open_source.preimage hα.1
  have hlc := (hα.2 e.chart ⟨e,rfl⟩).eventually_eq (⟨a,hea⟩ : W)
  obtain ⟨V,hV,hsub⟩ := (mem_nhds_subtype W ⟨a,hea⟩ _).mp hlc
  refine ⟨e.firstProjection (e.chart (α a)).2,?_⟩
  filter_upwards [hV,hW.mem_nhds hea] with b hbV hbW
  have hsec := hsub (show (⟨b,hbW⟩ : W) ∈ Subtype.val ⁻¹' V from hbV)
  change (e.chart (α b)).2=(e.chart (α a)).2 at hsec
  change (initial h₁ h₂ (α b)).val=
    FunctionEtale.sectionOf (e.firstProjection (e.chart (α a)).2) (α b)
  rw [initial_eq h₁ h₂ e (α b) hbW]
  change FunctionEtale.sectionOf (e.firstProjection (e.chart (α b)).2) (α b)=
    FunctionEtale.sectionOf (e.firstProjection (e.chart (α a)).2) (α b)
  rw [hsec]

lemma lift_diagonal (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) {R : I × I → X.Carrier}
    (hR : ProductBoxTopology.IsBox (splittingAtlas S) R) :
    ∃ G : I → HolomorphicEtale.Germs X X, Continuous G ∧
      G 0=initial h₁ h₂ (R (0,0)) ∧ ∀ a,
        HolomorphicEtale.base X X (G a)=R (a,a) ∧ IsFirst (S := S) (G a).val := by
  classical
  have ex (a : I) := lift_vertical h₁ h₂ (hR.vertical a)
    (initial h₁ h₂ (R (a,0))) rfl (initial_first h₁ h₂ _)
  choose F hFc hF0 hFb using ex
  have hc0 : Continuous (fun a ↦ F a 0) := by
    have he : (fun a ↦ F a 0)=(fun a ↦ initial h₁ h₂ (R (a,0))) := funext hF0
    rw [he]
    exact continuous_horizontal h₁ h₂ (hR.horizontal 0)
  let f : C(I × I,X.Carrier) := ⟨fun p ↦ R (p.2,p.1),hR.1.comp continuous_swap⟩
  have hF : Continuous (fun p : I × I ↦ F p.2 p.1) :=
    (HolomorphicEtale.localHomeomorph X X).continuous_lift (HolomorphicEtale.separated X X)
      f (funext fun p ↦ (hFb p.2 p.1).1) hc0 hFc
  exact ⟨fun a ↦ F a a,hF.comp (continuous_id.prodMk continuous_id),hF0 0,
    fun a ↦ hFb a a⟩

lemma lift_path [CompactSpace X.Carrier] (g : KahlerMetric X)
    (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S))
    {γ : I → X.Carrier} (hγ : Continuous γ) :
    ∃ G : C(I,HolomorphicEtale.Germs X X),
      G 0=initial h₁ h₂ (γ 0) ∧ HolomorphicEtale.base X X ∘ G=γ ∧
        ∀ a, IsFirst (S := S) (G a).val := by
  obtain ⟨R,hR,hdiag⟩ := path_diagonal g h₁ h₂ hγ
  obtain ⟨G,hG,hG0,hGb⟩ := lift_diagonal h₁ h₂ hR
  refine ⟨⟨G,hG⟩,?_,funext fun a ↦ (hGb a).1.trans (hdiag a),fun a ↦ (hGb a).2⟩
  rw [←hdiag 0]
  exact hG0

end FirstGerm
end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology
open scoped Manifold
namespace FunctionEtale
variable {M X : Type*} [TopologicalSpace M]

def value (g : Total M X) : X :=
  Germ.liftOn g.2 (fun f ↦ f g.1) (fun _ _ h ↦ h.eq_of_nhds)

@[simp] lemma value_section (f : M → X) (x : M) : value (sectionOf f x)=f x := rfl
end FunctionEtale

namespace UniversalCoverSplitting
namespace HolomorphicEtale
variable {m n k : ℕ} {M : ComplexManifold m} {X : ComplexManifold n}
    {Z : ComplexManifold k}

def value (g : Germs M X) : X.Carrier := FunctionEtale.value g.val

lemma value_of_section {g : Germs M X} {f : M.Carrier → X.Carrier}
    (hg : g.val=FunctionEtale.sectionOf f (base M X g)) : value g=f (base M X g) := by
  exact congrArg FunctionEtale.value hg

lemma mdifferentiable_value {F : Z.Carrier → Germs M X} (hF : Continuous F)
    {p : Z.Carrier → M.Carrier} (hp : MDifferentiable (model k) (model m) p)
    (hb : base M X ∘ F=p) : MDifferentiable (model k) (model n) (value ∘ F) := by
  intro z
  obtain ⟨U,hU,hz,f,hf,hev⟩ := locally_represented M X hF z
  have hbase (w : Z.Carrier) : base M X (F w)=p w := congrFun hb w
  have hzU : p z ∈ U := hbase z ▸ hz
  have hd := ((hf (p z) hzU).mdifferentiableAt (hU.mem_nhds hzU)).comp z (hp z)
  apply hd.congr_of_eventuallyEq
  filter_upwards [hev] with w hw
  change value (F w)=f (p w)
  rw [value_of_section hw.2,hbase]

lemma value_locally {A : Type*} [TopologicalSpace A]
    {F : A → Germs M X} (hF : Continuous F) {a : A}
    {f : M.Carrier → X.Carrier} (he : (F a).val=FunctionEtale.sectionOf f (base M X (F a))) :
    (fun b ↦ value (F b)) =ᶠ[𝓝 a] (fun b ↦ f (base M X (F b))) := by
  have hev := (continuous_subtype_val.comp hF).continuousAt.eventually
    ((FunctionEtale.isOpen_basic f isOpen_univ).mem_nhds ⟨mem_univ _,he⟩)
  exact hev.mono fun _ h ↦ value_of_section h.2

end HolomorphicEtale

lemma LocalBiholomorphism.mdifferentiable {n : ℕ} {X Z : ComplexManifold n}
    {p : Z.Carrier → X.Carrier} (hp : LocalBiholomorphism p) :
    MDifferentiable (model n) (model n) p := by
  intro z
  obtain ⟨e,hz,he,hd,_⟩ := hp z
  exact ((hd z hz).mdifferentiableAt (e.open_source.mem_nhds hz)).congr_of_eventuallyEq
    (Filter.mem_of_superset (e.open_source.mem_nhds hz) (fun w hw ↦ (he w hw).symm))

end UniversalCoverSplitting
end
end

section

noncomputable section
open scoped unitInterval

lemma IsLocalHomeomorph.lift_of_simplyConnected
    {A E X : Type*} [TopologicalSpace A] [TopologicalSpace E] [TopologicalSpace X]
    [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]
    {p : E → X} (hp : IsLocalHomeomorph p) (hsep : IsSeparatedMap p)
    (f : C(A,X)) (a₀ : A) (e₀ : E) (he : p e₀=f a₀)
    (ex : ∀ γ : C(I,A), γ 0=a₀ → ∃ Γ : C(I,E), Γ 0=e₀ ∧ p ∘ Γ=f.comp γ) :
    ∃! F : C(A,E), F a₀=e₀ ∧ p ∘ F=f := by
  apply hp.existsUnique_continuousMap_lifts f a₀ e₀ he ex
  intro γ γ' Γ Γ' hγ hγ' hΓ hΓ' hl hl' hend
  let q : Path a₀ (γ 1) := ⟨γ,hγ,rfl⟩
  let q' : Path a₀ (γ 1) := ⟨γ',hγ',hend.symm⟩
  obtain ⟨H⟩ := SimplyConnectedSpace.paths_homotopic q q'
  choose L hL0 hLl using (fun t : I ↦ ex (H.eval t) (H.eval t).source)
  have h0 : (L 0 : I → E)=Γ := by
    refine hsep.eq_of_comp_eq hp.isLocallyInjective (L 0).continuous Γ.continuous ?_ 0 ?_
    · rw [hLl,hl]
      rw [H.eval_zero]
      rfl
    · exact (hL0 0).trans hΓ.symm
  have h1 : (L 1 : I → E)=Γ' := by
    refine hsep.eq_of_comp_eq hp.isLocallyInjective (L 1).continuous Γ'.continuous ?_ 0 ?_
    · rw [hLl,hl']
      rw [H.eval_one]
      rfl
    · exact (hL0 1).trans hΓ'.symm
  have heq := hp.monodromy_theorem hsep (H.map f) L
    (fun t s ↦ congrFun (hLl t) s) (fun t ↦ (hL0 t).trans (hL0 0).symm) 1
  rw [h0,h1] at heq
  exact heq.symm
end
end

section

noncomputable section
open Set Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n k : ℕ} {X Z : ComplexManifold n} {A : ComplexManifold k}

lemma LocalBiholomorphism.mdifferentiable_lift {p : Z.Carrier → X.Carrier}
    (hp : LocalBiholomorphism p) {F : A.Carrier → Z.Carrier} (hF : Continuous F)
    {f : A.Carrier → X.Carrier} (hf : MDifferentiable (model k) (model n) f)
    (hl : p ∘ F=f) : MDifferentiable (model k) (model n) F := by
  intro a
  obtain ⟨e,hea,he,_,hdi⟩ := hp (F a)
  have hfa : f a=e (F a) := (congrFun hl a).symm.trans (he _ hea).symm
  have hft : f a ∈ e.target := hfa ▸ e.map_source hea
  have hd := ((hdi (f a) hft).mdifferentiableAt (e.open_target.mem_nhds hft)).comp a (hf a)
  apply hd.congr_of_eventuallyEq
  filter_upwards [hF.continuousAt (e.open_source.mem_nhds hea)] with b hb
  change F b=e.symm (f b)
  rw [←congrFun hl b]
  change F b=e.symm (p (F b))
  rw [←he _ hb]
  exact (e.left_inv hb).symm

lemma OrdinaryUniversalCover.holomorphic_lift (π : OrdinaryUniversalCover X Z)
    [SimplyConnectedSpace A.Carrier] {f : A.Carrier → X.Carrier}
    (hf : MDifferentiable (model k) (model n) f) (a : A.Carrier) (z : Z.Carrier)
    (hz : π.projection z=f a) :
    ∃ F : A.Carrier → Z.Carrier, MDifferentiable (model k) (model n) F ∧
      F a=z ∧ π.projection ∘ F=f := by
  let : LocallyPathConnectedSpace A.Carrier := ChartedSpace.locallyPathConnectedSpace (Model k) A.Carrier
  obtain ⟨F,⟨hF0,hFl⟩,_⟩ := π.covering.existsUnique_continuousMap_lifts ⟨f,hf.continuous⟩ a z hz
  exact ⟨F,π.liftedComplexStructure.mdifferentiable_lift F.continuous hf hFl,hF0,hFl⟩

end UniversalCoverSplitting
end
end

end OAI
