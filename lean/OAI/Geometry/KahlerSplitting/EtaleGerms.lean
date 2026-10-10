import OAI.Geometry.KahlerSplitting.PathBoxes

namespace OAI

section

noncomputable section
open Set Filter Topology
namespace FunctionEtale
variable (X Y : Type*) [TopologicalSpace X]

def Total := (x : X) × Germ (𝓝 x) Y

variable {X Y}
def base (g : Total X Y) : X := g.1
def sectionOf (f : X → Y) (x : X) : Total X Y := ⟨x,(f : Germ (𝓝 x) Y)⟩

def basic (f : X → Y) (U : Set X) : Set (Total X Y) :=
  {g | base g ∈ U ∧ g=sectionOf f (base g)}

instance : TopologicalSpace (Total X Y) :=
  TopologicalSpace.generateFrom {W | ∃ f U, IsOpen U ∧ W=basic f U}

lemma section_eq {f h : X → Y} {x : X} :
    sectionOf f x=sectionOf h x ↔ f =ᶠ[𝓝 x] h := by
  change (Sigma.mk (β := fun z : X ↦ Germ (𝓝 z) Y) x (f : Germ (𝓝 x) Y)=Sigma.mk x (h : Germ (𝓝 x) Y)) ↔ _
  simp only [Sigma.mk.inj_iff,heq_eq_eq,Germ.coe_eq,true_and]

lemma isOpen_basic (f : X → Y) {U : Set X} (hU : IsOpen U) : IsOpen (basic f U) :=
  TopologicalSpace.isOpen_generateFrom_of_mem ⟨f,U,hU,rfl⟩

lemma continuous_section (f : X → Y) : Continuous (sectionOf f) := by
  apply continuous_generateFrom_iff.mpr
  rintro W ⟨h,U,hU,rfl⟩
  have he : sectionOf f ⁻¹' basic h U=U ∩ {x | f =ᶠ[𝓝 x] h} := by
    ext x; exact and_congr Iff.rfl section_eq
  rw [he]
  exact hU.inter isOpen_setOfPred_eventually_nhds

lemma exists_representative (g : Total X Y) : ∃ f : X → Y, g=sectionOf f (base g) := by
  rcases g with ⟨x,g⟩
  induction g using Germ.inductionOn with | h f => exact ⟨f,rfl⟩

lemma continuous_base : Continuous (base : Total X Y → X) := by
  apply continuous_def.mpr
  intro U hU
  have he : base ⁻¹' U=⋃ f : X → Y, basic f U := by
    ext g; constructor
    · intro h
      obtain ⟨f,hf⟩ := exists_representative g
      exact mem_iUnion.mpr ⟨f,h,hf⟩
    · intro h; obtain ⟨f,hf⟩ := mem_iUnion.mp h; exact hf.1
  rw [he]
  exact isOpen_iUnion (fun f ↦ isOpen_basic f hU)

def chart (f : X → Y) : OpenPartialHomeomorph (Total X Y) X where
  toFun := base
  invFun := sectionOf f
  source := basic f univ
  target := univ
  map_source' := fun _ _ ↦ trivial
  map_target' := fun _ _ ↦ ⟨trivial,rfl⟩
  left_inv' := fun _ h ↦ h.2.symm
  right_inv' := fun _ _ ↦ rfl
  open_source := isOpen_basic f isOpen_univ
  open_target := isOpen_univ
  continuousOn_toFun := continuous_base.continuousOn
  continuousOn_invFun := (continuous_section f).continuousOn

lemma isLocalHomeomorph_base : IsLocalHomeomorph (base : Total X Y → X) := by
  intro g
  obtain ⟨f,hf⟩ := exists_representative g
  exact ⟨chart f,⟨trivial,hf⟩,rfl⟩

lemma isOpen_of_local {P : Set (Total X Y)}
    (hP : ∀ f : X → Y, IsOpen {x | sectionOf f x ∈ P}) : IsOpen P := by
  have he : P=⋃ f : X → Y, basic f {x | sectionOf f x ∈ P} := by
    ext g; constructor
    · intro h
      obtain ⟨f,hf⟩ := exists_representative g
      exact mem_iUnion.mpr ⟨f,show sectionOf f (base g) ∈ P from hf ▸ h,hf⟩
    · intro h
      obtain ⟨f,hf⟩ := mem_iUnion.mp h
      exact hf.2 ▸ hf.1
  rw [he]
  exact isOpen_iUnion (fun f ↦ isOpen_basic f (hP f))

lemma isLocalHomeomorph_restrict {P : Set (Total X Y)} (hP : IsOpen P) :
    IsLocalHomeomorph (fun g : P ↦ base g.val) :=
  isLocalHomeomorph_base.comp hP.isOpenEmbedding_subtypeVal.isLocalHomeomorph

lemma continuous_of_local {A : Type*} [TopologicalSpace A] {g : A → Total X Y}
    (hb : Continuous (base ∘ g))
    (hl : ∀ a, ∃ f : X → Y, ∀ᶠ b in 𝓝 a, g b=sectionOf f (base (g b))) : Continuous g := by
  apply continuous_iff_continuousAt.mpr
  intro a
  obtain ⟨f,hf⟩ := hl a
  exact ((continuous_section f).comp hb).continuousAt.congr (Filter.EventuallyEq.symm hf)

lemma locally_represented {A : Type*} [TopologicalSpace A] {g : A → Total X Y}
    (hg : Continuous g) (a : A) :
    ∃ f : X → Y, ∀ᶠ b in 𝓝 a, g b=sectionOf f (base (g b)) := by
  obtain ⟨f,hf⟩ := exists_representative (g a)
  exact ⟨f,(hg.continuousAt.eventually ((isOpen_basic f isOpen_univ).mem_nhds ⟨trivial,hf⟩)).mono
    fun _ h ↦ h.2⟩

end FunctionEtale
end
end

section

noncomputable section
open Set Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
namespace HolomorphicEtale
variable {m n : ℕ} (M : ComplexManifold m) (X : ComplexManifold n)

def IsHolomorphic (g : FunctionEtale.Total M.Carrier X.Carrier) : Prop :=
  ∃ U : Set M.Carrier, IsOpen U ∧ FunctionEtale.base g ∈ U ∧
    ∃ f : M.Carrier → X.Carrier,
      MDifferentiableOn (model m) (model n) f U ∧
      g=FunctionEtale.sectionOf f (FunctionEtale.base g)

abbrev Germs := {g : FunctionEtale.Total M.Carrier X.Carrier // IsHolomorphic M X g}
def base (g : Germs M X) : M.Carrier := FunctionEtale.base g.val

lemma isOpen_holomorphic : IsOpen {g | IsHolomorphic M X g} := by
  apply FunctionEtale.isOpen_of_local
  intro f
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨U,hU,hxU,h,hh,he⟩ := hx
  have heq : f =ᶠ[𝓝 x] h := FunctionEtale.section_eq.mp he
  filter_upwards [hU.mem_nhds hxU,heq.eventually_nhds] with y hy he'
  exact ⟨U,hU,hy,h,hh,FunctionEtale.section_eq.mpr he'⟩

lemma localHomeomorph : IsLocalHomeomorph (base M X) :=
  FunctionEtale.isLocalHomeomorph_restrict (isOpen_holomorphic M X)

lemma separated : IsSeparatedMap (base M X) := by
  let : LocallyConnectedSpace M.Carrier := ChartedSpace.locallyConnectedSpace (Model m) M.Carrier
  intro a b hab hne
  obtain ⟨U,hU,haU,f,hf,ha⟩ := a.property
  obtain ⟨V,hV,hbV,g,hg,hb⟩ := b.property
  have hcommon : U ∩ V ∈ 𝓝 (base M X a) :=
    inter_mem (hU.mem_nhds haU) (hV.mem_nhds (hab ▸ hbV))
  obtain ⟨W,⟨hW,haW,hWc⟩,hsub⟩ :=
    (LocallyConnectedSpace.open_connected_basis (base M X a)).mem_iff.mp hcommon
  let A : Set (Germs M X) := Subtype.val ⁻¹' FunctionEtale.basic f W
  let B : Set (Germs M X) := Subtype.val ⁻¹' FunctionEtale.basic g W
  refine ⟨A,B,(FunctionEtale.isOpen_basic f hW).preimage continuous_subtype_val,
    (FunctionEtale.isOpen_basic g hW).preimage continuous_subtype_val,
    ⟨haW,ha⟩,⟨show base M X b ∈ W from hab ▸ haW,hb⟩,?_⟩
  apply disjoint_left.mpr
  intro c hcA hcB
  have hfg : f =ᶠ[𝓝 (base M X c)] g :=
    FunctionEtale.section_eq.mp (hcA.2.symm.trans hcB.2)
  have heq := holomorphic_manifolds_eqOn_of_preconnected_of_eventuallyEq hW hWc.2
    (hf.mono (fun _ h ↦ (hsub h).1)) (hg.mono (fun _ h ↦ (hsub h).2)) hcA.1 hfg
  apply hne
  apply Subtype.ext
  calc a.val=FunctionEtale.sectionOf f (base M X a) := ha
       _ = FunctionEtale.sectionOf g (base M X a) :=
         FunctionEtale.section_eq.mpr (Filter.mem_of_superset (hW.mem_nhds haW) heq)
       _ = b.val := by rw [hab]; exact hb.symm

def sectionOf (f : M.Carrier → X.Carrier) {U : Set M.Carrier} (hU : IsOpen U)
    (hf : MDifferentiableOn (model m) (model n) f U) : U → Germs M X :=
  fun x ↦ ⟨FunctionEtale.sectionOf f x, U,hU,x.property,f,hf,rfl⟩

lemma continuous_section (f : M.Carrier → X.Carrier) {U : Set M.Carrier}
    (hU : IsOpen U) (hf : MDifferentiableOn (model m) (model n) f U) :
    Continuous (sectionOf M X f hU hf) :=
  ((FunctionEtale.continuous_section f).comp continuous_subtype_val).subtype_mk _

lemma locally_represented {A : Type*} [TopologicalSpace A] {F : A → Germs M X}
    (hF : Continuous F) (a : A) :
    ∃ U : Set M.Carrier, IsOpen U ∧ base M X (F a) ∈ U ∧
      ∃ f : M.Carrier → X.Carrier, MDifferentiableOn (model m) (model n) f U ∧
        ∀ᶠ b in 𝓝 a, base M X (F b) ∈ U ∧
          (F b).val=FunctionEtale.sectionOf f (base M X (F b)) := by
  obtain ⟨U,hU,hxU,f,hf,he⟩ := (F a).property
  refine ⟨U,hU,hxU,f,hf,?_⟩
  exact (continuous_subtype_val.comp hF).continuousAt.eventually
    ((FunctionEtale.isOpen_basic f hU).mem_nhds ⟨hxU,he⟩)

end HolomorphicEtale
end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma SplittingChart.transition_first (e d : SplittingChart S) {x : X.Carrier}
    (he : x ∈ e.chart.source) (hd : x ∈ d.chart.source) :
    (fun y ↦ (e.chart y).1) =ᶠ[𝓝 x]
      (fun y ↦ (e.chart (d.chart.symm ((d.chart y).1,(d.chart x).2))).1) := by
  let z := d.chart x
  have hzt : z ∈ d.chart.target := d.chart.map_source hd
  have hN : d.chart.target ∩ d.chart.symm ⁻¹' e.chart.source ∈ 𝓝 z := by
    refine inter_mem (d.chart.open_target.mem_nhds hzt) ((d.chart.symm.continuousAt hzt) ?_)
    simpa only [z,d.chart.left_inv hd] using e.chart.open_source.mem_nhds he
  obtain ⟨ε,hε,hεN⟩ := Metric.mem_nhds_iff.mp hN
  let U := ball z.1 ε
  let V := ball z.2 ε
  have hUV : U ×ˢ V ⊆ d.chart.target ∩ d.chart.symm ⁻¹' e.chart.source := by
    simpa only [U,V,ball_prod_same,Prod.eta] using hεN
  have hc := e.block_coordinates (isOpen_ball.prod isOpen_ball)
    (d.inverse_isBlockBox.mono (fun _ h ↦ (hUV h).1)) (fun _ h ↦ (hUV h).2)
  let F : Model r × Model s → Model r := fun p ↦ (e.chart (d.chart.symm p)).1
  have hF : DifferentiableOn ℂ F (U ×ˢ V) := hc.1.fst
  have hzero : ∀ p ∈ U ×ˢ V, ∀ v : Model s, fderiv ℂ F p (0,v)=0 := by
    intro p hp v
    have H := ((hc.1.differentiableAt ((isOpen_ball.prod isOpen_ball).mem_nhds hp)).hasFDerivAt.fst).fderiv
    change fderiv ℂ F p = _ at H
    rw [H]
    exact (hc.2 p hp).2 v
  have hloc : ∀ p ∈ U ×ˢ V, F p=F (p.1,z.2) := by
    intro p hp
    exact independent_second_of_fderiv_zero isOpen_ball isOpen_ball (convex_ball z.2 ε).isPreconnected
      hF hzero hp.1 hp.2 (mem_ball_self hε)
  have hdx := d.chart.continuousAt hd
  filter_upwards [d.chart.open_source.mem_nhds hd,
    hdx ((isOpen_ball.prod isOpen_ball).mem_nhds (show z ∈ U ×ˢ V from
      ⟨mem_ball_self hε,mem_ball_self hε⟩))] with y hy hdy
  simpa only [F,d.chart.left_inv hy] using hloc (d.chart y) hdy

namespace FirstGerm

def IsFirst (g : FunctionEtale.Total X.Carrier X.Carrier) : Prop :=
  ∀ e : SplittingChart S, FunctionEtale.base g ∈ e.chart.source →
    ∃ h : Model r → X.Carrier,
      g=FunctionEtale.sectionOf (fun y ↦ h (e.chart y).1) (FunctionEtale.base g)

lemma of_factor (e : SplittingChart S) {x : X.Carrier} (hx : x ∈ e.chart.source)
    (h : Model r → X.Carrier) :
    IsFirst (S := S) (FunctionEtale.sectionOf (fun y ↦ h (e.chart y).1) x) := by
  intro d hd
  refine ⟨fun a ↦ h (e.chart (d.chart.symm (a,(d.chart x).2))).1,?_⟩
  apply FunctionEtale.section_eq.mpr
  exact (e.transition_first d hx hd).mono (fun y hy ↦ congrArg h hy)

lemma congr {g k : FunctionEtale.Total X.Carrier X.Carrier}
    (hg : IsFirst (S := S) g) (h : g=k) : IsFirst (S := S) k := h ▸ hg

end FirstGerm
end UniversalCoverSplitting
end
end

end OAI
