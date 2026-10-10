import OAI.Geometry.KahlerSplitting.BlockMaps

namespace OAI

section

noncomputable section
open Set Filter Topology
open scoped unitInterval

namespace ProductBoxTopology
variable {A B X C D : Type*} [TopologicalSpace A] [TopologicalSpace B]
  [TopologicalSpace X] [TopologicalSpace C] [TopologicalSpace D]

def IsBox (atlas : Set (OpenPartialHomeomorph X (C × D))) (F : A × B → X) : Prop :=
  Continuous F ∧ ∀ e ∈ atlas,
    (∀ a, IsLocallyConstant (fun b : {b : B // F (a,b) ∈ e.source} ↦ (e (F (a,b))).1)) ∧
    (∀ b, IsLocallyConstant (fun a : {a : A // F (a,b) ∈ e.source} ↦ (e (F (a,b))).2))

lemma IsBox.separated {atlas : Set (OpenPartialHomeomorph X (C × D))}
    {F : A × B → X} (hF : IsBox atlas F) {e : OpenPartialHomeomorph X (C × D)}
    (he : e ∈ atlas) {U : Set A} {V : Set B} (hU : IsPreconnected U) (hV : IsPreconnected V)
    (hmap : MapsTo F (U ×ˢ V) e.source) {a a₀ : A} {b b₀ : B}
    (ha : a ∈ U) (ha₀ : a₀ ∈ U) (hb : b ∈ V) (hb₀ : b₀ ∈ V) :
    e (F (a,b)) = ((e (F (a,b₀))).1,(e (F (a₀,b))).2) := by
  let : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hU
  let : PreconnectedSpace V := isPreconnected_iff_preconnectedSpace.mp hV
  have h₁ : IsLocallyConstant (fun b : V ↦ (e (F (a,b))).1) :=
    ((hF.2 e he).1 a).comp_continuous (continuous_subtype_val.subtype_mk
      (fun b ↦ hmap ⟨ha,b.property⟩))
  have h₂ : IsLocallyConstant (fun a : U ↦ (e (F (a,b))).2) :=
    ((hF.2 e he).2 b).comp_continuous (continuous_subtype_val.subtype_mk
      (fun a ↦ hmap ⟨a.property,hb⟩))
  exact Prod.ext (h₁.apply_eq_of_preconnectedSpace ⟨b,hb⟩ ⟨b₀,hb₀⟩)
    (h₂.apply_eq_of_preconnectedSpace ⟨a,ha⟩ ⟨a₀,ha₀⟩)

theorem unique [T2Space X] (atlas : Set (OpenPartialHomeomorph X (C × D)))
    (hcover : ∀ x : X, ∃ e ∈ atlas, x ∈ e.source)
    {F G : I × I → X} (hF : IsBox atlas F) (hG : IsBox atlas G)
    (hbottom : ∀ a, F (a,0)=G (a,0)) (hleft : ∀ b, F (0,b)=G (0,b)) : F = G := by
  classical
  let c : Option atlas → Set (I × I)
    | none => {p | F p ≠ G p}
    | some e => F ⁻¹' e.val.source ∩ G ⁻¹' e.val.source
  have hc : ∀ i, IsOpen (c i) := by
    rintro (_|e)
    · exact (isClosed_eq hF.1 hG.1).isOpen_compl
    · exact (e.val.open_source.preimage hF.1).inter (e.val.open_source.preimage hG.1)
  have hcU : univ ⊆ ⋃ i, c i := by
    intro p _
    by_cases hp : F p = G p
    · obtain ⟨e,he,hpe⟩ := hcover (F p)
      exact mem_iUnion.mpr ⟨some ⟨e,he⟩,hpe,show G p ∈ e.source from hp ▸ hpe⟩
    · exact mem_iUnion.mpr ⟨none,hp⟩
  obtain ⟨t,ht0,htmono,⟨N,hN⟩,ht⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval_prod_self hc hcU
  have hprefix : ∀ i j, EqOn F G (Icc 0 (t i) ×ˢ Icc 0 (t j)) := by
    intro i
    induction i with
    | zero =>
      intro j p hp
      have hp0 : p.1 = 0 := le_antisymm (ht0 ▸ hp.1.2) hp.1.1
      change F (p.1,p.2)=G (p.1,p.2)
      rw [hp0]
      exact hleft p.2
    | succ i hi =>
      intro j
      induction j with
      | zero =>
        intro p hp
        have hp0 : p.2 = 0 := le_antisymm (ht0 ▸ hp.2.2) hp.2.1
        change F (p.1,p.2)=G (p.1,p.2)
        rw [hp0]
        exact hbottom p.1
      | succ j hj =>
        intro p hp
        by_cases hpi : p.1 ≤ t i
        · exact hi (j+1) ⟨⟨hp.1.1,hpi⟩,hp.2⟩
        by_cases hpj : p.2 ≤ t j
        · exact hj ⟨hp.1,⟨hp.2.1,hpj⟩⟩
        have hti : t i ≤ t (i+1) := htmono (Nat.le_succ i)
        have htj : t j ≤ t (j+1) := htmono (Nat.le_succ j)
        have hcorner : F (t i,t j)=G (t i,t j) := hi j ⟨⟨bot_le,le_rfl⟩,⟨bot_le,le_rfl⟩⟩
        obtain ⟨k,hk⟩ := ht i j
        cases k with
        | none => exact False.elim ((hk ⟨⟨le_rfl,hti⟩,⟨le_rfl,htj⟩⟩) hcorner)
        | some e =>
          have hmapF : MapsTo F (Icc (t i) (t (i+1)) ×ˢ Icc (t j) (t (j+1))) e.val.source :=
            fun _ h ↦ (hk h).1
          have hmapG : MapsTo G (Icc (t i) (t (i+1)) ×ˢ Icc (t j) (t (j+1))) e.val.source :=
            fun _ h ↦ (hk h).2
          have hpa : p.1 ∈ Icc (t i) (t (i+1)) := ⟨(not_le.mp hpi).le,hp.1.2⟩
          have hpb : p.2 ∈ Icc (t j) (t (j+1)) := ⟨(not_le.mp hpj).le,hp.2.2⟩
          have ha0 : t i ∈ Icc (t i) (t (i+1)) := ⟨le_rfl,hti⟩
          have hb0 : t j ∈ Icc (t j) (t (j+1)) := ⟨le_rfl,htj⟩
          apply e.val.injOn (hmapF ⟨hpa,hpb⟩) (hmapG ⟨hpa,hpb⟩)
          rw [hF.separated e.property isPreconnected_Icc isPreconnected_Icc hmapF hpa ha0 hpb hb0,
            hG.separated e.property isPreconnected_Icc isPreconnected_Icc hmapG hpa ha0 hpb hb0]
          have hbEq : F (p.1,t j)=G (p.1,t j) := hj ⟨hp.1,⟨bot_le,le_rfl⟩⟩
          have hlEq : F (t i,p.2)=G (t i,p.2) := hi (j+1) ⟨⟨bot_le,le_rfl⟩,hp.2⟩
          rw [hbEq,hlEq]
  funext p
  exact hprefix N N (by simpa only [hN N le_rfl] using
    (show p ∈ Icc (0:I) 1 ×ˢ Icc (0:I) 1 from ⟨⟨bot_le,le_top⟩,⟨bot_le,le_top⟩⟩))

end ProductBoxTopology
end
end

section

noncomputable section
open Set Filter Topology
namespace ProductBoxTopology
variable {A B X C D : Type*} [TopologicalSpace A] [TopologicalSpace B]
  [TopologicalSpace X] [TopologicalSpace C] [TopologicalSpace D]

lemma locallyConstant_of_finite_closed_cover {ι Y : Type*} [Finite ι]
    (U : ι → Set A) (hU : ∀ i, IsClosed (U i)) (hcover : ∀ a, ∃ i, a ∈ U i)
    {f : A → Y} (hf : ∀ i, IsLocallyConstant (fun a : U i ↦ f a)) : IsLocallyConstant f := by
  intro W
  have heq : (f ⁻¹' W)ᶜ = ⋃ i, Subtype.val '' ((fun a : U i ↦ f a) ⁻¹' Wᶜ) := by
    ext a
    constructor
    · intro ha
      obtain ⟨i,hi⟩ := hcover a
      exact mem_iUnion.mpr ⟨i,⟨⟨a,hi⟩,ha,rfl⟩⟩
    · rintro ⟨_,⟨i,rfl⟩,⟨a,ha,rfl⟩⟩
      exact ha
  rw [← isClosed_compl_iff,heq]
  apply isClosed_iUnion_of_finite
  intro i
  exact (hU i).isClosedMap_subtype_val _ ((hf i W).isClosed_compl)

lemma locallyConstant_source_of_finite_closed_cover {ι Y : Type*} [Finite ι]
    (U : ι → Set A) (hU : ∀ i, IsClosed (U i)) (hcover : ∀ a, ∃ i, a ∈ U i)
    (p : A → Prop) {f : A → Y}
    (hf : ∀ i, IsLocallyConstant (fun a : {a : U i // p a} ↦ f a)) :
    IsLocallyConstant (fun a : {a : A // p a} ↦ f a) := by
  apply locallyConstant_of_finite_closed_cover
    (fun i ↦ Subtype.val ⁻¹' U i) (fun i ↦ (hU i).preimage continuous_subtype_val)
    (fun a ↦ hcover a)
  intro i
  let g : {a : {a : A // p a} // a.val ∈ U i} → {a : U i // p a} :=
    fun a ↦ ⟨⟨a.val.val,a.property⟩,a.val.property⟩
  have hg : Continuous g := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  exact (hf i).comp_continuous hg

lemma IsBox.precomp {atlas : Set (OpenPartialHomeomorph X (C × D))}
    {F : A × B → X} (hF : IsBox atlas F) {A' B' : Type*}
    [TopologicalSpace A'] [TopologicalSpace B'] {a : A' → A} {b : B' → B}
    (ha : Continuous a) (hb : Continuous b) :
    IsBox atlas (fun p : A' × B' ↦ F (a p.1,b p.2)) := by
  refine ⟨hF.1.comp (ha.prodMap hb),?_⟩
  intro e he
  constructor
  · intro x
    exact ((hF.2 e he).1 (a x)).comp_continuous
      ((hb.comp continuous_subtype_val).subtype_mk (fun y ↦ y.property))
  · intro y
    exact ((hF.2 e he).2 (b y)).comp_continuous
      ((ha.comp continuous_subtype_val).subtype_mk (fun x ↦ x.property))

lemma IsBox.of_closed_rectangles {atlas : Set (OpenPartialHomeomorph X (C × D))}
    {F : A × B → X} (hF : Continuous F) {ι : Type*} [Finite ι]
    (U : ι → Set A) (V : ι → Set B) (hU : ∀ i, IsClosed (U i)) (hV : ∀ i, IsClosed (V i))
    (hcover : ∀ p : A × B, ∃ i, p ∈ U i ×ˢ V i)
    (hf : ∀ i, IsBox atlas (fun p : U i × V i ↦ F (p.1,p.2))) : IsBox atlas F := by
  refine ⟨hF,fun e he ↦ ⟨?_,?_⟩⟩
  · intro a
    apply locallyConstant_source_of_finite_closed_cover (f := fun b ↦ (e (F (a,b))).1)
      (fun i : {i : ι // a ∈ U i} ↦ V i) (fun i ↦ hV i)
      (fun b ↦ by obtain ⟨i,hi⟩ := hcover (a,b); exact ⟨⟨i,hi.1⟩,hi.2⟩)
      (fun b ↦ F (a,b) ∈ e.source)
    intro i
    exact ((hf i).2 e he).1 ⟨a,i.property⟩
  · intro b
    apply locallyConstant_source_of_finite_closed_cover (f := fun a ↦ (e (F (a,b))).2)
      (fun i : {i : ι // b ∈ V i} ↦ U i) (fun i ↦ hU i)
      (fun a ↦ by obtain ⟨i,hi⟩ := hcover (a,b); exact ⟨⟨i,hi.2⟩,hi.1⟩)
      (fun a ↦ F (a,b) ∈ e.source)
    intro i
    exact ((hf i).2 e he).2 ⟨b,i.property⟩

end ProductBoxTopology
end
end

section

noncomputable section
open Set Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

lemma locallyConstant_restrict_of_fderiv_zero {H K : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [NormedAddCommGroup K] [NormedSpace ℂ K]
    {U : Set H} (hU : IsOpen U) {f : H → K} (hf : DifferentiableOn ℂ f U)
    (hd : ∀ x ∈ U, fderiv ℂ f x = 0) : IsLocallyConstant (fun x : U ↦ f x) := by
  intro W
  have hW := hU.isOpen_inter_preimage_of_fderiv_eq_zero hf hd W
  convert hW.preimage (continuous_subtype_val : Continuous (Subtype.val : U → H)) using 1
  ext x
  simp

def splittingAtlas (S : HolomorphicSplitting X r s) :
    Set (OpenPartialHomeomorph X.Carrier (Model r × Model s)) :=
  Set.range (fun e : SplittingChart S ↦ e.chart)

lemma IsBlockBox.plaqueBox {U : Set E} {V : Set F} (hU : IsOpen U) (hV : IsOpen V)
    {f : E × F → X.Carrier} (hf : IsBlockBox S (U ×ˢ V) f) :
    ProductBoxTopology.IsBox (splittingAtlas S) (fun p : U × V ↦ f (p.1,p.2)) := by
  have hcont : ContinuousOn f (U ×ˢ V) := hf.1.continuousOn
  refine ⟨hcont.comp_continuous (continuous_subtype_val.prodMap continuous_subtype_val)
    (fun p ↦ ⟨p.1.property,p.2.property⟩),?_⟩
  rintro _ ⟨e,rfl⟩
  let W : Set (E × F) := (U ×ˢ V) ∩ f ⁻¹' e.chart.source
  have hW : IsOpen W := hcont.isOpen_inter_preimage (hU.prod hV) e.chart.open_source
  have hc := e.block_coordinates hW (hf.mono inter_subset_left)
    (show MapsTo f W e.chart.source from fun _ h ↦ h.2)
  constructor
  · intro a
    let T : Set F := V ∩ (fun b ↦ f (a,b)) ⁻¹' e.chart.source
    have hT : IsOpen T := (hcont.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ h ↦ ⟨a.property,h⟩)).isOpen_inter_preimage hV e.chart.open_source
    have hd (b : F) (hb : b ∈ T) : HasFDerivAt (fun b ↦ (e.chart (f (a,b))).1) (0 : F →L[ℂ] Model r) b := by
      have hab : ((a:E),b) ∈ W := ⟨⟨a.property,hb.1⟩,hb.2⟩
      have hg := (hc.1.differentiableAt (hW.mem_nhds hab)).hasFDerivAt.fst.comp b
        ((hasFDerivAt_const (𝕜 := ℂ) (a:E) b).prodMk (hasFDerivAt_id (𝕜 := ℂ) b))
      have heq : ((ContinuousLinearMap.fst ℂ (Model r) (Model s)).comp
          (fderiv ℂ (e.chart ∘ f) ((a:E),b))).comp
          ((0 : F →L[ℂ] E).prod (ContinuousLinearMap.id ℂ F)) = 0 := by
        apply ContinuousLinearMap.ext
        intro w
        exact (hc.2 _ hab).2 w
      rw [heq] at hg
      exact hg
    have hl := locallyConstant_restrict_of_fderiv_zero hT
      (fun b hb ↦ (hd b hb).differentiableAt.differentiableWithinAt) (fun b hb ↦ (hd b hb).fderiv)
    exact hl.comp_continuous ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk
      (fun b ↦ ⟨b.val.property,b.property⟩))
  · intro b
    let T : Set E := U ∩ (fun a ↦ f (a,b)) ⁻¹' e.chart.source
    have hT : IsOpen T := (hcont.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ h ↦ ⟨h,b.property⟩)).isOpen_inter_preimage hU e.chart.open_source
    have hd (a : E) (ha : a ∈ T) : HasFDerivAt (fun a ↦ (e.chart (f (a,b))).2) (0 : E →L[ℂ] Model s) a := by
      have hab : (a,(b:F)) ∈ W := ⟨⟨ha.1,b.property⟩,ha.2⟩
      have hg := (hc.1.differentiableAt (hW.mem_nhds hab)).hasFDerivAt.snd.comp a
        ((hasFDerivAt_id (𝕜 := ℂ) a).prodMk (hasFDerivAt_const (𝕜 := ℂ) (b:F) a))
      have heq : ((ContinuousLinearMap.snd ℂ (Model r) (Model s)).comp
          (fderiv ℂ (e.chart ∘ f) (a,(b:F)))).comp
          ((ContinuousLinearMap.id ℂ E).prod (0 : E →L[ℂ] F)) = 0 := by
        apply ContinuousLinearMap.ext
        intro v
        exact (hc.2 _ hab).1 v
      rw [heq] at hg
      exact hg
    have hl := locallyConstant_restrict_of_fderiv_zero hT
      (fun a ha ↦ (hd a ha).differentiableAt.differentiableWithinAt) (fun a ha ↦ (hd a ha).fderiv)
    exact hl.comp_continuous ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk
      (fun a ↦ ⟨a.val.property,a.property⟩))

end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology
open scoped unitInterval
namespace ProductBoxTopology
variable {A B X C D : Type*} [TopologicalSpace A] [TopologicalSpace B]
  [TopologicalSpace X] [TopologicalSpace C] [TopologicalSpace D]

lemma unique_paths [T2Space X] (atlas : Set (OpenPartialHomeomorph X (C × D)))
    (hcover : ∀ x : X, ∃ e ∈ atlas, x ∈ e.source)
    {F G : A × B → X} (hF : IsBox atlas F) (hG : IsBox atlas G)
    {a₀ a : A} {b₀ b : B} (α : Path a₀ a) (β : Path b₀ b)
    (hbottom : ∀ a, F (a,b₀)=G (a,b₀)) (hleft : ∀ b, F (a₀,b)=G (a₀,b)) :
    F (a,b)=G (a,b) := by
  have h := unique atlas hcover (hF.precomp α.continuous β.continuous)
    (hG.precomp α.continuous β.continuous)
    (fun s ↦ by simpa using hbottom (α s))
    (fun t ↦ by simpa using hleft (β t))
  simpa using congrFun h (1,1)

lemma unique_connected [T2Space X] [PathConnectedSpace A] [PathConnectedSpace B]
    (atlas : Set (OpenPartialHomeomorph X (C × D)))
    (hcover : ∀ x : X, ∃ e ∈ atlas, x ∈ e.source)
    {F G : A × B → X} (hF : IsBox atlas F) (hG : IsBox atlas G)
    (a₀ : A) (b₀ : B)
    (hbottom : ∀ a, F (a,b₀)=G (a,b₀)) (hleft : ∀ b, F (a₀,b)=G (a₀,b)) : F=G := by
  funext p
  exact unique_paths atlas hcover hF hG (PathConnectedSpace.somePath a₀ p.1)
    (PathConnectedSpace.somePath b₀ p.2) hbottom hleft

lemma pathConnected_Icc_unit {a b : I} (hab : a ≤ b) : PathConnectedSpace (Icc a b) := by
  refine ⟨⟨⟨a,le_rfl,hab⟩⟩,fun x y ↦ ?_⟩
  have hm (t : I) : Icc.convexComb x.val y.val t ∈ Icc a b := by
    constructor
    · change (a:ℝ) ≤ (1-(t:ℝ))*(x.val:ℝ)+(t:ℝ)*(y.val:ℝ)
      have hx : (a:ℝ) ≤ (x.val:ℝ) := x.property.1
      have hy : (a:ℝ) ≤ (y.val:ℝ) := y.property.1
      nlinarith [t.property.1,t.property.2]
    · change (1-(t:ℝ))*(x.val:ℝ)+(t:ℝ)*(y.val:ℝ) ≤ (b:ℝ)
      have hx : (x.val:ℝ) ≤ (b:ℝ) := x.property.2
      have hy : (y.val:ℝ) ≤ (b:ℝ) := y.property.2
      nlinarith [t.property.1,t.property.2]
  exact ⟨⟨⟨fun t ↦ ⟨Icc.convexComb x.val y.val t,hm t⟩,
    (Icc.continuous_convexComb x.val y.val).subtype_mk _⟩,
    by ext; simp,by ext; simp⟩⟩

end ProductBoxTopology
end
end

end OAI
