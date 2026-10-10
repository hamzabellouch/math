import Mathlib
import OAI.GroupTheory.PeriodicGroups.Frames.ExteriorComplex

namespace OAI

namespace SourceBurnside.Stability
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace HomologyEdge
variable {G : Type} [Group G] (C : ChainComplex (Rep ℚ G) ℕ)

abbrev Z (i : ℕ) := kernel (C.d (i+1) i)

def ontoCycles (i : ℕ) : C.X (i+2) ⟶ Z C i :=
  kernel.lift _ (C.d (i+2) (i+1)) (C.d_comp_d _ _ _)

lemma ontoCycles_epi (i : ℕ) (h : (C.sc' (i+2) (i+1) i).Exact) :
    Epi (ontoCycles C i) := h.epi_kernelLift

def cycleSequence (i : ℕ) : ShortComplex (Rep ℚ G) :=
  ShortComplex.mk (kernel.ι (C.d (i+2) (i+1))) (ontoCycles C i) (by
    apply (cancel_mono (kernel.ι (C.d (i+1) i))).mp
    simp [ontoCycles])

lemma cycleSequence_exact (i : ℕ) : (cycleSequence C i).Exact := by
  let φ : cycleSequence C i ⟶ ShortComplex.kernelSequence (C.d (i+2) (i+1)) :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := kernel.ι (C.d (i+1) i)
      comm₁₂ := by
        change 𝟙 _ ≫ kernel.ι _ = kernel.ι _ ≫ 𝟙 _
        exact (Category.id_comp _).trans (Category.comp_id _).symm
      comm₂₃ := by
        change 𝟙 _ ≫ C.d (i+2) (i+1) =
          kernel.lift _ (C.d (i+2) (i+1)) _ ≫ kernel.ι _
        exact (Category.id_comp _).trans (kernel.lift_ι _ _ _).symm }
  have : Epi φ.τ₁ := by
    change Epi (𝟙 (kernel (C.d (i+2) (i+1))))
    infer_instance
  have : IsIso φ.τ₂ := by
    change IsIso (𝟙 (C.X (i+2)))
    infer_instance
  have : Mono φ.τ₃ := by
    change Mono (kernel.ι (C.d (i+1) i))
    exact inferInstanceAs (Mono (kernel.ι (C.d (i+1) i)))
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr
    (ShortComplex.kernelSequence_exact _)

lemma cycleSequence_shortExact (i : ℕ) (h : (C.sc' (i+2) (i+1) i).Exact) :
    (cycleSequence C i).ShortExact := by
  have := ontoCycles_epi C i h
  exact { exact := cycleSequence_exact C i
          mono_f := by dsimp [cycleSequence]; infer_instance
          epi_g := by dsimp [cycleSequence]; infer_instance }

lemma zero_H0_of_epi {A B : Rep ℚ G} (f : A ⟶ B) [Epi f]
    (hA : IsZero (groupHomology A 0)) : IsZero (groupHomology B 0) := by
  have : Epi (groupHomology.map (MonoidHom.id G) f 0) := inferInstance
  exact IsZero.of_epi (groupHomology.map (MonoidHom.id G) f 0) hA

lemma isIso_H2_augmentation
    (hepi : Epi (C.d 1 0))
    (hex : ∀ i : Fin 3, (C.sc' (i.val+2) (i.val+1) i.val).Exact)
    (hacyc : ∀ i : Fin 3, ∀ q : ℕ, IsZero (groupHomology (C.X (i.val+2)) q)) :
    IsIso (groupHomology.map (MonoidHom.id G) (C.d 1 0) 2) := by
  have := hepi
  have := ontoCycles_epi C 2 (hex 2)
  have hz2 : IsZero (groupHomology (Z C 2) 0) :=
    zero_H0_of_epi (ontoCycles C 2) (hacyc 2 0)
  have hs1 := cycleSequence_shortExact C 1 (hex 1)
  have hz1 : IsZero (groupHomology (Z C 1) 1) :=
    (groupHomology.mapShortComplex₃_exact hs1 (i := 1) (j := 0) rfl).isZero_of_both_isZero
      (hacyc 1 1) hz2
  have := ontoCycles_epi C 1 (hex 1)
  have hz10 : IsZero (groupHomology (Z C 1) 0) :=
    zero_H0_of_epi (ontoCycles C 1) (hacyc 1 0)
  have hs0 := cycleSequence_shortExact C 0 (hex 0)
  have hz02 : IsZero (groupHomology (Z C 0) 2) :=
    (groupHomology.mapShortComplex₃_exact hs0 (i := 2) (j := 1) rfl).isZero_of_both_isZero
      (hacyc 0 2) hz1
  have hz01 : IsZero (groupHomology (Z C 0) 1) :=
    (groupHomology.mapShortComplex₃_exact hs0 (i := 1) (j := 0) rfl).isZero_of_both_isZero
      (hacyc 0 1) hz10
  have hs : (ShortComplex.kernelSequence (C.d 1 0)).ShortExact :=
    { exact := ShortComplex.kernelSequence_exact _
      mono_f := inferInstance
      epi_g := by change Epi (C.d 1 0); infer_instance }
  have : Mono (groupHomology.map (MonoidHom.id G) (C.d 1 0) 2) :=
    ((groupHomology.mapShortComplex₂ _ 2).exact_iff_mono
      (hz02.eq_zero_of_src _)).mp (groupHomology.mapShortComplex₂_exact hs 2)
  have : Epi (groupHomology.map (MonoidHom.id G) (C.d 1 0) 2) :=
    ((groupHomology.mapShortComplex₃ hs (i := 2) (j := 1) rfl).exact_iff_epi
      (hz01.eq_zero_of_tgt _)).mp (groupHomology.mapShortComplex₃_exact hs rfl)
  exact isIso_of_mono_of_epi _

end HomologyEdge
end
end SourceBurnside.Stability

namespace SourceBurnside.Stability.Frames
noncomputable section
open Classical CategoryTheory CategoryTheory.Limits Module
variable {V : Type} [LinearOrder V] (G : Type) [Group G] [MulAction G V]
variable {F W : Type} [DivisionRing F] [AddCommGroup W] [Module F W]
variable (ρ : V → W)
variable (hind : ∀(g : G) (s : Set V), LinearIndepOn F ρ s →
  LinearIndepOn F ρ ((g • ·) '' s))
def differentialRep (k : ℕ) : chainRep G (ρ := ρ) hind (k+1) ⟶ chainRep G (ρ := ρ) hind k :=
  Rep.ofHom
    { toLinearMap := differential (F := F) ρ k
      isIntertwining' := by
        intro g
        ext x
        change boundary V (labelMap (g • ·) x.val) = labelMap (g • ·) (boundary V x.val)
        exact boundary_labelMap (g • ·) x.val }

@[simp] lemma differentialRep_val (k : ℕ) (x : chainRep G (ρ := ρ) hind (k+1)) :
    ((differentialRep G ρ hind k).hom x).val = boundary V x.val := rfl

def repComplex : ChainComplex (Rep ℚ G) ℕ :=
  ChainComplex.of (chainRep G (ρ := ρ) hind) (differentialRep G ρ hind)
    (fun k => by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact boundary_boundary _)

@[simp] lemma repComplex_d (k : ℕ) : (repComplex G ρ hind).d (k+1) k =
    differentialRep G ρ hind k := by
  exact ChainComplex.of_d _ _ k

lemma repComplex_exact [FiniteDimensional F W]
    (hρ : Submodule.span F (Set.range ρ) = ⊤) (hrank : 10 < Module.finrank F W)
    (k : ℕ) (hk : k ≤ 2) :
    ((repComplex G ρ hind).sc' (k+2) (k+1) k).Exact := by
  apply (ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep ℚ G) (ModuleCat ℚ))).mp
  rw [CategoryTheory.ShortComplex.moduleCat_exact_iff]
  intro x hx
  change ((repComplex G ρ hind).d (k+1) k).hom x = 0 at hx
  rw [repComplex_d] at hx
  have hz : boundary V x.val = 0 := congrArg Subtype.val hx
  obtain ⟨y,hy,hdy⟩ := cycles_bound_upToThree ρ hρ hrank (k+1) (by omega) x.property hz
  refine ⟨⟨y,hy⟩,?_⟩
  change ((repComplex G ρ hind).d ((k+1)+1) (k+1)).hom ⟨y,hy⟩ = x
  rw [repComplex_d]
  exact Subtype.ext hdy

lemma differentialRep_epi [FiniteDimensional F W]
    (hρ : Submodule.span F (Set.range ρ) = ⊤) (hrank : 10 < Module.finrank F W) :
    Epi (differentialRep G ρ hind 0) := by
  apply (Rep.epi_iff_surjective _).mpr
  intro x
  obtain ⟨y,hy,hdy⟩ := degreeZero_lift ρ (coneSupply ρ hρ 10 hrank) x.property
  exact ⟨⟨y,hy⟩,Subtype.ext hdy⟩

lemma degreeZero_scalar (x : chains (F := F) ρ Set.univ 0) :
    x.val = (basis.repr x.val ∅) • basis (∅ : Finset V) := by
  rcases x with ⟨x,hx⟩
  change x = _
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t,ht,hc,hi,rfl⟩ := hx
    have he : t = ∅ := Finset.card_eq_zero.mp hc
    subst t
    simp only [Basis.repr_self,Finsupp.single_eq_same,one_smul]
  | zero => simp
  | add x y hx hy ihx ihy =>
    simp only [map_add,Finsupp.add_apply,add_smul]
    exact congrArg₂ (· + ·) ihx ihy
  | smul a x hx ih =>
    change x = (basis.repr x ∅) • basis ∅ at ih
    simpa only [map_smul,Finsupp.smul_apply,smul_eq_mul,smul_smul] using congrArg (a • ·) ih
def degreeZeroIso : chainRep G (ρ := ρ) hind 0 ≅ Rep.trivial ℚ G ℚ where
  hom := Rep.ofHom
    { toLinearMap := ((Finsupp.lapply ∅).comp basis.repr.toLinearMap).domRestrict _
      isIntertwining' := by
        intro g
        ext x
        change basis.repr (labelMap (g • ·) x.val) ∅ = basis.repr x.val ∅
        conv_lhs => rw [degreeZero_scalar ρ x]
        have hb : labelMap (g • ·) (basis (∅ : Finset V)) = basis ∅ := by simp
        simp only [map_smul,hb,Basis.repr_self,Finsupp.smul_apply,Finsupp.single_eq_same,smul_eq_mul,mul_one] }
  inv := Rep.ofHom
    { toLinearMap :=
        { toFun c := ⟨c • basis (∅ : Finset V), (chains (F := F) ρ Set.univ 0).smul_mem c
            (basis_mem_chains ρ ∅ (by simp) (by simp [LinearIndepOn]))⟩
          map_add' c d := Subtype.ext (add_smul _ _ _)
          map_smul' c d := Subtype.ext (mul_smul _ _ _) }
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro c
        apply Subtype.ext
        change c • basis ∅ = labelMap (g • ·) (c • basis ∅)
        simp }
  hom_inv_id := by ext x; exact Subtype.ext (degreeZero_scalar ρ x).symm
  inv_hom_id := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro c
    change basis.repr (c • basis (∅ : Finset V)) ∅ = c
    simp only [map_smul, Basis.repr_self,Finsupp.smul_apply,Finsupp.single_eq_same,smul_eq_mul,mul_one]

end

noncomputable section
open Classical Module CategoryTheory
variable {V : Type} [LinearOrder V]
variable {F W : Type} [DivisionRing F] [AddCommGroup W] [Module F W]
variable (ρ : V → W)

def Index (k : ℕ) := {t : Finset V // t.card=k ∧ LinearIndepOn F ρ (t : Set V)}

lemma span_index (k : ℕ) :
    Submodule.span ℚ (Set.range (fun t : Index (F := F) ρ k => basis t.val)) =
      chains (F := F) ρ Set.univ k := by
  congr 1
  ext z
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨t.val,Set.subset_univ _,t.property.1,t.property.2,rfl⟩
  · rintro ⟨t,ht,hc,hi,rfl⟩
    exact ⟨⟨t,hc,hi⟩,rfl⟩

def frameBasis (k : ℕ) : Basis (Index (F := F) ρ k) ℚ (chains (F := F) ρ Set.univ k) :=
  (Basis.span ((basis (V := V)).linearIndependent.comp (fun t : Index (F := F) ρ k => t.val)
    Subtype.val_injective)).map (LinearEquiv.ofEq _ _ (span_index ρ k))

@[simp] lemma frameBasis_val (k : ℕ) (t : Index (F := F) ρ k) :
    (frameBasis ρ k t).val = basis t.val := by
  simp [frameBasis,Basis.span_apply]

variable (G : Type) [Group G] [MulAction G V]
variable (hind : ∀(g : G) (s : Set V), LinearIndepOn F ρ s →
  LinearIndepOn F ρ ((g • ·) '' s))

@[instance_reducible] def indexAction (k : ℕ) : MulAction G (Index (F := F) ρ k) where
  smul g t := ⟨t.val.image (g • ·), by
    exact ⟨(Finset.card_image_of_injective _ (MulAction.injective g)).trans t.property.1,
      by simpa only [Finset.coe_image] using hind g _ t.property.2⟩⟩
  one_smul t := Subtype.ext (by
    change t.val.image (fun v => (1 : G) • v) = t.val
    simp)
  mul_smul g h t := Subtype.ext (by
    change t.val.image (fun v => (g*h) • v) =
      (t.val.image (fun v => h • v)).image (fun v => g • v)
    simp [Finset.image_image,mul_smul,Function.comp_def])

@[simp] lemma indexAction_val (k : ℕ) (g : G) (t : Index (F := F) ρ k) :
    letI := indexAction ρ G hind k
    (g • t).val = t.val.image (g • ·) := rfl

lemma frame_action_monomial (k : ℕ) (g : G) (t : Index (F := F) ρ k) :
    letI := indexAction ρ G hind k
    ∃c : ℚˣ, (chainRep G (ρ := ρ) hind k).ρ g (frameBasis ρ k t) =
      c.val • frameBasis ρ k (g • t) := by
  let := indexAction ρ G hind k
  obtain ⟨c,hc,he⟩ := labelMap_basis (g • ·) (MulAction.injective g) t.val
  refine ⟨Units.mk0 c hc,?_⟩
  apply Subtype.ext
  change labelMap (g • ·) (frameBasis ρ k t).val = _
  simpa only [frameBasis_val,Submodule.coe_smul,Units.val_mk0,indexAction_val] using he

end

noncomputable section
open Classical Module CategoryTheory
variable {V W U : Type}

def labelHom (f : V → W) : Ambient V →ₐ[ℚ] Ambient W :=
  ExteriorAlgebra.map (Finsupp.lmapDomain ℚ ℚ f)

@[simp] lemma labelHom_vertex (f : V → W) (v : V) :
    labelHom f (vertex V v) = vertex W (f v) := by
  simp [labelHom,vertex,Finsupp.lmapDomain_apply]

@[simp] lemma labelHom_id : labelHom (V := V) id = AlgHom.id ℚ _ := by
  simp [labelHom,Finsupp.lmapDomain_id]

lemma labelHom_comp (f : V → W) (g : W → U) :
    labelHom (g ∘ f) = (labelHom g).comp (labelHom f) := by
  simp [labelHom,Finsupp.lmapDomain_comp]

variable [LinearOrder V] [LinearOrder W] [LinearOrder U]

lemma labelHom_basis (f : V → W) (hf : Function.Injective f) (s : Finset V) :
    ∃c : ℚ, c≠0 ∧ labelHom f (basis s) = c • basis (s.image f) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1,one_ne_zero,by simp⟩
  | @insert v s hv ih =>
    obtain ⟨c,hc,he⟩ := basis_insert_inverse v s hv
    obtain ⟨d,hd,hde⟩ := ih
    have hv' : f v ∉ s.image f := by simpa only [Finset.mem_image,hf.eq_iff,exists_eq_right] using hv
    obtain ⟨e,he0,hee⟩ := vertex_mul_basis (f v) (s.image f) hv'
    refine ⟨c*(d*e),mul_ne_zero hc (mul_ne_zero hd he0),?_⟩
    rw [he,map_smul,map_mul,labelHom_vertex,hde,mul_smul_comm,hee,smul_smul,smul_smul,
      Finset.image_insert]
    simp only [mul_assoc]

def labelEquiv (e : V ≃ W) : Ambient V ≃ₐ[ℚ] Ambient W :=
  { labelHom e with
    invFun := labelHom e.symm
    left_inv x := by
      have h := congrArg (fun f : Ambient V →ₐ[ℚ] Ambient V => f x) (labelHom_comp e e.symm)
      simpa using h.symm
    right_inv x := by
      have h := congrArg (fun f : Ambient W →ₐ[ℚ] Ambient W => f x) (labelHom_comp e.symm e)
      simpa using h.symm }

variable {F P Q : Type} [DivisionRing F] [AddCommGroup P] [Module F P]
variable [AddCommGroup Q] [Module F Q] (ρ : V → P) (σ : W → Q)
variable (e : V ≃ W)
variable (hi : ∀s : Set V, LinearIndepOn F ρ s → LinearIndepOn F σ (e '' s))

include hi in
lemma labelHom_chains (k : ℕ) {x : Ambient V} (hx : x∈chains (F := F) ρ Set.univ k) :
    labelHom e x∈chains (F := F) σ Set.univ k := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s,hs,hcard,hsind,rfl⟩ := hx
    obtain ⟨c,hc,he⟩ := labelHom_basis e e.injective s
    rw [he]
    apply (chains (F := F) σ Set.univ k).smul_mem c
    have hc : (s.image e).card=k := (Finset.card_image_of_injective _ e.injective).trans hcard
    rw [←hc]
    exact basis_mem_chains (F := F) σ _ (Set.subset_univ _) (by simpa using hi _ hsind)
  | zero => simp
  | add x y hx hy ihx ihy => simpa using (chains (F := F) σ Set.univ k).add_mem ihx ihy
  | smul a x hx ihx => simpa using (chains (F := F) σ Set.univ k).smul_mem a ihx

def chainLinear (k : ℕ) : chains (F := F) ρ Set.univ k →ₗ[ℚ] chains (F := F) σ Set.univ k where
  toFun x := ⟨labelHom e x.val,labelHom_chains ρ σ e hi k x.property⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

variable (hi' : ∀s : Set W, LinearIndepOn F σ s → LinearIndepOn F ρ (e.symm '' s))

def chainEquiv (k : ℕ) : chains (F := F) ρ Set.univ k ≃ₗ[ℚ] chains (F := F) σ Set.univ k :=
  { chainLinear ρ σ e hi k with
    invFun := chainLinear σ ρ e.symm hi' k
    left_inv x := Subtype.ext ((labelEquiv e).left_inv x.val)
    right_inv x := Subtype.ext ((labelEquiv e).right_inv x.val) }

variable {G H : Type} [Group G] [Group H] [MulAction G V] [MulAction H W]
variable (hind : ∀g : G, ∀s : Set V, LinearIndepOn F ρ s → LinearIndepOn F ρ ((g • ·) '' s))
variable (hind' : ∀g : H, ∀s : Set W, LinearIndepOn F σ s → LinearIndepOn F σ ((g • ·) '' s))
variable (eg : G ≃* H) (he : ∀(g : G) (v : V), e (g • v) = eg g • e v)

include he in
lemma chainEquiv_intertwining (k : ℕ) (g : G) :
    (chainEquiv ρ σ e hi hi' k).toLinearMap.comp ((chainRep G (ρ := ρ) hind k).ρ g) =
      ((chainRep H (ρ := σ) hind' k).ρ (eg g)).comp (chainEquiv ρ σ e hi hi' k).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change labelHom e (labelHom (g • ·) x.val) = labelHom (eg g • ·) (labelHom e x.val)
  have he' : (e ∘ (g • ·)) = (eg g • ·) ∘ e := funext (he g)
  have hh := congrArg (fun f : V → W => labelHom f) he'
  rw [labelHom_comp,labelHom_comp] at hh
  exact congrArg (fun f : Ambient V →ₐ[ℚ] Ambient W => f x.val) hh

def chainHomologyIso (k n : ℕ) :
    groupHomology (chainRep G (ρ := ρ) hind k) n ≅
      groupHomology (chainRep H (ρ := σ) hind' k) n :=
  groupHomology.mapIso eg (chainEquiv ρ σ e hi hi' k)
    (chainEquiv_intertwining ρ σ e hi hi' hind hind' eg he k) n

end
end SourceBurnside.Stability.Frames

end OAI
