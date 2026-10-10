import Mathlib
import OAI.CategoryTheory.Thomason.AtomFibers

namespace OAI

/-! Top Sequences. -/

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory
open CategoryTheory

namespace Functor
variable {X : OmegaCategory.{u}} {Y : OmegaCategory.{v}}

def injectiveImage (F : Functor X Y) (hF : Function.Injective F.map) : Subcategory Y where
  carrier := Set.range F.map
  source_mem k := by
    rintro x ⟨a,rfl⟩
    exact ⟨X.source k a,F.map_source k a⟩
  target_mem k := by
    rintro x ⟨a,rfl⟩
    exact ⟨X.target k a,F.map_target k a⟩
  comp_mem k := by
    rintro x y h ⟨a,rfl⟩ ⟨b,rfl⟩
    have hab : X.target k a = X.source k b := hF (by
      rw [F.map_target,F.map_source]; exact h)
    exact ⟨X.comp k a b hab,F.map_comp k a b hab h⟩

end Functor
namespace Subcategory
variable {X : OmegaCategory.{u}} {Y : OmegaCategory.{v}}

def preimage (S : Subcategory Y) (F : Functor X Y) : Subcategory X where
  carrier := F.map ⁻¹' S.carrier
  source_mem k := by
    intro x hx
    change F.map (X.source k x) ∈ S.carrier
    rw [F.map_source]
    exact S.source_mem k hx
  target_mem k := by
    intro x hx
    change F.map (X.target k x) ∈ S.carrier
    rw [F.map_target]
    exact S.target_mem k hx
  comp_mem k := by
    intro x y h hx hy
    change F.map (X.comp k x y h) ∈ S.carrier
    rw [F.map_comp k x y h (F.map_composable h)]
    exact S.comp_mem k _ hx hy

end Subcategory
end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
variable {X Y : OmegaCategory.{u}}

lemma mapCell_injective (F : X ⟶ Y) (hF : Function.Injective F.map) :
    Function.Injective (mapCell F) := by
  intro x y h
  apply Subtype.ext
  funext n
  apply OmegaCategory.Functor.ext
  funext z
  apply hF
  exact congrArg (fun c => (eval n c).map z) h

lemma ofMap_in_image_iff (S : Subcategory Y) {n : ℕ}
    (F : (K.{u} n).nu ⟶ Y) :
    ofMap F ∈ (OmegaCategory.Functor.injectiveImage (mapFunctor S.inclusion)
      (mapCell_injective S.inclusion S.inclusion_injective)).carrier ↔
    ∀ t, F.map t ∈ S.carrier := by
  constructor
  · rintro ⟨x,hx⟩ t
    have h := congrArg (fun c => (eval n c).map t) hx
    rw [eval_ofMap_self] at h
    exact h ▸ ((eval n x).map t).property
  · intro h
    refine ⟨ofMap (S.lift F h),?_⟩
    change mapCell S.inclusion (ofMap (S.lift F h)) = ofMap F
    rw [mapCell_ofMap,S.lift_inclusion]

def cylinderSubcategory (S : Subcategory (tensorFunctor.obj X)) : Subcategory X :=
  (OmegaCategory.Functor.injectiveImage (mapFunctor S.inclusion)
    (mapCell_injective S.inclusion S.inclusion_injective)).preimage (tensorUnit X)

lemma mem_cylinderSubcategory_iff (S : Subcategory (tensorFunctor.obj X))
    (n : ℕ) (x : X.Cells n) :
    x.val ∈ (cylinderSubcategory S).carrier ↔ ∀ t, (generatorCylinder n x).map t ∈ S.carrier := by
  change tensorUnitCell x.val ∈ (OmegaCategory.Functor.injectiveImage (mapFunctor S.inclusion)
    (mapCell_injective S.inclusion S.inclusion_injective)).carrier ↔ _
  erw [tensorUnitCell_of_bounded n x,ofMap_in_image_iff]
  rfl

variable {M : DirectedComplex.{u}}

lemma endpoint_mem_of_atoms (A : RankedAtoms.{u,v} M)
    (S : Subcategory (tensorFunctor.obj M.nu))
    (h : ∀ a b, ((tensorEndpoint a).app M.nu).map (A.atom b) ∈ S.carrier)
    (a : Bool) (x : M.nu.Cell) : ((tensorEndpoint a).app M.nu).map x ∈ S.carrier := by
  induction A.all_atomic x with
  | atom b => exact h a b
  | compose k x y hxy hx hy ihx ihy =>
    change ((tensorEndpoint a).app M.nu).map (M.nu.comp k x y hxy) ∈ S.carrier
    erw [((tensorEndpoint a).app M.nu).map_comp k x y hxy
      (((tensorEndpoint a).app M.nu).map_composable hxy)]
    exact S.comp_mem k _ ihx ihy

theorem tensor_mem_of_atoms (A : RankedAtoms.{u,v} M)
    (S : Subcategory (tensorFunctor.obj M.nu))
    (hend : ∀ a b, ((tensorEndpoint a).app M.nu).map (A.atom b) ∈ S.carrier)
    (hvert : ∀ b, verticalCell (A.dim b) ⟨A.atom b,A.bounded b⟩ ∈ S.carrier) :
    ∀ z, z ∈ S.carrier := by
  have he := endpoint_mem_of_atoms A S hend
  have hbounded (n : ℕ) (x : M.nu.Cell) (hx : M.nu.source n x = x) :
      x ∈ (cylinderSubcategory S).carrier := by
    induction n using Nat.strong_induction_on generalizing x with
    | h n ih =>
      have hpaste := A.bounded_pasting n x hx
      clear hx
      induction hpaste with
      | atom b hb =>
        apply (mem_cylinderSubcategory_iff S (A.dim b) ⟨A.atom b,A.bounded b⟩).mpr
        intro t
        apply GrayRecursive.generated (A.dim b)
          (fun z => (generatorCylinder (X := M.nu) (A.dim b) ⟨A.atom b,A.bounded b⟩).map z ∈ S.carrier)
        · intro a s
          erw [generatorCylinder_endpoint]
          exact he a _
        · intro s
          obtain ⟨p,a,hp,rfl⟩ := table_classification s
          erw [generatorCylinder_vertical_face]
          by_cases hpd : p = A.dim b
          · subst p
            have hf : M.nu.face (A.dim b) a (A.atom b) = A.atom b :=
              M.nu.face_of_fixed (A.bounded b) le_rfl a
            erw [verticalCell_eq_of_value _ (⟨A.atom b,A.bounded b⟩ : M.nu.Cells (A.dim b)) hf]
            exact hvert b
          · have hpn : p < n := by omega
            let y : M.nu.Cells p := ⟨M.nu.face p a (A.atom b), by
              cases a
              · exact M.nu.source_source_self p _
              · exact M.nu.source_target_self p _⟩
            have hy := ih p hpn y.val y.property
            exact (mem_cylinderSubcategory_iff S p y).mp hy (verticalTable (topTable p))
        · intro k s t hst hs ht
          erw [(generatorCylinder (X := M.nu) (A.dim b) ⟨A.atom b,A.bounded b⟩).map_comp k s t hst
            ((generatorCylinder (X := M.nu) (A.dim b) ⟨A.atom b,A.bounded b⟩).map_composable hst)]
          exact S.comp_mem k _ hs ht
      | compose k hk x y hxy hpx hpy ihx ihy =>
        exact (cylinderSubcategory S).comp_mem k hxy ihx ihy
  have hc (x : M.nu.Cell) : x ∈ (cylinderSubcategory S).carrier := by
    obtain ⟨n,hn⟩ := M.nu.finite_dimension x
    exact hbounded n x hn
  apply tensor_cells_induction (fun z => z ∈ S.carrier)
  · exact he
  · intro n x
    exact (mem_cylinderSubcategory_iff S n x).mp (hc x.val) (verticalTable (topTable n))
  · exact fun k x hx => S.source_mem k hx
  · exact fun k x hx => S.target_mem k hx
  · exact fun k x y h hx hy => S.comp_mem k h hx hy

theorem tensor_functor_ext_atoms (A : RankedAtoms.{u,v} M)
    {F G : tensorFunctor.obj M.nu ⟶ Y}
    (hend : ∀ a b, F.map (((tensorEndpoint a).app M.nu).map (A.atom b)) =
      G.map (((tensorEndpoint a).app M.nu).map (A.atom b)))
    (hvert : ∀ b, F.map (verticalCell (A.dim b) ⟨A.atom b,A.bounded b⟩) =
      G.map (verticalCell (A.dim b) ⟨A.atom b,A.bounded b⟩)) : F = G := by
  let S : Subcategory (tensorFunctor.obj M.nu) := {
    carrier := {x | F.map x = G.map x}
    source_mem := by
      intro k x h
      change F.map _ = G.map _
      rw [F.map_source,G.map_source,h]
    target_mem := by
      intro k x h
      change F.map _ = G.map _
      rw [F.map_target,G.map_target,h]
    comp_mem := by
      intro k x y h hx hy
      change F.map _ = G.map _
      rw [F.map_comp k x y h (F.map_composable h),
        G.map_comp k x y h (G.map_composable h)]
      change F.map x = G.map x at hx
      change F.map y = G.map y at hy
      congr 1 }
  exact OmegaCategory.Functor.ext (funext (tensor_mem_of_atoms A S hend hvert))
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains.Prism.Word
open DirectedComplex DirectedComplex.Table

def coefficient {N : ℕ} (w : Word N) (p : ℕ) :
    (complex (Fin (N+1))).Chain p →+ ℤ where
  toFun x := x.val w.val
  map_add' _ _ := rfl
  map_zero' := rfl

def rankedAtoms (N : ℕ) : RankedAtoms (complex (Fin (N+1))) where
  Index := Word N
  finite := Fintype.ofFinite (Word N)
  dim := Word.dim
  rank := Word.rank
  atom := Word.atom
  bounded := Word.atom_dim
  coefficient := Word.coefficient
  homogeneous _ _ _ := Word.dim_eq_of_coefficient _ _
  ext _ := Word.chain_ext
  positive _ := Word.chain_positive
  top b c e := by
    classical
    change (b.atom.row b.dim e).val c.val = _
    rw [b.atom_top e]
    by_cases h : b = c
    · subst c; simp
    · rw [ite_eq_right h,Finsupp.single_eq_of_ne (fun he => h (Subtype.ext he.symm))]
  ranked := Word.atom_rank

def ofOrderIso {N : ℕ} {P : Type u} [LinearOrder P] (e : Fin (N+1) ≃o P) :
    RankedAtoms (complex P) :=
  (rankedAtoms N).transport (complexMap (e : Fin (N+1) →o P))
    (complexMap (e.symm : P →o Fin (N+1)))
    (complexMap_orderIso_inverse e) (complexMap_orderIso_inverse e.symm)
end Thomason.NormalizedChains.Prism.Word

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex Table OmegaCategory NormalizedChains

lemma chainComparison_endpoint_basis {N : ℕ} {P : Type u} [LinearOrder P]
    (e : Fin (N+1) ≃o P) (a : Bool) (b : (Prism.Word.ofOrderIso e).Index) :
    (chainComparison (NormalizedChains.complex P)).map
      (((tensorEndpoint a).app (NormalizedChains.complex P).nu).map
        ((Prism.Word.ofOrderIso e).atom b)) =
      (Prism.Basis.ofOrderIso e).atom (.endpoint a b) := by
  rw [chainComparison_endpoint_apply]
  exact (congrArg (fun h : Hom (NormalizedChains.complex (Fin (N+1)))
      (NormalizedChains.complex P).cylinder => h.table b.atom)
    ((complexMap (e : Fin (N+1) →o P)).cylinder_endpoint a)).symm

lemma chainComparison_vertical_basis {N : ℕ} {P : Type u} [LinearOrder P]
    (e : Fin (N+1) ≃o P) (b : (Prism.Word.ofOrderIso e).Index) :
    (chainComparison (NormalizedChains.complex P)).map
      (verticalCell ((Prism.Word.ofOrderIso e).dim b)
        ⟨(Prism.Word.ofOrderIso e).atom b,(Prism.Word.ofOrderIso e).bounded b⟩) =
      (Prism.Basis.ofOrderIso e).atom (.vertical b) := by
  erw [chainComparison_verticalCell ((Prism.Word.ofOrderIso e).dim b)
    ⟨(Prism.Word.ofOrderIso e).atom b,(Prism.Word.ofOrderIso e).bounded b⟩]
  exact (verticalTable_natural (complexMap (e : Fin (N+1) →o P)) b.atom).symm

lemma chainComparison_section_is_inverse {N : ℕ} {P : Type u} [LinearOrder P]
    (e : Fin (N+1) ≃o P)
    (G : (NormalizedChains.complex P).cylinder.nu ⟶
      tensorFunctor.obj (NormalizedChains.complex P).nu)
    (hG : G ≫ chainComparison (NormalizedChains.complex P) = 𝟙 _) :
    chainComparison (NormalizedChains.complex P) ≫ G = 𝟙 _ := by
  let M := NormalizedChains.complex P
  let A := Prism.Word.ofOrderIso e
  let B := Prism.Basis.ofOrderIso e
  have hsection (t : M.cylinder.nu.Cell) :
      (chainComparison M).map (G.map t) = t :=
    congrArg (fun f : M.cylinder.nu ⟶ M.cylinder.nu => f.map t) hG
  apply tensor_functor_ext_atoms A
  · intro a b
    change G.map ((chainComparison M).map _) = _
    apply chainComparison_atom_fiber_subsingleton B (.endpoint a b)
    · rw [hsection]
      exact chainComparison_endpoint_basis e a b
    · exact chainComparison_endpoint_basis e a b
  · intro b
    change G.map ((chainComparison M).map _) = _
    apply chainComparison_atom_fiber_subsingleton B (.vertical b)
    · rw [hsection]
      exact chainComparison_vertical_basis e b
    · exact chainComparison_vertical_basis e b

lemma chainComparison_finiteSimplex_isIso_of_section (P : Type u) [LinearOrder P] [Finite P]
    (G : (NormalizedChains.complex P).cylinder.nu ⟶
      tensorFunctor.obj (NormalizedChains.complex P).nu)
    (hG : G ≫ chainComparison (NormalizedChains.complex P) = 𝟙 _) :
    IsIso (chainComparison (NormalizedChains.complex P)) := by
  let := Fintype.ofFinite P
  by_cases he : Fintype.card P = 0
  · let : IsEmpty P := Fintype.card_eq_zero_iff.mp he
    infer_instance
  · have hp : Fintype.card P = (Fintype.card P - 1) + 1 := by omega
    let e := Fintype.orderIsoFinOfCardEq P hp
    exact ⟨⟨G,chainComparison_section_is_inverse e G hG,hG⟩⟩

theorem fullMain_of_standardSimplex_sections
    (h : ∀ m : ℕ, ∃ G :
      (NormalizedChains.complex (ULift.{u} (Fin (m+3)))).cylinder.nu ⟶
        tensorFunctor.obj (NormalizedChains.complex (ULift.{u} (Fin (m+3)))).nu,
      G ≫ chainComparison (NormalizedChains.complex (ULift.{u} (Fin (m+3)))) = 𝟙 _) :
    FullMain.{u} := by
  apply fullMain_of_standardSimplexComparison_isIso
  intro m
  obtain ⟨G,hG⟩ := h m
  exact chainComparison_finiteSimplex_isIso_of_section _ G hG
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex Table OmegaCategory GlobeComplex
variable {M : DirectedComplex.{u}} (A : RankedAtoms.{u,v} M)

inductive AtomicLayers (n : ℕ) : (tensorFunctor.obj M.nu).Cell → Prop
  | endpoint (a : Bool) (b : A.Index) (hb : A.dim b ≤ n) :
      AtomicLayers n (((tensorEndpoint a).app M.nu).map (A.atom b))
  | vertical (b : A.Index) (hb : A.dim b < n) :
      AtomicLayers n (verticalCell (A.dim b) ⟨A.atom b,A.bounded b⟩)
  | lower (k : ℕ) (hk : k < n) (z : (tensorFunctor.obj M.nu).Cell)
      (hz : (tensorFunctor.obj M.nu).source k z = z) : AtomicLayers n z
  | compose (k : ℕ) (hk : k < n) (x y)
      (h : (tensorFunctor.obj M.nu).target k x = (tensorFunctor.obj M.nu).source k y) :
      AtomicLayers n x → AtomicLayers n y →
        AtomicLayers n ((tensorFunctor.obj M.nu).comp k x y h)

namespace AtomicLayers
variable {A} {n : ℕ}

lemma bounded {z : (tensorFunctor.obj M.nu).Cell} (h : AtomicLayers A n z) :
    (tensorFunctor.obj M.nu).source n z = z := by
  induction h with
  | endpoint a b hb =>
    erw [endpoint_source]
    exact congrArg ((tensorEndpoint a).app M.nu).map
      (M.nu.source_fixed_upwards hb (A.bounded b))
  | vertical b hb =>
    exact (tensorFunctor.obj M.nu).source_fixed_upwards (by omega : A.dim b+1 ≤ n)
      (verticalCell_bounded _ _)
  | lower k hk z hz => exact (tensorFunctor.obj M.nu).source_fixed_upwards hk.le hz
  | compose k hk x y h hx hy ihx ihy =>
    erw [(tensorFunctor.obj M.nu).source_comp_gt n k hk _ _ _
      ((tensorFunctor.obj M.nu).source_composable hk h)]
    exact (tensorFunctor.obj M.nu).comp_congr_cells k _ _ ihx ihy

def subcategory (A : RankedAtoms.{u,v} M) (n : ℕ) :
    Subcategory (tensorFunctor.obj M.nu) where
  carrier := {z | AtomicLayers A n z}
  source_mem k := by
    intro z hz
    change AtomicLayers A n ((tensorFunctor.obj M.nu).source k z)
    by_cases hk : k < n
    · exact .lower k hk _ ((tensorFunctor.obj M.nu).source_source_self k z)
    · rw [(tensorFunctor.obj M.nu).source_fixed_upwards (by omega : n ≤ k) hz.bounded]
      exact hz
  target_mem k := by
    intro z hz
    change AtomicLayers A n ((tensorFunctor.obj M.nu).target k z)
    by_cases hk : k < n
    · exact .lower k hk _ ((tensorFunctor.obj M.nu).source_target_self k z)
    · rw [(tensorFunctor.obj M.nu).target_eq_self_of_source_eq_self
        ((tensorFunctor.obj M.nu).source_fixed_upwards (by omega : n ≤ k) hz.bounded)]
      exact hz
  comp_mem k := by
    intro x y h hx hy
    change AtomicLayers A n ((tensorFunctor.obj M.nu).comp k x y h)
    by_cases hk : k < n
    · exact .compose k hk x y h hx hy
    · rw [(tensorFunctor.obj M.nu).comp_of_left_source_fixed k x y h
        ((tensorFunctor.obj M.nu).source_fixed_upwards (by omega : n ≤ k) hx.bounded)]
      exact hy

lemma endpoint_cell (a : Bool) (x : M.nu.Cell) (hx : M.nu.source n x = x) :
    AtomicLayers A n (((tensorEndpoint a).app M.nu).map x) := by
  have h := A.bounded_pasting n x hx
  clear hx
  induction h with
  | atom b hb => exact .endpoint a b hb
  | compose k hk x y h hpx hpy ihx ihy =>
    change AtomicLayers A n (((tensorEndpoint a).app M.nu).map (M.nu.comp k x y h))
    erw [((tensorEndpoint a).app M.nu).map_comp k x y h
      (((tensorEndpoint a).app M.nu).map_composable h)]
    exact .compose k hk _ _ _ ihx ihy

lemma cylinder_atom (b : A.Index) (hb : A.dim b < n) :
    A.atom b ∈ (cylinderSubcategory (subcategory A n)).carrier := by
  apply (mem_cylinderSubcategory_iff (subcategory A n) (A.dim b)
    ⟨A.atom b,A.bounded b⟩).mpr
  intro t
  apply GrayRecursive.generated (A.dim b)
    (fun z => (generatorCylinder (X := M.nu) (A.dim b)
      ⟨A.atom b,A.bounded b⟩).map z ∈ (subcategory A n).carrier)
  · intro a s
    erw [generatorCylinder_endpoint]
    apply endpoint_cell
    obtain ⟨p,e,hp,rfl⟩ := table_classification s
    erw [← (GlobeComplex.lift (C := M.nu) (A.atom b) (A.bounded b)).map_source]
    apply congrArg (GlobeComplex.lift (C := M.nu) (A.atom b) (A.bounded b)).map
    change truncate n false (truncate p e (topTable (A.dim b))) = _
    rw [truncate_truncate,ite_eq_right (by omega : ¬ n < p)]
  · intro s
    obtain ⟨p,e,hp,rfl⟩ := table_classification s
    erw [generatorCylinder_vertical_face]
    by_cases he : p = A.dim b
    · subst p
      have hf : M.nu.face (A.dim b) e (A.atom b) = A.atom b :=
        M.nu.face_of_fixed (A.bounded b) le_rfl e
      erw [verticalCell_eq_of_value _ (⟨A.atom b,A.bounded b⟩ : M.nu.Cells (A.dim b)) hf]
      exact AtomicLayers.vertical b hb
    · exact AtomicLayers.lower (p+1) (by omega) _ (verticalCell_bounded _ _)
  · intro k s t h hs ht
    erw [(generatorCylinder (X := M.nu) (A.dim b) ⟨A.atom b,A.bounded b⟩).map_comp k s t h
      ((generatorCylinder (X := M.nu) (A.dim b) ⟨A.atom b,A.bounded b⟩).map_composable h)]
    exact (subcategory A n).comp_mem k _ hs ht

lemma vertical_cell (r : ℕ) (hr : r < n) (x : M.nu.Cells r) :
    AtomicLayers A n (verticalCell r x) := by
  have hh (y : M.nu.Cell) (hp : A.BoundedPasting r y) :
      y ∈ (cylinderSubcategory (subcategory A n)).carrier := by
    induction hp with
    | atom b hb => exact cylinder_atom b (by omega)
    | compose k hk a b h hpa hpb iha ihb =>
      exact (cylinderSubcategory (subcategory A n)).comp_mem k h iha ihb
  exact (mem_cylinderSubcategory_iff (subcategory A n) r x).mp
    (hh x.val (A.bounded_pasting r x.val x.property))
    (verticalTable (topTable r))

end AtomicLayers

theorem tensor_atomic_layers (n : ℕ) (z : (tensorFunctor.obj M.nu).Cell)
    (hz : (tensorFunctor.obj M.nu).source n z = z) : AtomicLayers A n z := by
  apply tensor_bounded_cells_induction n (AtomicLayers A n)
    (fun a x hx => AtomicLayers.endpoint_cell a x hx)
    (fun r hr x => AtomicLayers.vertical_cell r hr x)
    (fun r hr x hx => .lower r hr x hx)
    (fun r hr x y _ _ h hx hy => .compose r hr x y h hx hy) z hz
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

variable (C : OmegaCategory.{u}) (n : ℕ) (G : C.Cell → Prop)

inductive Whisker : C.Cell → Prop
  | generator (x) : G x → C.source (n+1) x = x → Whisker x
  | left (k : ℕ) (hk : k < n) (a x)
      (ha : C.source n a = a) (h : C.target k a = C.source k x) :
      Whisker x → Whisker (C.join k a x)
  | right (k : ℕ) (hk : k < n) (x a)
      (ha : C.source n a = a) (h : C.target k x = C.source k a) :
      Whisker x → Whisker (C.join k x a)

inductive TopSequence : C.Cell → Prop
  | lower (x) : C.source n x = x → TopSequence x
  | single (x) : C.Whisker n G x → TopSequence x
  | compose (x y) (h : C.target n x = C.source n y) :
      TopSequence x → TopSequence y → TopSequence (C.join n x y)

variable {C n G}
namespace Whisker

lemma bounded {x : C.Cell} (h : C.Whisker n G x) : C.source (n+1) x = x := by
  induction h with
  | generator x hg hx => exact hx
  | left k hk a x ha h hx ih =>
    rw [C.join_source_gt (n+1) k a x (by omega) h,
      C.source_fixed_upwards (Nat.le_succ n) ha,ih]
  | right k hk x a ha h hx ih =>
    rw [C.join_source_gt (n+1) k x a (by omega) h,
      ih,C.source_fixed_upwards (Nat.le_succ n) ha]

end Whisker
namespace TopSequence

lemma bounded {x : C.Cell} (h : C.TopSequence n G x) : C.source (n+1) x = x := by
  induction h with
  | lower x hx => exact C.source_fixed_upwards (Nat.le_succ n) hx
  | single x hx => exact hx.bounded
  | compose x y h hx hy ihx ihy =>
    rw [C.join_source_gt (n+1) n x y (by omega) h,ihx,ihy]

lemma whisker_left {x : C.Cell} (hx : C.TopSequence n G x)
    (k : ℕ) (hk : k < n) (a : C.Cell) (ha : C.source n a = a)
    (h : C.target k a = C.source k x) : C.TopSequence n G (C.join k a x) := by
  induction hx with
  | lower x hx =>
    apply TopSequence.lower
    rw [C.join_source_gt n k a x hk h,ha,hx]
  | single x hx => exact .single _ (.left k hk a x ha h hx)
  | compose x y hxy hx hy ihx ihy =>
    have hax : C.target k a = C.source k x := by
      rw [C.join_source_le k n x y hk.le hxy] at h
      exact h
    have hay : C.target k a = C.source k y := by
      have he := congrArg (C.source k) hxy
      simp only [C.source_target,ite_eq_left hk,C.source_source,min_eq_left hk.le] at he
      exact hax.trans he
    rw [C.join_whisker_left k n hk a x y ha hxy hax hay]
    refine .compose _ _ ?_ (ihx hax) (ihy hay)
    rw [C.join_target_gt n k a x hk hax,C.join_source_gt n k a y hk hay]
    rw [ha,C.target_eq_self_of_source_eq_self ha,hxy]

lemma whisker_right {x : C.Cell} (hx : C.TopSequence n G x)
    (k : ℕ) (hk : k < n) (a : C.Cell) (ha : C.source n a = a)
    (h : C.target k x = C.source k a) : C.TopSequence n G (C.join k x a) := by
  induction hx with
  | lower x hx =>
    apply TopSequence.lower
    rw [C.join_source_gt n k x a hk h,hx,ha]
  | single x hx => exact .single _ (.right k hk x a ha h hx)
  | compose x y hxy hx hy ihx ihy =>
    have hya : C.target k y = C.source k a := by
      rw [C.join_target_le k n x y hk.le hxy] at h
      exact h
    have hxa : C.target k x = C.source k a := by
      have he := congrArg (C.target k) hxy
      simp only [C.target_target,min_eq_left hk.le,C.target_source,ite_eq_left hk] at he
      exact he.trans hya
    rw [C.join_whisker_right k n hk x y a ha hxy hxa hya]
    refine .compose _ _ ?_ (ihx hxa) (ihy hya)
    rw [C.join_target_gt n k x a hk hxa,C.join_source_gt n k y a hk hya]
    rw [ha,C.target_eq_self_of_source_eq_self ha,hxy]

lemma join {x y : C.Cell} (hx : C.TopSequence n G x) (hy : C.TopSequence n G y)
    (k : ℕ) (hk : k ≤ n) (h : C.target k x = C.source k y) :
    C.TopSequence n G (C.join k x y) := by
  by_cases hn : k = n
  · subst k
    exact .compose x y h hx hy
  have hkn : k < n := by omega
  have hxs : C.target k x = C.source k (C.source n y) := by
    rw [C.source_source,min_eq_left hk]
    exact h
  have hty : C.target k (C.target n x) = C.source k y := by
    rw [C.target_target,min_eq_left hk]
    exact h
  rw [C.join_factor_right k n hkn x y h]
  refine .compose _ _ ?_
    (hx.whisker_right k hkn _ (C.source_source_self n y) hxs)
    (hy.whisker_left k hkn _ (C.source_target_self n x) hty)
  rw [C.join_target_gt n k x (C.source n y) hkn hxs,
    C.join_source_gt n k (C.target n x) y hkn hty,
    C.source_target_self n x,C.target_source_self n y]

lemma comp {x y : C.Cell} (hx : C.TopSequence n G x) (hy : C.TopSequence n G y)
    (k : ℕ) (hk : k ≤ n) (h : C.target k x = C.source k y) :
    C.TopSequence n G (C.comp k x y h) := by
  rw [← C.join_eq k x y h]
  exact hx.join hy k hk h

end TopSequence
end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.RankedAtoms
open Table OmegaCategory

variable {K : DirectedComplex.{u}} (A : RankedAtoms.{u,v} K)
variable {C : OmegaCategory.{w}} (F : OmegaCategory.Functor C K.nu)

def TopGenerator (n : ℕ) (x : C.Cell) : Prop :=
  ∃ b : A.Index, A.dim b = n+1 ∧ F.map x = A.atom b

lemma basis_ne_zero (p : ℕ) (b : A.Index) (hb : A.dim b = p) : A.basis p b ≠ 0 := by
  intro h
  have ht := A.coefficient_basis p b b
  rw [h,map_zero,ite_eq_left hb,ite_eq_left rfl] at ht
  omega

lemma top_row_join (n k : ℕ) (hk : k < n) (x y : C.Cell)
    (h : C.target k x = C.source k y) :
    (F.map (C.join k x y)).row n false =
      (F.map x).row n false + (F.map y).row n false := by
  rw [F.map_join k x y h,K.nu.join_eq k (F.map x) (F.map y) (F.map_composable h)]
  change (Table.comp k (F.map x) (F.map y) (F.map_composable h)).row n false = _
  erw [comp_row]
  simp only [show ¬ n < k by omega,show n ≠ k by omega,ite_false]

lemma top_row_lower (n : ℕ) (x : C.Cell) (hx : C.source n x = x) :
    (F.map x).row (n+1) false = 0 := by
  have h : truncate n false (F.map x) = F.map x :=
    (F.map_source n x).symm.trans (congrArg F.map hx)
  exact row_above_fixed (F.map x) h (Nat.lt_succ_self n) false

lemma whisker_top_basis {n : ℕ} {x : C.Cell} (h : C.Whisker n (A.TopGenerator F n) x) :
    ∃ b : A.Index, A.dim b = n+1 ∧ (F.map x).row (n+1) false = A.basis (n+1) b := by
  induction h with
  | generator x hg hx =>
    obtain ⟨b,hb,he⟩ := hg
    refine ⟨b,hb,?_⟩
    rw [he,← hb,A.basis_own]
  | left k hk a x ha h hx ih =>
    obtain ⟨b,hb,he⟩ := ih
    refine ⟨b,hb,?_⟩
    rw [top_row_join F (n+1) k (by omega) a x h,top_row_lower F n a ha,zero_add,he]
  | right k hk x a ha h hx ih =>
    obtain ⟨b,hb,he⟩ := ih
    refine ⟨b,hb,?_⟩
    rw [top_row_join F (n+1) k (by omega) x a h,top_row_lower F n a ha,add_zero,he]

lemma fixed_of_top_row_zero (n : ℕ)
    (hreflect : ∀ x : C.Cell, truncate n false (F.map x) = F.map x → C.source n x = x)
    (x : C.Cell) (hx : C.source (n+1) x = x)
    (ht : (F.map x).row (n+1) false = 0) : C.source n x = x := by
  apply hreflect
  exact fixed_of_top_zero ((F.map_source (n+1) x).symm.trans (congrArg F.map hx)) ht

lemma topSequence_single {n : ℕ} {b : A.Index} (hb : A.dim b = n+1)
    (hreflect : ∀ x : C.Cell, truncate n false (F.map x) = F.map x → C.source n x = x)
    {x : C.Cell} (h : C.TopSequence n (A.TopGenerator F n) x)
    (ht : (F.map x).row (n+1) false = A.basis (n+1) b) :
    C.Whisker n (A.TopGenerator F n) x := by
  induction h with
  | lower x hx =>
    have hz := top_row_lower F n x hx
    exact False.elim (A.basis_ne_zero (n+1) b hb (ht.symm.trans hz))
  | single x hx => exact hx
  | compose x y h hx hy ihx ihy =>
    rw [top_row_join F (n+1) n (Nat.lt_succ_self n) x y h] at ht
    rcases A.positive_split_basis (n+1) b hb _ _
      ((F.map x).positive (n+1) false) ((F.map y).positive (n+1) false) ht with hzero | hzero
    · have hx' := fixed_of_top_row_zero F n hreflect x hx.bounded hzero
      rw [C.join_left_unit n x y hx' h]
      rw [hzero,zero_add] at ht
      exact ihy ht
    · have hy' := fixed_of_top_row_zero F n hreflect y hy.bounded hzero
      rw [C.join_right_unit n x y hy' h]
      rw [hzero,add_zero] at ht
      exact ihx ht

lemma top_and_source_ext (n : ℕ) (x y : Table K)
    (hx : truncate (n+1) false x = x) (hy : truncate (n+1) false y = y)
    (ht : x.row (n+1) false = y.row (n+1) false)
    (hs : truncate n false x = truncate n false y) : x = y := by
  ext p e
  by_cases hp : n < p
  · exact NormalizedChains.rows_above_top_agree x y hx hy ht p (by omega) e
  · have hpn : p ≤ n := by omega
    by_cases he : p = n ∧ e = true
    · obtain ⟨he,rfl⟩ := he
      subst p
      have hleft := congrArg (fun z : Table K => z.row n false) hs
      simp only [truncate_row,lt_self_iff_false,ite_false,ite_true] at hleft
      have hd := congrArg (K.d n) ht
      rw [x.boundary,y.boundary,hleft] at hd
      exact (sub_left_inj).mp hd
    · have h := congrArg (fun z : Table K => z.row p e) hs
      by_cases hpn' : p < n
      · simpa only [truncate_row,ite_eq_left hpn'] using h
      · have hp : p = n := by omega
        subst p
        have he' : e = false := by cases e <;> simp_all
        subst e
        simpa only [truncate_row,lt_self_iff_false,ite_false,ite_true] using h
end Thomason.DirectedComplex.RankedAtoms

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex Table OmegaCategory NormalizedChains

variable {N : ℕ} {P : Type u} [LinearOrder P] (e : Fin (N+1) ≃o P)

theorem tensor_top_sequence (n : ℕ)
    (x : (tensorFunctor.obj (NormalizedChains.complex P).nu).Cell)
    (hx : (tensorFunctor.obj (NormalizedChains.complex P).nu).source (n+1) x = x) :
    (tensorFunctor.obj (NormalizedChains.complex P).nu).TopSequence n
      ((Prism.Basis.ofOrderIso e).TopGenerator (chainComparison (NormalizedChains.complex P)) n) x := by
  let M := NormalizedChains.complex P
  let A := Prism.Word.ofOrderIso e
  let B := Prism.Basis.ofOrderIso e
  let T := tensorFunctor.obj M.nu
  let F := chainComparison M
  have hh := tensor_atomic_layers A (n+1) x hx
  clear hx
  induction hh with
  | endpoint a b hb =>
    by_cases he : A.dim b ≤ n
    · apply TopSequence.lower
      erw [endpoint_source]
      exact congrArg ((tensorEndpoint a).app M.nu).map
        (M.nu.source_fixed_upwards he (A.bounded b))
    · apply TopSequence.single
      apply Whisker.generator
      · exact ⟨Prism.Basis.endpoint a b,by change A.dim b = n+1; omega,
          chainComparison_endpoint_basis e a b⟩
      · erw [endpoint_source]
        exact congrArg ((tensorEndpoint a).app M.nu).map
          (M.nu.source_fixed_upwards hb (A.bounded b))
  | vertical b hb =>
    by_cases he : A.dim b < n
    · exact TopSequence.lower _ (T.source_fixed_upwards (by omega : A.dim b+1 ≤ n)
        (verticalCell_bounded _ _))
    · apply TopSequence.single
      apply Whisker.generator
      · exact ⟨Prism.Basis.vertical b,by change A.dim b+1 = n+1; omega,
          chainComparison_vertical_basis e b⟩
      · exact T.source_fixed_upwards (by omega : A.dim b+1 ≤ n+1)
          (verticalCell_bounded _ _)
  | lower k hk z hz => exact TopSequence.lower _ (T.source_fixed_upwards (by omega : k ≤ n) hz)
  | compose k hk x y h hx hy ihx ihy => exact ihx.comp ihy k (by omega) h

theorem tensor_single_top_whisker (n : ℕ) (b : (Prism.Basis.ofOrderIso e).Index)
    (hb : (Prism.Basis.ofOrderIso e).dim b = n+1)
    (x : (tensorFunctor.obj (NormalizedChains.complex P).nu).Cell)
    (hx : (tensorFunctor.obj (NormalizedChains.complex P).nu).source (n+1) x = x)
    (ht : ((chainComparison (NormalizedChains.complex P)).map x).row (n+1) false =
      (Prism.Basis.ofOrderIso e).basis (n+1) b) :
    (tensorFunctor.obj (NormalizedChains.complex P).nu).Whisker n
      ((Prism.Basis.ofOrderIso e).TopGenerator (chainComparison (NormalizedChains.complex P)) n) x := by
  apply (Prism.Basis.ofOrderIso e).topSequence_single
    (chainComparison (NormalizedChains.complex P)) hb
    (chainComparison_reflects_dimension (Prism.Basis.ofOrderIso e) n)
    (tensor_top_sequence e n x hx) ht
end Thomason.GrayRecursive.IntervalHom

end

end OAI
