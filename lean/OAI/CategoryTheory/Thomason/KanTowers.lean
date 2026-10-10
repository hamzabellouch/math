import Mathlib
import OAI.CategoryTheory.Thomason.CoherentGluing

namespace OAI

/-! Kan Towers. -/

noncomputable section
universe u v w z


namespace Thomason.AttachmentComparison
open CategoryTheory Limits OmegaCategory Attachments OneCat

lemma nerve_mono_orderMap {A E : Type u} [PartialOrder A] [PartialOrder E]
    (i : A →o E) (hi : Function.Injective i) : Mono (nerveMap i.toFunctor) := by
  rw [NatTrans.mono_iff_mono_app]
  intro m
  rw [CategoryTheory.mono_iff_injective]
  intro f g he
  exact CategoryTheory.Functor.ext (fun k => hi (congrArg (fun F => F.obj k) he))

lemma one_nerve_mono_orderMap {A E : Type u} [PartialOrder A] [PartialOrder E]
    (i : A →o E) (hi : Function.Injective i) :
    Mono ((streetNerveFinite 1).map (posetMap 1 i)) := by
  let ηA := (categorificationFiniteAdjunction 1).unit.app (nerve A)
  let ηE := (categorificationFiniteAdjunction 1).unit.app (nerve E)
  have : IsIso ηA := oneUnitCatIso (Cat.of A)
  have : IsIso ηE := oneUnitCatIso (Cat.of E)
  have : Mono (nerveMap i.toFunctor) := nerve_mono_orderMap i hi
  have he : (streetNerveFinite 1).map (posetMap 1 i) =
      inv ηA ≫ nerveMap i.toFunctor ≫ ηE := by
    apply (cancel_epi ηA).mp
    rw [IsIso.hom_inv_id_assoc]
    exact ((categorificationFiniteAdjunction 1).unit.naturality (nerveMap i.toFunctor)).symm
  rw [he]
  infer_instance
end Thomason.AttachmentComparison

end

noncomputable section
universe u v w z
open CategoryTheory Limits

namespace Thomason.AttachmentComparison

def upward {P : Type u} [PartialOrder P] (A : Set P) : Set P :=
  {p | ∃ a ∈ A, a ≤ p}

abbrev inclusion {P : Type u} [PartialOrder P] (n : ℕ) (A : Set P) :
    (categorificationFinite n).obj (nerve A) ⟶ (categorificationFinite n).obj (nerve P) :=
  (categorificationFinite n).map
    (nerveMap (OrderEmbedding.subtype A).toOrderHom.toFunctor)

abbrev nerveInclusion {P : Type u} [PartialOrder P] (n : ℕ) (A : Set P) :=
  (streetNerveFinite n).map (inclusion n A)

def comparison {P : Type u} [PartialOrder P] (n : ℕ) (A : Set P)
    {X : OmegaCategory.NCategory.{u} n}
    (a : (categorificationFinite n).obj (nerve A) ⟶ X) :
    pushout ((streetNerveFinite n).map a) (nerveInclusion n A) ⟶
      (streetNerveFinite n).obj (pushout a (inclusion n A)) :=
  pushout.desc ((streetNerveFinite n).map (pushout.inl a (inclusion n A)))
    ((streetNerveFinite n).map (pushout.inr a (inclusion n A))) (by
      simp only [← Functor.map_comp, pushout.condition])

def targetMap {P : Type u} [PartialOrder P] (n : ℕ) (A : Set P)
    {X X' : OmegaCategory.NCategory.{u} n}
    (a : (categorificationFinite n).obj (nerve A) ⟶ X)
    (a' : (categorificationFinite n).obj (nerve A) ⟶ X')
    (f : X ⟶ X') (hf : a ≫ f = a') :
    pushout a (inclusion n A) ⟶ pushout a' (inclusion n A) :=
  pushout.desc (f ≫ pushout.inl a' (inclusion n A))
    (pushout.inr a' (inclusion n A)) (by
      rw [← Category.assoc, hf, pushout.condition])

def sourceMap {P : Type u} [PartialOrder P] (n : ℕ) (A : Set P)
    {X X' : OmegaCategory.NCategory.{u} n}
    (a : (categorificationFinite n).obj (nerve A) ⟶ X)
    (a' : (categorificationFinite n).obj (nerve A) ⟶ X')
    (f : X ⟶ X') (hf : a ≫ f = a') :
    pushout ((streetNerveFinite n).map a) (nerveInclusion n A) ⟶
      pushout ((streetNerveFinite n).map a') (nerveInclusion n A) :=
  pushout.desc ((streetNerveFinite n).map f ≫ pushout.inl
      ((streetNerveFinite n).map a') (nerveInclusion n A))
    (pushout.inr ((streetNerveFinite n).map a') (nerveInclusion n A)) (by
      rw [← Category.assoc, ← Functor.map_comp, hf, pushout.condition])

def OneStatement : Prop := ∀ {P : Type u} [PartialOrder P]
    (A : Set P) (_ : IsLowerSet A)
    (r : upward A →o A)
    (_ : ∀ a : A, r ⟨a.val, a.val, a.property, le_rfl⟩ = a)
    (_ : ∀ (a : A) (z : upward A), a.val ≤ z.val ↔ a ≤ r z)
    (X : OmegaCategory.NCategory.{u} 1)
    (a : (categorificationFinite 1).obj (nerve A) ⟶ X),
    simplicialWeakEquivalences (comparison 1 A a) ∧
    Mono (nerveInclusion 1 A) ∧
    ∀ (X' : OmegaCategory.NCategory.{u} 1)
      (a' : (categorificationFinite 1).obj (nerve A) ⟶ X')
      (f : X ⟶ X') (hf : a ≫ f = a'),
      sourceMap 1 A a a' f hf ≫ comparison 1 A a' =
        comparison 1 A a ≫ (streetNerveFinite 1).map (targetMap 1 A a a' f hf)
end Thomason.AttachmentComparison

end

noncomputable section
universe u v w z
open CategoryTheory Limits

namespace Thomason.AttachmentComparison
open CategoryTheory Limits OmegaCategory Attachments OneCat

lemma comparison_local_one {B : Type u} [PartialOrder B]
    (A : Set B) (hA : IsLowerSet A)
    (r : upward A →o A)
    (hr : ∀ a : A, r ⟨a.val,a.val,a.property,le_rfl⟩ = a)
    (hadj : ∀ (a : A) (z : upward A), a.val ≤ z.val ↔ a ≤ r z)
    {X Y : NCategory.{u} 1} (a : posetObj 1 A ⟶ X)
    (j : X ⟶ Y) (v : posetObj 1 B ⟶ Y) (sc : IsPushout a (inc 1 A) j v)
    {P : SSet.{u}} {lX : (streetNerveFinite 1).obj X ⟶ P}
    {lB : (streetNerveFinite 1).obj (posetObj 1 B) ⟶ P}
    (ss : IsPushout ((streetNerveFinite 1).map a) ((streetNerveFinite 1).map (inc 1 A)) lX lB)
    (F : P ⟶ (streetNerveFinite 1).obj Y)
    (hFX : lX ≫ F = (streetNerveFinite 1).map j)
    (hFB : lB ≫ F = (streetNerveFinite 1).map v) : KanLocal.Local F := by
  let Z := upward A
  let C := Aᶜ
  have hAZ : A ⊆ Z := fun x hx => ⟨x,hx,le_rfl⟩
  have hZ : IsUpperSet Z := by
    intro x y hxy hx
    obtain ⟨a,ha,hax⟩ := hx
    exact ⟨a,ha,hax.trans hxy⟩
  have hC : IsUpperSet C := isUpperSet_compl.mpr hA
  have hcov : Z ∪ C = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x ∈ A
    · exact Or.inl (hAZ hx)
    · exact Or.inr hx
  obtain ⟨YZ,jZ,vZ,uZ,scZ,hj,hv,sq⟩ :=
    attachment_nerve_cover 1 (by decide) A Z C hZ hC hAZ (disjoint_compl_right) hcov a j v sc
  let N := streetNerveFinite 1
  let e := N.map (sb 1 A Z hAZ)
  let b := N.map a
  let PZ := pushout b e
  let xZ := pushout.inl b e
  let zZ := pushout.inr b e
  let sZ := IsPushout.of_hasPushout b e
  let FZ : PZ ⟶ N.obj YZ := sZ.desc (N.map jZ) (N.map vZ) (by
    rw [← N.map_comp, ← N.map_comp, scZ.w])
  have hFZX : xZ ≫ FZ = N.map jZ := sZ.inl_desc _ _ _
  have hFZZ : zZ ≫ FZ = N.map vZ := sZ.inr_desc _ _ _
  obtain ⟨gZ,HZ,HYZ,hcoh⟩ := finite_poset_comparison_coherent
    (subposetMap A Z hAZ) r hr (fun z => (hadj (r z) z).mpr le_rfl)
    scZ sZ FZ hFZX hFZZ
  let pZ : PZ ⟶ P := sZ.desc lX (N.map (inc 1 Z) ≫ lB) (by
    rw [← Category.assoc, ← N.map_comp, sb_inc]
    exact ss.w)
  have hpZX : xZ ≫ pZ = lX := sZ.inl_desc _ _ _
  have hpZZ : zZ ≫ pZ = N.map (inc 1 Z) ≫ lB := sZ.inr_desc _ _ _
  have ss' : IsPushout b (e ≫ N.map (inc 1 Z)) (xZ ≫ pZ) lB := by
    rw [hpZX, ← N.map_comp, sb_inc]
    exact ss
  have sr : IsPushout zZ (N.map (inc 1 Z)) pZ lB := ss'.of_top hpZZ sZ
  have sp := (poset_nerve_cover 1 (by decide) Z C hZ hC hcov).paste_horiz sr
  let k := N.map (sb 1 (Z ∩ C) Z Set.inter_subset_left) ≫ zZ
  let c := N.map (sb 1 (Z ∩ C) C Set.inter_subset_right)
  have hc : Mono c := one_nerve_mono_orderMap
    (A := ↥(Z ∩ C)) (E := C) (subposetMap (Z ∩ C) C Set.inter_subset_right)
    (by intro x y he; exact Subtype.ext (congrArg (fun z : C => (z : B)) he))
  have hk : k ≫ FZ = N.map (sb 1 (Z ∩ C) Z Set.inter_subset_left ≫ vZ) := by
    rw [show k = N.map (sb 1 (Z ∩ C) Z Set.inter_subset_left) ≫ zZ from rfl,
      Category.assoc, hFZZ, ← N.map_comp]
  have sq' : IsPushout (k ≫ FZ) c (N.map uZ) (N.map (inc 1 C ≫ v)) := by
    rw [hk]
    exact sq
  have hFpZ : pZ ≫ F = FZ ≫ N.map uZ := by
    apply sZ.hom_ext
    · rw [← Category.assoc, hpZX, ← Category.assoc xZ, hFZX, ← N.map_comp, hj]
      exact hFX
    · rw [← Category.assoc, hpZZ, Category.assoc, hFB,
        ← Category.assoc zZ, hFZZ, ← N.map_comp, ← N.map_comp, hv]
  have hFC : (N.map (inc 1 C) ≫ lB) ≫ F = N.map (inc 1 C ≫ v) := by
    rw [Category.assoc, hFB, ← N.map_comp]
  exact KanLocal.local_pushout_map k c FZ
    (KanLocal.local_heq FZ ⟨gZ, LastVertexProof.homotopic_of_homotopy HZ,
      LastVertexProof.homotopic_of_homotopy HYZ⟩) sp sq' F hFpZ hFC

end Thomason.AttachmentComparison

end

noncomputable section
universe u v w z


namespace Thomason.KanPath
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonoidalClosed Simplicial
open LastVertexProof KanHomotopy KanLocal
open SSet.modelCategoryQuillen

abbrev Paths (B : SSet.{u}) := (ihom (Δ[1] : SSet.{u})).obj B

def curryR {A B : SSet.{u}} (h : A ⊗ Δ[1] ⟶ B) : A ⟶ Paths B :=
  curry ((β_ Δ[1] A).hom ≫ h)
def uncurryR {A B : SSet.{u}} (g : A ⟶ Paths B) : A ⊗ Δ[1] ⟶ B :=
  (β_ A Δ[1]).hom ≫ uncurry g

@[simp] lemma uncurryR_curryR {A B : SSet.{u}} (h : A ⊗ Δ[1] ⟶ B) :
    uncurryR (curryR h) = h := by
  dsimp only [uncurryR, curryR]
  rw [uncurry_curry, ← Category.assoc]
  have hh : (β_ A Δ[1]).hom ≫ (β_ Δ[1] A).hom = 𝟙 _ := by ext n x <;> rfl
  rw [hh, Category.id_comp]

@[simp] lemma curryR_uncurryR {A B : SSet.{u}} (g : A ⟶ Paths B) :
    curryR (uncurryR g) = g := by
  dsimp only [uncurryR, curryR]
  rw [← Category.assoc]
  have hh : (β_ Δ[1] A).hom ≫ (β_ A Δ[1]).hom = 𝟙 _ := by ext n x <;> rfl
  rw [hh, Category.id_comp, curry_uncurry]

lemma uncurryR_injective {A B : SSet.{u}} : Function.Injective (@uncurryR A B) := by
  intro g h H
  simpa using congrArg curryR H

@[reassoc] lemma uncurryR_pre {A C B : SSet.{u}} (a : A ⟶ C) (g : C ⟶ Paths B) :
    uncurryR (a ≫ g) = a ▷ Δ[1] ≫ uncurryR g := by
  dsimp only [uncurryR]
  rw [uncurry_natural_left, ← Category.assoc, ← Category.assoc]
  congr 1

@[reassoc] lemma uncurryR_post {A B C : SSet.{u}} (g : A ⟶ Paths B) (f : B ⟶ C) :
    uncurryR (g ≫ (ihom Δ[1]).map f) = uncurryR g ≫ f := by
  dsimp only [uncurryR]
  rw [uncurry_natural_right, Category.assoc]

def ev (B : SSet.{u}) : Paths B ⊗ Δ[1] ⟶ B := uncurryR (𝟙 (Paths B))
def eval₀ (B : SSet.{u}) : Paths B ⟶ B := SSet.ι₀ ≫ ev B
def eval₁ (B : SSet.{u}) : Paths B ⟶ B := SSet.ι₁ ≫ ev B
def const (B : SSet.{u}) : B ⟶ Paths B := curryR (fst B Δ[1])

lemma uncurryR_eq {A B : SSet.{u}} (g : A ⟶ Paths B) :
    uncurryR g = g ▷ Δ[1] ≫ ev B := by
  simpa only [Category.comp_id, ev] using uncurryR_pre g (𝟙 (Paths B))

@[reassoc] lemma comp_eval₀ {A B : SSet.{u}} (g : A ⟶ Paths B) :
    g ≫ eval₀ B = SSet.ι₀ ≫ uncurryR g := by
  rw [uncurryR_eq, eval₀, SSet.ι₀_comp_assoc]
@[reassoc] lemma comp_eval₁ {A B : SSet.{u}} (g : A ⟶ Paths B) :
    g ≫ eval₁ B = SSet.ι₁ ≫ uncurryR g := by
  rw [uncurryR_eq, eval₁, SSet.ι₁_comp_assoc]

@[reassoc (attr := simp)] lemma const_eval₀ (B : SSet.{u}) : const B ≫ eval₀ B = 𝟙 B := by
  rw [comp_eval₀, const, uncurryR_curryR]
  simp
@[reassoc (attr := simp)] lemma const_eval₁ (B : SSet.{u}) : const B ≫ eval₁ B = 𝟙 B := by
  rw [comp_eval₁, const, uncurryR_curryR]
  simp

@[reassoc] lemma eval₀_naturality {B C : SSet.{u}} (f : B ⟶ C) :
    (ihom Δ[1]).map f ≫ eval₀ C = eval₀ B ≫ f := by
  have H := uncurryR_post (𝟙 (Paths B)) f
  simp only [Category.id_comp] at H
  rw [comp_eval₀, H]
  rfl
@[reassoc] lemma eval₁_naturality {B C : SSet.{u}} (f : B ⟶ C) :
    (ihom Δ[1]).map f ≫ eval₁ C = eval₁ B ≫ f := by
  have H := uncurryR_post (𝟙 (Paths B)) f
  simp only [Category.id_comp] at H
  rw [comp_eval₁, H]
  rfl

def minSquare (A : SSet.{u}) : (A ⊗ Δ[1]) ⊗ Δ[1] ⟶ A ⊗ Δ[1] where
  app n := ↾fun x => (x.1.1, SSet.stdSimplex.objMk
    (SSet.stdSimplex.asOrderHom x.1.2 ⊓ SSet.stdSimplex.asOrderHom x.2))
  naturality n m θ := by
    ext x
    apply Prod.ext
    · rfl
    · apply SSet.stdSimplex.ext
      intro j
      rfl

lemma minSquare_left (A : SSet.{u}) : SSet.ι₀ ▷ Δ[1] ≫ minSquare A = fst A Δ[1] ≫ SSet.ι₀ := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  apply Prod.ext
  · rfl
  · apply SSet.stdSimplex.ext
    intro j
    change min 0 (_ : Fin 2) = 0
    exact min_eq_left (Fin.zero_le _)
lemma minSquare_right (A : SSet.{u}) : SSet.ι₁ ▷ Δ[1] ≫ minSquare A = 𝟙 _ := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  apply Prod.ext
  · rfl
  · apply SSet.stdSimplex.ext
    intro j
    change min 1 (_ : Fin 2) = _
    exact min_eq_right (Fin.le_last _)
lemma minSquare_bottom (A : SSet.{u}) : SSet.ι₀ ≫ minSquare A = fst A Δ[1] ≫ SSet.ι₀ := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  apply Prod.ext
  · rfl
  · apply SSet.stdSimplex.ext
    intro j
    change min (_ : Fin 2) 0 = 0
    exact min_eq_right (Fin.zero_le _)

def contraction (B : SSet.{u}) : SSet.Homotopy (eval₀ B ≫ const B) (𝟙 (Paths B)) :=
  CoherentGluing.toHomotopy (curryR (minSquare (Paths B) ≫ ev B))
    (by
      apply uncurryR_injective
      rw [uncurryR_pre, uncurryR_curryR, ← Category.assoc, minSquare_left,
        Category.assoc, uncurryR_pre, const, uncurryR_curryR, whiskerRight_fst]
      rfl)
    (by
      apply uncurryR_injective
      rw [uncurryR_pre, uncurryR_curryR, ← Category.assoc, minSquare_right, Category.id_comp]
      rfl)

@[reassoc] lemma contraction_eval₀ (B : SSet.{u}) :
    (contraction B).h ≫ eval₀ B = fst _ _ ≫ eval₀ B := by
  rw [comp_eval₀]
  change SSet.ι₀ ≫ uncurryR (curryR (minSquare (Paths B) ≫ ev B)) = _
  rw [uncurryR_curryR, ← Category.assoc, minSquare_bottom, Category.assoc]
  rfl

lemma cylinder_lift_ends {D E X Y : SSet.{u}} (i : D ⟶ E)
    (hi : SSet.anodyneExtensions i) (p : X ⟶ Y) (hp : simplicialFibrations p)
    (x₀ x₁ : E ⟶ X) (H : D ⊗ Δ[1] ⟶ X) (G : E ⊗ Δ[1] ⟶ Y)
    (h₀ : i ≫ x₀ = SSet.ι₀ ≫ H) (h₁ : i ≫ x₁ = SSet.ι₁ ≫ H)
    (g₀ : x₀ ≫ p = SSet.ι₀ ≫ G) (g₁ : x₁ ≫ p = SSet.ι₁ ≫ G)
    (hG : H ≫ p = i ▷ Δ[1] ≫ G) :
    ∃ Q : E ⊗ Δ[1] ⟶ X, i ▷ Δ[1] ≫ Q = H ∧
      SSet.ι₀ ≫ Q = x₀ ∧ SSet.ι₁ ≫ Q = x₁ ∧ Q ≫ p = G := by
  let s := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) i intervalEnds
  have hc : i ▷ SimplicialCylinder.Ends Δ[0] ≫ endsTensorMap x₀ x₁ =
      D ◁ intervalEnds ≫ H := by
    ext n x
    rcases x with ⟨x,y⟩
    cases y with
    | inl y => exact congrArg (fun t : D ⟶ X => t.app n x) h₀
    | inr y => exact congrArg (fun t : D ⟶ X => t.app n x) h₁
  let t : s.pt ⟶ X := s.isPushout.desc (endsTensorMap x₀ x₁) H hc
  have hinl : s.inl ≫ s.ι = E ◁ intervalEnds := s.inl_ι
  have hinr : s.inr ≫ s.ι = i ▷ Δ[1] := s.inr_ι
  have ht : t ≫ p = s.ι ≫ G := by
    apply s.isPushout.hom_ext
    · simp only [t, ← Category.assoc, s.isPushout.inl_desc, hinl]
      ext n x
      rcases x with ⟨x,y⟩
      cases y with
      | inl y => exact congrArg (fun t : E ⟶ Y => t.app n x) g₀
      | inr y => exact congrArg (fun t : E ⟶ Y => t.app n x) g₁
    · simpa only [t, ← Category.assoc, s.isPushout.inr_desc, hinr] using hG
  have : HasLiftingProperty s.ι p :=
    SSet.anodyneExtensions_pushoutObjObjι' s hi p hp
  let sq : CommSq t s.ι p G := ⟨ht⟩
  have he : E ◁ intervalEnds ≫ sq.lift = endsTensorMap x₀ x₁ := by
    rw [← hinl, Category.assoc, sq.fac_left]
    exact s.isPushout.inl_desc _ _ _
  refine ⟨sq.lift, ?_, ?_, ?_, sq.fac_right⟩
  · rw [← hinr, Category.assoc, sq.fac_left]
    exact s.isPushout.inr_desc _ _ _
  · ext n x
    exact congrArg (fun t => t.app n (x, Sum.inl (SSet.stdSimplex.objMk (OrderHom.const _ 0)))) he
  · ext n x
    exact congrArg (fun t => t.app n (x, Sum.inr (SSet.stdSimplex.objMk (OrderHom.const _ 0)))) he

abbrev MappingPath {A B : SSet.{u}} (f : A ⟶ B) := pullback f (eval₀ B)
def left {A B : SSet.{u}} (f : A ⟶ B) : A ⟶ MappingPath f :=
  pullback.lift (𝟙 A) (f ≫ const B) (by simp)
def right {A B : SSet.{u}} (f : A ⟶ B) : MappingPath f ⟶ B :=
  pullback.snd f (eval₀ B) ≫ eval₁ B

@[reassoc (attr := simp)] lemma fac {A B : SSet.{u}} (f : A ⟶ B) : left f ≫ right f = f := by
  simp [left, right, pullback.lift_snd_assoc]

lemma left_heq {A B : SSet.{u}} (f : A ⟶ B) : IsHomotopyEquivalence (left f) := by
  let a := pullback.fst f (eval₀ B)
  let p := pullback.snd f (eval₀ B)
  have hp : a ≫ f = p ≫ eval₀ B := pullback.condition
  let H : MappingPath f ⊗ Δ[1] ⟶ MappingPath f := pullback.lift (fst _ _ ≫ a)
    (p ▷ Δ[1] ≫ (contraction B).h)
    (by rw [Category.assoc, Category.assoc, contraction_eval₀,
      whiskerRight_fst_assoc, ← hp])
  refine ⟨a, ?_, ?_⟩
  · have hl : left f ≫ a = 𝟙 A := by simp only [left, a, pullback.lift_fst]
    rw [hl]
    exact homotopic_refl _
  · apply homotopic_of_homotopy
    refine CoherentGluing.toHomotopy H ?_ ?_
    · apply pullback.hom_ext
      · simp [H, a, left, pullback.lift_fst]
      · simp only [H, Category.assoc, pullback.lift_snd]
        rw [SSet.ι₀_comp_assoc, (contraction B).h₀]
        simp only [left, pullback.lift_snd]
        rw [← Category.assoc, ← hp]
        rfl
    · apply pullback.hom_ext
      · simp [H, a, pullback.lift_fst]
      · simp only [H, Category.assoc, pullback.lift_snd, Category.id_comp]
        rw [SSet.ι₁_comp_assoc, (contraction B).h₁, Category.comp_id]

def map {A₁ A₀ B₁ B₀ : SSet.{u}} {f₁ : A₁ ⟶ B₁} {f₀ : A₀ ⟶ B₀}
    (a : A₁ ⟶ A₀) (b : B₁ ⟶ B₀) (h : a ≫ f₀ = f₁ ≫ b) :
    MappingPath f₁ ⟶ MappingPath f₀ :=
  pullback.lift (pullback.fst _ _ ≫ a) (pullback.snd _ _ ≫ (ihom Δ[1]).map b) (by
    simp only [Category.assoc, eval₀_naturality, h]
    rw [← Category.assoc, pullback.condition, Category.assoc])

@[reassoc (attr := simp)] lemma map_fst {A₁ A₀ B₁ B₀ : SSet.{u}}
    {f₁ : A₁ ⟶ B₁} {f₀ : A₀ ⟶ B₀} (a : A₁ ⟶ A₀) (b : B₁ ⟶ B₀)
    (h : a ≫ f₀ = f₁ ≫ b) :
    map a b h ≫ pullback.fst f₀ (eval₀ B₀) = pullback.fst f₁ (eval₀ B₁) ≫ a := by
  simp only [map, pullback.lift_fst]
@[reassoc (attr := simp)] lemma map_snd {A₁ A₀ B₁ B₀ : SSet.{u}}
    {f₁ : A₁ ⟶ B₁} {f₀ : A₀ ⟶ B₀} (a : A₁ ⟶ A₀) (b : B₁ ⟶ B₀)
    (h : a ≫ f₀ = f₁ ≫ b) :
    map a b h ≫ pullback.snd f₀ (eval₀ B₀) =
      pullback.snd f₁ (eval₀ B₁) ≫ (ihom Δ[1]).map b := by
  simp only [map, pullback.lift_snd]
@[reassoc (attr := simp)] lemma map_right {A₁ A₀ B₁ B₀ : SSet.{u}}
    {f₁ : A₁ ⟶ B₁} {f₀ : A₀ ⟶ B₀} (a : A₁ ⟶ A₀) (b : B₁ ⟶ B₀)
    (h : a ≫ f₀ = f₁ ≫ b) :
    map a b h ≫ right f₀ = right f₁ ≫ b := by
  simp only [right, map_snd_assoc, Category.assoc, eval₁_naturality]

lemma map_comp {A₂ A₁ A₀ B₂ B₁ B₀ : SSet.{u}}
    {f₂ : A₂ ⟶ B₂} {f₁ : A₁ ⟶ B₁} {f₀ : A₀ ⟶ B₀}
    (a₁ : A₂ ⟶ A₁) (b₁ : B₂ ⟶ B₁) (h₁ : a₁ ≫ f₁ = f₂ ≫ b₁)
    (a₀ : A₁ ⟶ A₀) (b₀ : B₁ ⟶ B₀) (h₀ : a₀ ≫ f₀ = f₁ ≫ b₀)
    (h : (a₁ ≫ a₀) ≫ f₀ = f₂ ≫ (b₁ ≫ b₀)) :
    map a₁ b₁ h₁ ≫ map a₀ b₀ h₀ = map (a₁ ≫ a₀) (b₁ ≫ b₀) h := by
  apply pullback.hom_ext
  · simp
  · simp [Functor.map_comp]

lemma right_lifting {A B D E : SSet.{u}} [SSet.KanComplex A] [SSet.KanComplex B]
    (f : A ⟶ B) (i : D ⟶ E) (hi : SSet.anodyneExtensions i)
    (x : D ⟶ MappingPath f) (y : E ⟶ B) (h : x ≫ right f = i ≫ y) :
    ∃ l : E ⟶ MappingPath f, i ≫ l = x ∧ l ≫ right f = y := by
  obtain ⟨a,ha⟩ := extend_anodyne i hi (x ≫ pullback.fst f (eval₀ B))
  have hp : simplicialFibrations (terminal.from B) := by
    change J.rlp _
    rw [← fibrations_eq, ← HomotopicalAlgebra.fibration_iff]
    infer_instance
  obtain ⟨Q,hQ,h₀,h₁,_⟩ := cylinder_lift_ends i hi (terminal.from B) hp
    (a ≫ f) y (uncurryR (x ≫ pullback.snd f (eval₀ B))) (terminal.from _)
    (by
      rw [← Category.assoc, ha, Category.assoc, pullback.condition, ← Category.assoc,
        comp_eval₀])
    (by rw [← comp_eval₁]; exact h.symm)
    (by subsingleton) (by subsingleton) (by subsingleton)
  let l : E ⟶ MappingPath f := pullback.lift a (curryR Q)
    (by rw [comp_eval₀, uncurryR_curryR, h₀])
  refine ⟨l, ?_, ?_⟩
  · apply pullback.hom_ext
    · simpa only [l, Category.assoc, pullback.lift_fst] using ha
    · simp only [Category.assoc, l, pullback.lift_snd]
      apply uncurryR_injective
      rw [uncurryR_pre, uncurryR_curryR, hQ]
  · change l ≫ pullback.snd _ _ ≫ eval₁ B = y
    rw [← Category.assoc, pullback.lift_snd, comp_eval₁, uncurryR_curryR, h₁]

lemma right_fibration {A B : SSet.{u}} [SSet.KanComplex A] [SSet.KanComplex B]
    (f : A ⟶ B) : simplicialFibrations (right f) := by
  change J.rlp _
  intro D E i hi
  constructor
  intro x y sq
  obtain ⟨l,hl,hr⟩ := right_lifting f i (MorphismProperty.le_llp_rlp J i hi) x y sq.w
  exact ⟨⟨l,hl,hr⟩⟩

lemma relative_lifting {A₁ A₀ B₁ B₀ D E : SSet.{u}}
    {f₁ : A₁ ⟶ B₁} {f₀ : A₀ ⟶ B₀} (a : A₁ ⟶ A₀) (b : B₁ ⟶ B₀)
    (w : a ≫ f₀ = f₁ ≫ b) (ha : simplicialFibrations a) (hb : simplicialFibrations b)
    (i : D ⟶ E) (hi : SSet.anodyneExtensions i)
    (x : D ⟶ MappingPath f₁) (y : E ⟶ MappingPath f₀) (z : E ⟶ B₁)
    (hm : x ≫ map a b w = i ≫ y) (hr : x ≫ right f₁ = i ≫ z)
    (hyz : y ≫ right f₀ = z ≫ b) :
    ∃ l : E ⟶ MappingPath f₁, i ≫ l = x ∧ l ≫ map a b w = y ∧ l ≫ right f₁ = z := by
  have : HasLiftingProperty i a := hi _ ha
  let sq : CommSq (x ≫ pullback.fst f₁ (eval₀ B₁)) i a
      (y ≫ pullback.fst f₀ (eval₀ B₀)) := ⟨by
    simpa only [Category.assoc, map_fst] using
      congrArg (fun t => t ≫ pullback.fst f₀ (eval₀ B₀)) hm⟩
  obtain ⟨Q,hQ,h₀,h₁,hbQ⟩ := cylinder_lift_ends i hi b hb
    (sq.lift ≫ f₁) z (uncurryR (x ≫ pullback.snd f₁ (eval₀ B₁)))
    (uncurryR (y ≫ pullback.snd f₀ (eval₀ B₀)))
    (by rw [← Category.assoc, sq.fac_left, Category.assoc, pullback.condition,
      ← Category.assoc, comp_eval₀])
    (by rw [← comp_eval₁]; exact hr.symm)
    (by
      rw [Category.assoc, ← w, ← Category.assoc, sq.fac_right, Category.assoc,
        pullback.condition, ← Category.assoc, comp_eval₀])
    (by rw [← comp_eval₁]; exact hyz.symm)
    (by
      have hm' : (x ≫ pullback.snd f₁ (eval₀ B₁)) ≫ (ihom Δ[1]).map b =
          i ≫ (y ≫ pullback.snd f₀ (eval₀ B₀)) := by
        simpa only [Category.assoc, map_snd] using
          congrArg (fun t => t ≫ pullback.snd f₀ (eval₀ B₀)) hm
      rw [← uncurryR_post, hm', uncurryR_pre])
  let l : E ⟶ MappingPath f₁ := pullback.lift sq.lift (curryR Q)
    (by rw [comp_eval₀, uncurryR_curryR, h₀])
  refine ⟨l, ?_, ?_, ?_⟩
  · apply pullback.hom_ext
    · simpa only [l, Category.assoc, pullback.lift_fst] using sq.fac_left
    · simp only [l, Category.assoc, pullback.lift_snd]
      apply uncurryR_injective
      rw [uncurryR_pre, uncurryR_curryR, hQ]
  · apply pullback.hom_ext
    · simp only [Category.assoc, map_fst, l, pullback.lift_fst_assoc, sq.fac_right]
    · simp only [Category.assoc, map_snd, l, pullback.lift_snd_assoc]
      apply uncurryR_injective
      rw [uncurryR_post, uncurryR_curryR, hbQ]
  · change l ≫ pullback.snd _ _ ≫ eval₁ B₁ = z
    rw [← Category.assoc, pullback.lift_snd, comp_eval₁, uncurryR_curryR, h₁]

abbrev Matching {A₀ B₁ B₀ : SSet.{u}} (f₀ : A₀ ⟶ B₀) (b : B₁ ⟶ B₀) :=
  pullback (right f₀) b

def relative {A₁ A₀ B₁ B₀ : SSet.{u}}
    {f₁ : A₁ ⟶ B₁} {f₀ : A₀ ⟶ B₀} (a : A₁ ⟶ A₀) (b : B₁ ⟶ B₀)
    (w : a ≫ f₀ = f₁ ≫ b) : MappingPath f₁ ⟶ Matching f₀ b :=
  pullback.lift (map a b w) (right f₁) (map_right a b w)

lemma relative_fibration {A₁ A₀ B₁ B₀ : SSet.{u}}
    {f₁ : A₁ ⟶ B₁} {f₀ : A₀ ⟶ B₀} (a : A₁ ⟶ A₀) (b : B₁ ⟶ B₀)
    (w : a ≫ f₀ = f₁ ≫ b) (ha : simplicialFibrations a) (hb : simplicialFibrations b) :
    simplicialFibrations (relative a b w) := by
  change J.rlp _
  intro D E i hi
  constructor
  intro x t sq
  obtain ⟨l,hl,hm,hr⟩ := relative_lifting a b w ha hb i
    (MorphismProperty.le_llp_rlp J i hi) x
    (t ≫ pullback.fst (right f₀) b) (t ≫ pullback.snd (right f₀) b)
    (by simpa only [Category.assoc, relative, pullback.lift_fst] using
      congrArg (fun q => q ≫ pullback.fst (right f₀) b) sq.w)
    (by simpa only [Category.assoc, relative, pullback.lift_snd] using
      congrArg (fun q => q ≫ pullback.snd (right f₀) b) sq.w)
    (by rw [Category.assoc, Category.assoc, pullback.condition])
  refine ⟨⟨l,hl,?_⟩⟩
  apply pullback.hom_ext
  · simpa only [Category.assoc, relative, pullback.lift_fst] using hm
  · simpa only [Category.assoc, relative, pullback.lift_snd] using hr

instance mappingPath_kan {A B : SSet.{u}} [SSet.KanComplex A] [SSet.KanComplex B]
    (f : A ⟶ B) : SSet.KanComplex (MappingPath f) := by
  let : HomotopicalAlgebra.Fibration (right f) := by
    rw [HomotopicalAlgebra.fibration_iff, fibrations_eq]
    exact right_fibration f
  exact HomotopicalAlgebra.isFibrant_of_fibration (right f)

lemma right_heq {A B : SSet.{u}} (f : A ⟶ B) (hf : IsHomotopyEquivalence f) :
    IsHomotopyEquivalence (right f) :=
  heq_of_precomp (left f) (right f) (left_heq f) (by simpa using hf)

lemma right_rlp {A B : SSet.{u}} [SSet.KanComplex A] [SSet.KanComplex B]
    (f : A ⟶ B) (hf : IsHomotopyEquivalence f) :
    (MorphismProperty.monomorphisms SSet).rlp (right f) :=
  rlp_of_homotopy_equivalence (right f) (right_fibration f) (right_heq f hf)

lemma relative_rlp {A₁ A₀ B₁ B₀ : SSet.{u}}
    [SSet.KanComplex A₁] [SSet.KanComplex A₀] [SSet.KanComplex B₁] [SSet.KanComplex B₀]
    {f₁ : A₁ ⟶ B₁} {f₀ : A₀ ⟶ B₀} (a : A₁ ⟶ A₀) (b : B₁ ⟶ B₀)
    (w : a ≫ f₀ = f₁ ≫ b) (ha : simplicialFibrations a) (hb : simplicialFibrations b)
    (hf₁ : IsHomotopyEquivalence f₁) (hf₀ : IsHomotopyEquivalence f₀) :
    (MorphismProperty.monomorphisms SSet).rlp (relative a b w) := by
  have hp : (MorphismProperty.monomorphisms SSet).rlp (pullback.snd (right f₀) b) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback (right f₀) b) (right_rlp f₀ hf₀)
  have hp' : simplicialFibrations (pullback.snd (right f₀) b) := by
    change J.rlp _
    exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback (right f₀) b)
      (right_fibration f₀)
  let : HomotopicalAlgebra.Fibration (pullback.snd (right f₀) b) := by
    rw [HomotopicalAlgebra.fibration_iff, fibrations_eq]
    exact hp'
  let : SSet.KanComplex (Matching f₀ b) :=
    HomotopicalAlgebra.isFibrant_of_fibration (pullback.snd (right f₀) b)
  have hq : IsHomotopyEquivalence (relative a b w) :=
    heq_of_postcomp _ (pullback.snd (right f₀) b) (heq_of_rlp _ hp)
      (by simpa only [relative, pullback.lift_snd] using right_heq f₁ hf₁)
  exact rlp_of_homotopy_equivalence _ (relative_fibration a b w ha hb) hq

end Thomason.KanPath

end

noncomputable section
universe u v w z


namespace Thomason.KanTower
open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonoidalClosed Simplicial
open LastVertexProof KanHomotopy KanLocal KanPath
open SSet.modelCategoryQuillen

abbrev edge (n : ℕ) : op (n + 1) ⟶ op n := (homOfLE (Nat.le_succ n)).op

def cone (F : ℕᵒᵖ ⥤ SSet.{u}) {Z : SSet.{u}} (p : ∀ n, Z ⟶ F.obj (op n))
    (hp : ∀ n, p (n+1) ≫ F.map (edge n) = p n) : Cone F := by
  have H (m n : ℕ) (h : m ≤ n) : p n ≫ F.map (homOfLE h).op = p m := by
    induction n, h using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      have e : (homOfLE (Nat.le.step hn)).op = edge n ≫ (homOfLE hn).op := Subsingleton.elim _ _
      rw [e, F.map_comp, ← Category.assoc, hp, ih]
  refine ⟨Z, ⟨fun n => p n.unop, ?_⟩⟩
  intro n m f
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
  exact (H m.unop n.unop (leOfHom f.unop)).symm

@[simp] lemma cone_π (F : ℕᵒᵖ ⥤ SSet.{u}) {Z : SSet.{u}} (p : ∀ n, Z ⟶ F.obj (op n))
    (hp : ∀ n, p (n+1) ≫ F.map (edge n) = p n) (n : ℕ) :
    (cone F p hp).π.app (op n) = p n := rfl

section
variable (F G : ℕᵒᵖ ⥤ SSet.{u}) (f : F ⟶ G)

abbrev limMap : limit F ⟶ limit G := lim.map f

def stage (n : ℕ) : MappingPath (limMap F G f) ⟶ MappingPath (f.app (op n)) :=
  KanPath.map (limit.π F (op n)) (limit.π G (op n)) (by simp)

def transition (n : ℕ) : MappingPath (f.app (op (n+1))) ⟶ MappingPath (f.app (op n)) :=
  KanPath.map (F.map (edge n)) (G.map (edge n)) (f.naturality (edge n))

@[reassoc (attr := simp)] lemma stage_fst (n : ℕ) :
    stage F G f n ≫ pullback.fst _ _ = pullback.fst _ _ ≫ limit.π F (op n) := by
  simp [stage]
@[reassoc (attr := simp)] lemma stage_snd (n : ℕ) :
    stage F G f n ≫ pullback.snd _ _ = pullback.snd _ _ ≫ (ihom Δ[1]).map (limit.π G (op n)) := by
  simp [stage]
@[reassoc (attr := simp)] lemma stage_right (n : ℕ) :
    stage F G f n ≫ right (f.app (op n)) = right (limMap F G f) ≫ limit.π G (op n) := by
  simp [stage]

@[reassoc (attr := simp)] lemma transition_fst (n : ℕ) :
    transition F G f n ≫ pullback.fst _ _ = pullback.fst _ _ ≫ F.map (edge n) := by
  simp [transition]
@[reassoc (attr := simp)] lemma transition_snd (n : ℕ) :
    transition F G f n ≫ pullback.snd _ _ = pullback.snd _ _ ≫ (ihom Δ[1]).map (G.map (edge n)) := by
  simp [transition]

@[reassoc] lemma stage_transition (n : ℕ) :
    stage F G f (n+1) ≫ transition F G f n = stage F G f n := by
  apply pullback.hom_ext
  · simp
  · simp only [Category.assoc, transition_snd, stage_snd_assoc, stage_snd,
      ← Functor.map_comp, limit.w]

variable (hF : ∀ n, SSet.KanComplex (F.obj (op n)))
  (hG : ∀ n, SSet.KanComplex (G.obj (op n)))
  (ha : ∀ n, simplicialFibrations (F.map (edge n)))
  (hb : ∀ n, simplicialFibrations (G.map (edge n)))
  (hf : ∀ n, IsHomotopyEquivalence (f.app (op n)))

include hF hG ha hb hf in
lemma path_limit_rlp : (MorphismProperty.monomorphisms SSet).rlp (right (limMap F G f)) := by
  intro D E i hi
  let : Mono i := hi
  constructor
  intro x y sq
  let X (n : ℕ) := {l : E ⟶ MappingPath (f.app (op n)) //
    i ≫ l = x ≫ stage F G f n ∧ l ≫ right (f.app (op n)) = y ≫ limit.π G (op n)}
  have seed : Nonempty (X 0) := by
    let := hF 0
    let := hG 0
    have : HasLiftingProperty i (right (f.app (op 0))) := right_rlp _ (hf 0) i hi
    let s : CommSq (x ≫ stage F G f 0) i (right (f.app (op 0)))
        (y ≫ limit.π G (op 0)) := ⟨by rw [Category.assoc, stage_right, ← Category.assoc, sq.w, Category.assoc]⟩
    exact ⟨⟨s.lift,s.fac_left,s.fac_right⟩⟩
  have step (n : ℕ) (l : X n) :
      Nonempty {l' : X (n+1) // l'.1 ≫ transition F G f n = l.1} := by
    let := hF n
    let := hF (n+1)
    let := hG n
    let := hG (n+1)
    let t : E ⟶ Matching (f.app (op n)) (G.map (edge n)) :=
      pullback.lift l.1 (y ≫ limit.π G (op (n+1))) (by rw [l.2.2, Category.assoc, limit.w])
    have : HasLiftingProperty i
        (relative (F.map (edge n)) (G.map (edge n)) (f.naturality (edge n))) :=
      relative_rlp _ _ _ (ha n) (hb n) (hf (n+1)) (hf n) i hi
    let s : CommSq (x ≫ stage F G f (n+1)) i
        (relative (F.map (edge n)) (G.map (edge n)) (f.naturality (edge n))) t := ⟨by
      apply pullback.hom_ext
      · simp only [Category.assoc, relative, pullback.lift_fst, t]
        change x ≫ (stage F G f (n+1) ≫ transition F G f n) = i ≫ l.1
        rw [stage_transition, l.2.1]
      · simp only [Category.assoc, relative, pullback.lift_snd, t]
        rw [stage_right, ← Category.assoc, sq.w, Category.assoc]⟩
    have h₁ : s.lift ≫ transition F G f n = l.1 := by
      simpa only [Category.assoc, relative, pullback.lift_fst, t, transition] using
        congrArg (fun r => r ≫ pullback.fst (right (f.app (op n))) (G.map (edge n))) s.fac_right
    have h₂ : s.lift ≫ right (f.app (op (n+1))) = y ≫ limit.π G (op (n+1)) := by
      simpa only [Category.assoc, relative, pullback.lift_snd, t] using
        congrArg (fun r => r ≫ pullback.snd (right (f.app (op n))) (G.map (edge n))) s.fac_right
    exact ⟨⟨⟨s.lift,s.fac_left,h₂⟩,h₁⟩⟩
  let lifts : ∀ n, X n := fun n => Nat.rec seed.some (fun n l => (step n l).some.1) n
  have hw (n : ℕ) : (lifts (n+1)).1 ≫ transition F G f n = (lifts n).1 :=
    (step n (lifts n)).some.2
  have hwA (n : ℕ) : ((lifts (n+1)).1 ≫ pullback.fst _ _) ≫ F.map (edge n) =
      (lifts n).1 ≫ pullback.fst _ _ := by
    simpa only [Category.assoc, transition_fst] using
      congrArg (fun r => r ≫ pullback.fst (f.app (op n)) (eval₀ (G.obj (op n)))) (hw n)
  have hwP (n : ℕ) : ((lifts (n+1)).1 ≫ pullback.snd _ _) ≫ (ihom Δ[1]).map (G.map (edge n)) =
      (lifts n).1 ≫ pullback.snd _ _ := by
    simpa only [Category.assoc, transition_snd] using
      congrArg (fun r => r ≫ pullback.snd (f.app (op n)) (eval₀ (G.obj (op n)))) (hw n)
  let A : E ⟶ limit F := limit.lift F (cone F (fun n => (lifts n).1 ≫ pullback.fst _ _) hwA)
  have hA (n : ℕ) : A ≫ limit.π F (op n) = (lifts n).1 ≫ pullback.fst _ _ :=
    limit.lift_π _ _
  let H : E ⊗ Δ[1] ⟶ limit G := limit.lift G (cone G (fun n => uncurryR ((lifts n).1 ≫ pullback.snd _ _))
    (fun n => by rw [← uncurryR_post, hwP]))
  have hH (n : ℕ) : H ≫ limit.π G (op n) = uncurryR ((lifts n).1 ≫ pullback.snd _ _) :=
    limit.lift_π _ _
  have h₀ : SSet.ι₀ ≫ H = A ≫ limMap F G f := by
    apply limit.hom_ext
    rintro ⟨n⟩
    simp only [Category.assoc, hH, ← comp_eval₀, limMap, lim_map, limMap_π]
    rw [← Category.assoc A, hA]
    simp only [Category.assoc, pullback.condition]
  have h₁ : SSet.ι₁ ≫ H = y := by
    apply limit.hom_ext
    rintro ⟨n⟩
    rw [Category.assoc, hH, ← comp_eval₁]
    exact (lifts n).2.2
  have hAx : i ≫ A = x ≫ pullback.fst (limMap F G f) (eval₀ (limit G)) := by
    apply limit.hom_ext
    rintro ⟨n⟩
    rw [Category.assoc, hA]
    simpa only [Category.assoc, stage_fst] using
      congrArg (fun r => r ≫ pullback.fst (f.app (op n)) (eval₀ (G.obj (op n)))) (lifts n).2.1
  have hHx : i ▷ Δ[1] ≫ H = uncurryR (x ≫ pullback.snd (limMap F G f) (eval₀ (limit G))) := by
    apply limit.hom_ext
    rintro ⟨n⟩
    rw [Category.assoc, hH, ← uncurryR_pre, ← Category.assoc, (lifts n).2.1,
      Category.assoc, stage_snd, ← Category.assoc, uncurryR_post]
  let l : E ⟶ MappingPath (limMap F G f) := pullback.lift A (curryR H)
    (by rw [comp_eval₀, uncurryR_curryR, h₀])
  refine ⟨⟨l, ?_, ?_⟩⟩
  · apply pullback.hom_ext
    · simpa only [l, Category.assoc, pullback.lift_fst] using hAx
    · simp only [l, Category.assoc, pullback.lift_snd]
      apply uncurryR_injective
      rw [uncurryR_pre, uncurryR_curryR, hHx]
  · change l ≫ pullback.snd _ _ ≫ eval₁ (limit G) = y
    rw [← Category.assoc, pullback.lift_snd, comp_eval₁, uncurryR_curryR, h₁]

include hF hG ha hb hf in

lemma homotopyEquivalence_limit : IsHomotopyEquivalence (limMap F G f) := by
  rw [← fac (limMap F G f)]
  exact KanLocal.heq_comp (left_heq _) (heq_of_rlp _ (path_limit_rlp F G f hF hG ha hb hf))

end
end Thomason.KanTower

end

end OAI
