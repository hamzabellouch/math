import Mathlib
import OAI.GroupTheory.FiniteType.TwistedBrinBasisCutBasis

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace EquivariantOrderChains
open OrderListChains OrderChainComplex
variable {G P : Type} [Group G] [Preorder P] [MulAction G P]
  [CovariantClass G P HSMul.hSMul LE.le]

def orderMap (g : G) : P →o P := ⟨(g • ·),fun _ _ h => smul_le_smul_left g h⟩

def simplexAct (n : ℕ) (g : G) (s : simplexSet P n) : simplexSet P n :=
  ⟨(g • s.val.1,s.val.2.map (g • ·)),s.property.1.map P (orderMap g),by
    simpa [degree] using s.property.2⟩

instance simplexAction (n : ℕ) : MulAction G (simplexSet P n) where
  smul := simplexAct n
  one_smul s := by
    apply Subtype.ext
    change ((1:G) • s.val.1,s.val.2.map ((1:G) • ·)) = s.val
    simp
  mul_smul g h s := by
    apply Subtype.ext
    change ((g*h) • s.val.1,s.val.2.map ((g*h) • ·)) =
      (g • (h • s.val.1),(s.val.2.map (h • ·)).map (g • ·))
    simp [mul_smul,List.map_map,Function.comp_def]

omit [Preorder P] in
lemma mapChain_id [Preorder P] (c : Chain P) : mapChain P id c = c := by
  have hh : mapChain P (id : P → P) = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro s r
    simp
  rw [hh,LinearMap.id_apply]
omit [Preorder P] in
lemma mapChain_comp [Preorder P] (f g : P → P) (c : Chain P) :
    mapChain P (f ∘ g) c = mapChain P f (mapChain P g c) := by
  have hh : mapChain P (f ∘ g) = (mapChain P f).comp (mapChain P g) := by
    apply Finsupp.lhom_ext
    intro s r
    simp [List.map_map]
  exact LinearMap.congr_fun hh c

def action (n : ℕ) (g : G) : chains P n →ₗ[ℤ] chains P n :=
  LinearMap.codRestrict _ ((mapChain P (g • ·)).comp (chains P n).subtype) (by
    intro c
    exact (mem_chains P).mpr ⟨OrderChains.map_mem P (orderMap g)
      ((mem_chains P).mp c.property).1,
      OrderChains.map_degree P (g • ·) ((mem_chains P).mp c.property).2⟩)

lemma action_val (n : ℕ) (g : G) (c : chains P n) :
    (action n g c).val = mapChain P (g • ·) c := rfl

def representation (n : ℕ) : Representation ℤ G (chains P n) where
  toFun := action n
  map_one' := by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    simp only [action_val,one_smul,Module.End.one_apply]
    exact mapChain_id c.val
  map_mul' := by
    intro g h
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    change mapChain P ((g*h) • ·) c.val = mapChain P (g • ·) (mapChain P (h • ·) c.val)
    simpa only [mul_smul,Function.comp_def] using mapChain_comp (g • ·) (h • ·) c.val

def object (n : ℕ) : Rep ℤ G := Rep.of (representation (G := G) (P := P) n)

def differential (n : ℕ) : object (G := G) (P := P) (n+1) ⟶ object (G := G) (P := P) n :=
  Rep.ofHom ⟨d P n,by
    intro g
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact boundary_mapChain P (g • ·) c.val⟩

def augmentation : object (G := G) (P := P) 0 ⟶ Rep.trivial ℤ G ℤ :=
  Rep.ofHom ⟨aug P,by
    intro g
    apply LinearMap.ext
    intro c
    exact augmentation_mapChain P (g • ·) c.val⟩

lemma differential_squared (n : ℕ) :
    differential (G := G) (P := P) (n+1) ≫ differential n = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  exact d_d P n
lemma differential_aug : differential (G := G) (P := P) 0 ≫ augmentation = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  exact d_aug P

attribute [-instance] AddCommGroup.toIntModule
lemma exact_aug (he : OrderChains.ExactIn P 0) :
    (ShortComplex.mk (differential (G := G) 0) augmentation (differential_aug (P := P))).Exact := by
  rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep ℤ G) (ModuleCat ℤ)),
    ShortComplex.moduleCat_exact_iff]
  exact fun x hx => (OrderChainComplex.exact_aug P he x).mp hx
lemma exact_succ (n : ℕ) (he : OrderChains.ExactIn P (n+1)) :
    (ShortComplex.mk (differential (G := G) (n+1)) (differential n)
      (differential_squared (P := P) n)).Exact := by
  rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep ℤ G) (ModuleCat ℤ)),
    ShortComplex.moduleCat_exact_iff]
  exact fun x hx => (OrderChainComplex.exact_succ P n he x).mp hx
instance [Nonempty P] : Epi (augmentation (G := G) (P := P)) :=
  (Rep.epi_iff_surjective _).mpr (aug_surjective P)
attribute [instance] AddCommGroup.toIntModule

lemma basisIso_single (n : ℕ) (s : simplexSet P n) (r : ℤ) :
    basisIso P n ⟨Finsupp.single s.val r,Finsupp.single_mem_supported ℤ r s.property⟩ =
      Finsupp.single s r := by
  apply (basisIso P n).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  apply Subtype.ext
  exact (Finsupp.supportedEquivFinsupp_symm_single _ s r).symm

lemma basisIso_action (n : ℕ) (g : G) (c : chains P n) :
    basisIso P n (action n g c) =
      Finsupp.lmapDomain ℤ ℤ (fun s : simplexSet P n => g • s) (basisIso P n c) := by
  classical
  obtain ⟨z,rfl⟩ := (basisIso P n).symm.surjective c
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add,hx,hy]
  | single s r =>
    have he : (basisIso P n).symm (Finsupp.single s r) =
        ⟨Finsupp.single s.val r,Finsupp.single_mem_supported ℤ r s.property⟩ := by
      apply (basisIso P n).injective
      rw [LinearEquiv.apply_symm_apply,basisIso_single]
    rw [he,basisIso_single]
    have ha : action n g ⟨Finsupp.single s.val r,Finsupp.single_mem_supported ℤ r s.property⟩ =
        ⟨Finsupp.single (g • s).val r,Finsupp.single_mem_supported ℤ r (g • s).property⟩ := by
      apply Subtype.ext
      exact mapChain_single P (g • ·) s.val r
    rw [ha,basisIso_single]
    simp

variable (G) in
def permutationRepresentation (V : Type) [MulAction G V] : Representation ℤ G (V →₀ ℤ) where
  toFun g := Finsupp.lmapDomain ℤ ℤ (g • ·)
  map_one' := by apply Finsupp.lhom_ext; intro v r; simp
  map_mul' g h := by apply Finsupp.lhom_ext; intro v r; simp [mul_smul]

variable (G) in
def permutationObject (V : Type) [MulAction G V] : Rep ℤ G := Rep.of (permutationRepresentation G V)

def permutationIso (n : ℕ) : object (G := G) (P := P) n ≅
    permutationObject G (simplexSet P n) :=
  Rep.mkIso (Representation.Equiv.mk (basisIso P n) (fun g => by
    apply LinearMap.ext
    intro c
    exact basisIso_action n g c))
end EquivariantOrderChains

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
namespace OrderBrown
attribute [-instance] AddCommGroup.toIntModule
open OrderChainComplex EquivariantOrderChains
variable {G P I : Type} [Group G] [Preorder P] [MulAction G P]
  [CovariantClass G P HSMul.hSMul LE.le] [Nonempty P]

def permIso (n : ℕ) : object (G := G) (P := P) n ≅ OrbitBrown.perm G (simplexSet P n) :=
  permutationIso n ≪≫ Rep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℤ _) (fun g => by
    apply Finsupp.lhom_ext
    intro s r
    change Finsupp.mapDomain (g • ·) (Finsupp.single s r) =
      FunctionalTree.diagonalAction (Rep.trivial ℤ G ℤ) g (Finsupp.single s r)
    rw [Finsupp.mapDomain_single, FunctionalTree.diagonalAction_single]
    rfl))

def C : ℕ → Rep ℤ G
  | 0 => Rep.trivial ℤ G ℤ
  | n+1 => object (G := G) (P := P) n
def d : (n : ℕ) → C (G := G) (P := P) (n+1) ⟶ C (G := G) (P := P) n
  | 0 => augmentation
  | n+1 => differential n
omit [Nonempty P] in
lemma w [Nonempty P] (n : ℕ) : d (G := G) (P := P) (n+1) ≫ d n = 0 := by
  cases n with
  | zero => exact differential_aug
  | succ n => exact differential_squared n
instance : Epi (d (G := G) (P := P) 0) := inferInstanceAs (Epi (augmentation (G := G) (P := P)))

theorem vanishing (N : ℕ)
    (he : ∀ i ≤ N+1, OrderChains.ExactIn P i)
    (hf : ∀ n : ℕ, Finite (OrbitCoefficients.Orbits (G := G) (simplexSet P n)))
    (hfg : ∀ n : ℕ, ∀ s : simplexSet P n, Group.FG (MulAction.stabilizer G s))
    (hz : ∀ n : ℕ, ∀ s : simplexSet P n, ∀ (J : Type) (j : ℕ),
      IsZero (groupHomology (RegularProductR.rep ℤ (MulAction.stabilizer G s) J) (j+1))) :
    IsZero (groupHomology (RegularProductR.rep ℤ G I) (N+1)) := by
  apply ProductBrown.regularProductsOfComplex (C (G := G) (P := P)) d w (Iso.refl _) N
  · intro i hi
    cases i with
    | zero => exact EquivariantOrderChains.exact_aug (he 0 hi)
    | succ n => exact EquivariantOrderChains.exact_succ n (he (n+1) hi)
  · intro i hi hlo
    cases i with
    | zero => omega
    | succ n =>
      let := hf n
      apply OrbitBrown.coordinates_iso (permIso (G := G) (P := P) n).symm
      apply OrbitBrown.coordinates_perm G (simplexSet P n)
      intro s
      let := hfg n s
      exact OrbitModule.trivial_presentation_of_fg _
  · intro i hi n
    let := hf i
    apply IsZero.of_iso _ ((groupHomology.functor ℤ G (n+1)).mapIso
      ((tensorLeft (RegularProductR.rep ℤ G I)).mapIso (permIso (G := G) (P := P) i)))
    exact OrbitBrown.acyclic_perm G (simplexSet P i) (hz i) n
end OrderBrown

end

end OAI
