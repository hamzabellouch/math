import OAI.Algebra.Finitistic.Bar.TotalMap
import Mathlib.Algebra.Category.ModuleCat.Products

namespace OAI
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open scoped DirectSum
noncomputable section
namespace DerivedBar.RecursiveTotal
universe u
variable {D : Type u} [Ring D]
local notation "c" => ComplexShape.down ℕ

abbrev Diagonal (n : ℕ) := {p : ℕ × ℕ // p.1+p.2=n}

/-- Every index records every bar length and the final input degree. -/
def Index : ℕ → ℕ → Type
  | 0, _ => Unit
  | r+1, n => (p : Diagonal n) × Index r p.val.2

instance indexFinite (r n : ℕ) : Finite (Index r n) := by
  induction r generalizing n with
  | zero => exact inferInstanceAs (Finite Unit)
  | succ r ih =>
    have : Finite (Diagonal n) := DerivedBar.finiteTotalDiagonal n
    have (degree : ℕ) : Finite (Index r degree) := ih degree
    exact inferInstanceAs (Finite ((p : Diagonal n) × Index r p.val.2))

local instance (r n : ℕ) : DecidableEq (Index r n) := Classical.decEq _

variable (B : ℕ → ModuleCat.{u} D ⥤ ChainComplex (ModuleCat.{u} D) ℕ)
  [∀ r, (B r).Additive]

abbrev degreeFunctor (r i : ℕ) : ModuleCat.{u} D ⥤ ModuleCat.{u} D :=
  B r ⋙ HomologicalComplex.eval _ c i

variable (Z : ChainComplex (ModuleCat.{u} D) ℕ)

def bicomplex (r : ℕ) (W : ChainComplex (ModuleCat.{u} D) ℕ) :
    HomologicalComplex₂ (ModuleCat.{u} D) c c :=
  HomologicalComplex₂.flip (((B r).mapHomologicalComplex c).obj W)

/-- Successively totalize the given module-to-chain functors. -/
def iter : ℕ → ChainComplex (ModuleCat.{u} D) ℕ
  | 0 => Z
  | r+1 => (bicomplex B r (iter r)).total c

/-- Literal nested terms, before any coproducts are taken. -/
def summand : (r n : ℕ) → Index r n → ModuleCat.{u} D
  | 0, n, _ => Z.X n
  | r+1, _, ⟨p,t⟩ => (degreeFunctor B r p.val.1).obj (summand r p.val.2 t)

/-- Insert a literal nested term into the actual recursive total. -/
def inclusion : (r n : ℕ) → (t : Index r n) → summand B Z r n t ⟶ (iter B Z r).X n
  | 0, _, _ => 𝟙 _
  | r+1, n, ⟨p,t⟩ =>
    (degreeFunctor B r p.val.1).map (inclusion r p.val.2 t) ≫
      (bicomplex B r (iter B Z r)).ιTotal c p.val.1 p.val.2 n p.property

/-- A map out of an additive image of the recursive total is specified on all
literal nested terms. Only finite diagonal coproducts are distributed. -/
def desc : (r : ℕ) → (G : ModuleCat.{u} D ⥤ ModuleCat.{u} D) → [G.Additive] →
    {n : ℕ} → {Y : ModuleCat.{u} D} →
    (∀ t : Index r n, G.obj (summand B Z r n t) ⟶ Y) →
    (G.obj ((iter B Z r).X n) ⟶ Y)
  | 0, _, _, _, _, f => f ()
  | r+1, G, _, _, _, f => totalMapDesc G (bicomplex B r (iter B Z r))
      (fun i q h => desc r (degreeFunctor B r i ⋙ G) (fun t => f ⟨⟨⟨i,q⟩,h⟩,t⟩))

@[reassoc (attr := simp)]
theorem inclusion_desc (r : ℕ) (G : ModuleCat.{u} D ⥤ ModuleCat.{u} D) [G.Additive]
    {n : ℕ} {Y : ModuleCat.{u} D}
    (f : ∀ t : Index r n, G.obj (summand B Z r n t) ⟶ Y) (t : Index r n) :
    G.map (inclusion B Z r n t) ≫ desc B Z r G f = f t := by
  induction r generalizing G n with
  | zero =>
    cases t
    change G.map (𝟙 (Z.X n)) ≫ f () = f ()
    erw [G.map_id, Category.id_comp]
  | succ r ih =>
    rcases t with ⟨⟨⟨i,q⟩,h⟩,t⟩
    simp only [inclusion, desc]
    erw [Functor.map_comp, Category.assoc, ι_totalMapDesc]
    exact ih (degreeFunctor B r i ⋙ G) _ t

theorem hom_ext (r : ℕ) (G : ModuleCat.{u} D ⥤ ModuleCat.{u} D) [G.Additive]
    {n : ℕ} {Y : ModuleCat.{u} D}
    {f g : G.obj ((iter B Z r).X n) ⟶ Y}
    (h : ∀ t : Index r n, G.map (inclusion B Z r n t) ≫ f =
      G.map (inclusion B Z r n t) ≫ g) : f=g := by
  induction r generalizing G n with
  | zero =>
    have hh := h ()
    change G.map (𝟙 (Z.X n)) ≫ f = G.map (𝟙 (Z.X n)) ≫ g at hh
    erw [G.map_id, Category.id_comp, Category.id_comp] at hh
    exact hh
  | succ r ih =>
    apply totalMap_hom_ext G (bicomplex B r (iter B Z r))
    intro i q hq
    apply ih (degreeFunctor B r i ⋙ G)
    intro t
    have hh := h ⟨⟨⟨i,q⟩,hq⟩,t⟩
    dsimp only [inclusion] at hh
    erw [Functor.map_comp] at hh
    simpa only [Category.assoc, Functor.comp_map] using! hh

/-- Actual degreewise flattening into an ordinary direct sum of nested tensors.
The universal property is proved for the recursive totals, not assumed. -/
def flattenIso (r n : ℕ) (G : ModuleCat.{u} D ⥤ ModuleCat.{u} D) [G.Additive] :
    G.obj ((iter B Z r).X n) ≅
      ModuleCat.of D (⨁ t : Index r n, G.obj (summand B Z r n t)) where
  hom := desc B Z r G (fun t => ModuleCat.ofHom (DirectSum.lof D (Index r n) (fun t => G.obj (summand B Z r n t)) t))
  inv := ModuleCat.ofHom (DirectSum.toModule D _ _
    (fun t => (G.map (inclusion B Z r n t)).hom))
  hom_inv_id := by
    apply hom_ext B Z r G
    intro t
    simp only [inclusion_desc_assoc, Category.comp_id]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
      DirectSum.toModule_lof]
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply DirectSum.linearMap_ext
    intro t
    apply LinearMap.ext
    intro v
    have h := congrArg (fun f => f.hom v)
      (inclusion_desc B Z r G
        (fun t => ModuleCat.ofHom (DirectSum.lof D (Index r n) (fun t => G.obj (summand B Z r n t)) t)) t)
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
      DirectSum.toModule_lof, ModuleCat.hom_id, LinearMap.id_apply] using h
end DerivedBar.RecursiveTotal

end

end OAI
