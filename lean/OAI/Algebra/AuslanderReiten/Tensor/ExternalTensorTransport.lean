import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorSemilinear
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorDifferential

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (h : A ≃ₐ[k] A) (j : B ≃ₐ[k] B)

abbrev tensorRestriction : ModuleCat.{u} (A ⊗[k] B) ⥤ ModuleCat.{u} (A ⊗[k] B) :=
  ModuleCat.restrictScalars (Algebra.TensorProduct.map h.toAlgHom j.toAlgHom).toRingHom

local notation "F" => tensorRestriction k A B h j

section Naturality
variable {M M' : ModuleCat.{u} A} {N N' : ModuleCat.{u} B}
variable (e : M →ₗ[k] M) (e' : M' →ₗ[k] M')
variable (f : N →ₗ[k] N) (f' : N' →ₗ[k] N')
variable (he : ∀ a x, e (a • x) = h a • e x)
variable (he' : ∀ a x, e' (a • x) = h a • e' x)
variable (hf : ∀ b x, f (b • x) = j b • f x)
variable (hf' : ∀ b x, f' (b • x) = j b • f' x)
variable (a : M ⟶ M') (b : N ⟶ N')
variable (ha : ∀ x, a.hom (e x) = e' (a.hom x))
variable (hb : ∀ x, b.hom (f x) = f' (b.hom x))

include ha hb in
theorem tensorSemilinear_natural :
    ModuleCat.ofHom (X := moduleObject k A B M N) (Y := (F).obj (moduleObject k A B M N))
      (tensorSemilinear k A B h j e f he hf) ≫
      (F).map
        (mapHom k A B a b) =
    mapHom k A B a b ≫ ModuleCat.ofHom
      (X := moduleObject k A B M' N') (Y := (F).obj (moduleObject k A B M' N'))
      (tensorSemilinear k A B h j e' f' he' hf') := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  let w : M ⊗[k] N := z
  change TensorProduct.map (a.hom.restrictScalars k) (b.hom.restrictScalars k)
      (TensorProduct.map e f w) =
    TensorProduct.map e' f' (TensorProduct.map (a.hom.restrictScalars k) (b.hom.restrictScalars k) w)
  induction w using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
    simp only [TensorProduct.map_tmul, LinearMap.restrictScalars_apply]
    exact congrArg₂ (fun s t => s ⊗ₜ[k] t) (ha x) (hb y)
end Naturality

variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)
variable (e : ∀ n, P.X n →ₗ[k] P.X n) (f : ∀ n, Q.X n →ₗ[k] Q.X n)
variable (he : ∀ n a x, e n (a • x) = h a • e n x)
variable (hf : ∀ n b x, f n (b • x) = j b • f n x)
def transportSummand (i j' : ℕ) : moduleObject k A B (P.X i) (Q.X j') ⟶
    (F).obj (moduleObject k A B (P.X i) (Q.X j')) :=
  ModuleCat.ofHom (X := moduleObject k A B (P.X i) (Q.X j'))
    (Y := (F).obj (moduleObject k A B (P.X i) (Q.X j')))
    (tensorSemilinear k A B h j (e i) (f j') (he i) (hf j'))

def transportTerm (n : ℕ) : (complex k A B P Q).X n ⟶
    (F).obj ((complex k A B P Q).X n) :=
  desc k A B P Q (fun i j' hij =>
    transportSummand k A B h j P Q e f he hf i j' ≫
      (F).map (inclusion k A B P Q i j' n hij))

@[reassoc] theorem inclusion_transportTerm (i j' n : ℕ) (hij : i+j'=n) :
    inclusion k A B P Q i j' n hij ≫ transportTerm k A B h j P Q e f he hf n =
      transportSummand k A B h j P Q e f he hf i j' ≫
        (F).map (inclusion k A B P Q i j' n hij) :=
  inclusion_desc k A B P Q _ i j' hij

variable (hdP : ∀ n x, (P.d (n+1) n).hom (e (n+1) x) = e n ((P.d (n+1) n).hom x))
variable (hdQ : ∀ n x, (Q.d (n+1) n).hom (f (n+1) x) = f n ((Q.d (n+1) n).hom x))

include hdP in
theorem horizontal_transport (i j' n : ℕ) (hij : i+j'=n+1) :
    horizontal k A B P Q i j' n ≫ transportTerm k A B h j P Q e f he hf n =
      transportSummand k A B h j P Q e f he hf i j' ≫
        (F).map (horizontal k A B P Q i j' n) := by
  cases i with
  | zero => simp only [horizontal_zero, Functor.map_zero, zero_comp, comp_zero]
  | succ i =>
    have hi : i+j'=n := by omega
    rw [horizontal_succ k A B P Q i j' n hi, Category.assoc,
      inclusion_transportTerm, Functor.map_comp, ← Category.assoc, ← Category.assoc]
    apply congrArg (fun t => t ≫ (F).map (inclusion k A B P Q i j' n hi))
    exact (tensorSemilinear_natural k A B h j (e (i+1)) (e i) (f j') (f j')
      (he (i+1)) (he i) (hf j') (hf j') (P.d (i+1) i) (𝟙 (Q.X j'))
      (hdP i) (fun _ => rfl)).symm

include hdQ in
theorem vertical_transport (i j' n : ℕ) (hij : i+j'=n+1) :
    vertical k A B P Q i j' n ≫ transportTerm k A B h j P Q e f he hf n =
      transportSummand k A B h j P Q e f he hf i j' ≫
        (F).map (vertical k A B P Q i j' n) := by
  cases j' with
  | zero => simp only [vertical_zero, Functor.map_zero, zero_comp, comp_zero]
  | succ j' =>
    have hi : i+j'=n := by omega
    rw [vertical_succ k A B P Q i j' n hi, Linear.units_smul_comp,
      Category.assoc, inclusion_transportTerm, Functor.map_units_smul,
      Linear.comp_units_smul, Functor.map_comp, ← Category.assoc, ← Category.assoc]
    apply congrArg (fun t => ((-1 : ℤˣ)^i) • t)
    apply congrArg (fun t => t ≫ (F).map (inclusion k A B P Q i j' n hi))
    exact (tensorSemilinear_natural k A B h j (e i) (e i) (f (j'+1)) (f j')
      (he i) (he i) (hf (j'+1)) (hf j') (𝟙 (P.X i)) (Q.d (j'+1) j')
      (fun _ => rfl) (hdQ j')).symm

def transportComplex : complex k A B P Q ⟶
    ((F).mapHomologicalComplex (.down ℕ)).obj (complex k A B P Q) where
  f n := transportTerm k A B h j P Q e f he hf n
  comm' n m hnm := by
    have hn : m+1=n := hnm
    subst n
    apply hom_ext k A B P Q
    intro i j' hij
    change inclusion k A B P Q i j' (m+1) hij ≫
      (transportTerm k A B h j P Q e f he hf (m+1) ≫
        (F).map ((complex k A B P Q).d (m+1) m)) =
      inclusion k A B P Q i j' (m+1) hij ≫
        ((complex k A B P Q).d (m+1) m ≫ transportTerm k A B h j P Q e f he hf m)
    rw [← Category.assoc, inclusion_transportTerm, Category.assoc,
      ← Functor.map_comp, inclusion_d, Functor.map_add, Preadditive.comp_add,
      ← Category.assoc, inclusion_d, Preadditive.add_comp,
      horizontal_transport k A B h j P Q e f he hf hdP i j' m hij,
      vertical_transport k A B h j P Q e f he hf hdQ i j' m hij]

end ArExplicit.ExternalTensor

end

end OAI
