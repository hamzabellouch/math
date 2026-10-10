import Mathlib
import OAI.GroupTheory.FiniteType.BinaryAlgebraPresentation

namespace OAI

noncomputable section
open scoped Pointwise
namespace SourceCorner
variable {R : Type} [Ring R] {e : R} (he : IsIdempotentElem e)
                                                                          
def val : he.Corner →ₙ+* R where
  toFun x := x.val
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

def unitEmbedding : he.Cornerˣ →* Rˣ := NonunitalCompression.units (val he)
lemma unitEmbedding_injective : Function.Injective (unitEmbedding he) :=
  NonunitalCompression.units_injective (val he) Subtype.val_injective
lemma unitEmbedding_val (u : he.Cornerˣ) :
    (unitEmbedding he u).val = 1-e+u.val.val := by
  change 1+(u.val.val-e)=1-e+u.val.val
  abel
lemma unitEmbedding_left (u : he.Cornerˣ) (x : he.Corner) :
    (unitEmbedding he u).val*x.val=(u.val*x).val := by
  change (1+(u.val.val-e))*x.val=u.val.val*x.val
  rw [add_mul,sub_mul,one_mul,(Subsemigroup.mem_corner_iff he).mp x.property |>.1]
  abel
lemma unitEmbedding_right (u : he.Cornerˣ) (x : he.Corner) :
    x.val*(unitEmbedding he u).val=(x*u.val).val := by
  change x.val*(1+(u.val.val-e))=x.val*u.val.val
  rw [mul_add,mul_sub,mul_one,(Subsemigroup.mem_corner_iff he).mp x.property |>.2]
  abel
end SourceCorner

namespace StageGeometry
open StageConstruction
variable {R Y W G : Type} [Ring R] [Nontrivial R] [Group W] [MulAction W Y]
  [Group G]
local instance : DecidableEq Y := Classical.decEq _
variable (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)
variable (e : R) (he : IsIdempotentElem e) (hne : e≠0)
variable (S T : Y → he.Corner)
variable (hTS : ∀ y y', T y*S y'=if y=y' then 1 else 0)
variable (ρ : W →* he.Cornerˣ) (ι : Q R →* W) (point : X R → Y)
variable (hρS : ∀ w y, (ρ w).val*S y=S (w • y))
variable (hTρ : ∀ w y, T y*(ρ w).val=T (w⁻¹ • y))
variable (hpoint : ∀ q x, ι q • point x=point (q • x))
variable (hφ : Function.Injective φ) (hρ : Function.Injective ρ)
variable (hι : Function.Injective ι) (hpt : Function.Injective point)
variable (F₂ : PairDiagrams (ZMod 2) ι point) (F₃ : PairDiagrams (ZMod 3) ι point)

include φ D hne hTS hρS hTρ hpoint hφ hρ hι hpt F₂ F₃

theorem action_of_corner_ring_data
    (A : Type) [Finite A] (π : FreeAlgebra (ZMod 2) A →+* R)
    (hπ : Function.Surjective π) (rel : Set (FreeAlgebra (ZMod 2) A))
    (hrel : rel.Finite) (hker : TwoSidedIdeal.ker π=TwoSidedIdeal.span rel)
    (g : G →* he.Cornerˣ) (hg : Function.Injective g) :
    ∃ (Λ : Type) (_ : Group Λ) (Z : Type) (_ : MulAction Λ Z),
      Countable Z ∧ Infinite Z ∧ FaithfulSMul Λ Z ∧
      (∃ ν : G →* Λ, Function.Injective ν) ∧
      (∀ n (x y : Fin n → Z), Function.Injective x → Function.Injective y →
        ∃ q : Λ, ∀ j, q • x j=y j) ∧
      SimpleFInftyOvergroups.HasTypeFInfty Λ ∧
      (∀ n (x : Fin n → Z),
        SimpleFInftyOvergroups.HasTypeFInfty
          (HomStabilizer.fixedTuple (MulAction.toPermHom Λ Z) x)) ∧
      (∀ s : Set Z, s.Finite →
        SimpleFInftyOvergroups.HasTypeFInfty (fixingSubgroup Λ s) ∧
        SimpleFInftyOvergroups.HasTypeFInfty (MulAction.stabilizer Λ s)) := by
  let ρ' := (SourceCorner.unitEmbedding he).comp ρ
  let g' := (SourceCorner.unitEmbedding he).comp g
  let S' : Y → R := fun y => (S y).val
  let T' : Y → R := fun y => (T y).val
  have hρ' : Function.Injective ρ' := (SourceCorner.unitEmbedding_injective he).comp hρ
  have hg' : Function.Injective g' := (SourceCorner.unitEmbedding_injective he).comp hg
  have hTS' : ∀ y y', T' y*S' y'=if y=y' then e else 0 := by
    intro y y'
    change (SourceCorner.val he) (T y)*(SourceCorner.val he) (S y') = _
    rw [← map_mul, hTS]
    split_ifs
    · rfl
    · exact map_zero (SourceCorner.val he)
  have hSe' : ∀ y, S' y*e=S' y := fun y =>
    ((Subsemigroup.mem_corner_iff he).mp (S y).property).2
  have hρS' : ∀ w y, (ρ' w).val*S' y=S' (w • y) := by
    intro w y
    exact (SourceCorner.unitEmbedding_left he (ρ w) (S y)).trans
      (congrArg Subtype.val (hρS w y))
  have hTρ' : ∀ w y, T' y*(ρ' w).val=T' (w⁻¹ • y) := by
    intro w y
    exact (SourceCorner.unitEmbedding_right he (ρ w) (T y)).trans
      (congrArg Subtype.val (hTρ w y))
  let := limitAction φ D S' ρ' ι point hρS' hpoint hφ hρ' hι
  refine ⟨LimitGroup φ D ρ' ι hφ hρ' hι,inferInstance,
    LimitPoints φ S' point,inferInstance,?_⟩
  obtain ⟨hc,hi,hf,hg,ht,hgeo,_hu,hs⟩ :=
    action_of_binary_ring_data φ D e S' T' hTS' hSe' ρ' ι point hρS' hTρ' hpoint
      hφ hρ' hι hpt hne F₂ F₃ A π hπ rel hrel hker g' hg'
  refine ⟨hc,hi,hf,hg,ht,hgeo,?_,hs⟩
  intro n x
  exact SimpleFInftyOvergroups.HasTypeFInfty.of_equiv
    (HomStabilizer.enumeratedSubset x (Set.range x) rfl).symm
    (hs (Set.range x) (Set.finite_range x)).1
end StageGeometry

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace AcyclicResolution
variable {k G : Type} [CommRing k] [Group G]

lemma H0_surjective {A B : Rep k G} (f : A ⟶ B) (hf : Function.Surjective f.hom) :
    Function.Surjective ((groupHomology.functor k G 0).map f) := by
  intro x
  obtain ⟨b,hb⟩ := (ModuleCat.epi_iff_surjective (groupHomology.H0π B)).mp inferInstance x
  obtain ⟨a,ha⟩ := hf b
  refine ⟨groupHomology.H0π A a,?_⟩
  have he := congrArg (fun l : ModuleCat.of k A.V ⟶ groupHomology B 0 => l a)
    (groupHomology.H0π_comp_map (MonoidHom.id G) f)
  exact he.trans ((congrArg (groupHomology.H0π B) ha).trans hb)

variable (Z C : ℕ → Rep.{0} k G)
  (f : ∀ i, Z (i+1) ⟶ C i) (g : ∀ i, C i ⟶ Z i)
  (w : ∀ i, f i ≫ g i = 0)

def row (i : ℕ) := ShortComplex.mk (f i) (g i) (w i)
def differential (i : ℕ) : C (i+1) ⟶ C i := g (i+1) ≫ f i
include w in
lemma differential_squared (i : ℕ) : differential Z C f g (i+1) ≫ differential Z C f g i = 0 := by
  simp only [differential,Category.assoc,← Category.assoc (f (i+1)),w,zero_comp,comp_zero]

def complexRow (i : ℕ) := ShortComplex.mk (differential Z C f g (i+1))
  (differential Z C f g i) (differential_squared Z C f g w i)

lemma H0_injective (i : ℕ) (hs : (row Z C f g w (i+1)).ShortExact)
    (he : ((complexRow Z C f g w i).map (groupHomology.functor k G 0)).Exact) : Function.Injective ((groupHomology.functor k G 0).map (f i)) := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro z hz
  obtain ⟨c,hc⟩ := H0_surjective (g (i+1))
    ((Rep.epi_iff_surjective _).mp hs.epi_g) z
  have hd : ((groupHomology.functor k G 0).map (differential Z C f g i)) c = 0 := by
    simpa only [differential,Functor.map_comp,ModuleCat.hom_comp,LinearMap.comp_apply,hc] using hz
  obtain ⟨b,hb⟩ := (ShortComplex.moduleCat_exact_iff _).mp he c hd
  change ((groupHomology.functor k G 0).map (differential Z C f g (i+1))) b = c at hb
  have hzero : ((groupHomology.functor k G 0).map (g (i+1)))
      (((groupHomology.functor k G 0).map (differential Z C f g (i+1))) b) = 0 := by
    change (((groupHomology.functor k G 0).map (differential Z C f g (i+1)) ≫
      (groupHomology.functor k G 0).map (g (i+1))) b) = 0
    rw [← Functor.map_comp]
    rw [show differential Z C f g (i+1) ≫ g (i+1) = 0 by
      simp only [differential,Category.assoc,w,comp_zero]]
    rw [Functor.map_zero]
    rfl
  rwa [hb,hc] at hzero

theorem vanishing (N : ℕ)
    (hs : ∀ i ≤ N+1, (row Z C f g w i).ShortExact)
    (he : ∀ i ≤ N, ((complexRow Z C f g w i).map (groupHomology.functor k G 0)).Exact)
    (ha : ∀ i ≤ N, ∀ d : ℕ, IsZero (groupHomology (C i) (d+1))) :
    ∀ d i, i+(d+1) ≤ N+1 → IsZero (groupHomology (Z i) (d+1)) := by
  intro d
  induction d with
  | zero =>
    intro i hi
    have hin : i ≤ N := by omega
    have hs0 := hs i (by omega)
    let δ := groupHomology.δ hs0 1 0 rfl
    let : Mono δ := groupHomology.mono_δ_of_isZero hs0 0 (ha i hin 0)
    have hfi := H0_injective Z C f g w i (hs (i+1) (by omega)) (he i hin)
    have hw := (groupHomology.mapShortComplex₁ hs0 (show 0+1=1 from rfl)).zero
    change δ ≫ (groupHomology.functor k G 0).map (f i) = 0 at hw
    have hz (z : groupHomology (Z i) 1) : δ z = 0 := by
      apply hfi
      have hh := congrArg (fun l : groupHomology (Z i) 1 ⟶ groupHomology (C i) 0 => l z) hw
      change ((groupHomology.functor k G 0).map (f i)) (δ z) = 0 at hh
      change (((groupHomology.functor k G 0).map (f i)).hom) (δ z) =
        (((groupHomology.functor k G 0).map (f i)).hom) 0
      rw [map_zero]
      exact hh
    let : Subsingleton (groupHomology (Z i) 1) := ⟨fun x y =>
      (ModuleCat.mono_iff_injective δ).mp inferInstance ((hz x).trans (hz y).symm)⟩
    exact ModuleCat.isZero_of_subsingleton _
  | succ d ih =>
    intro i hi
    have hin : i ≤ N := by omega
    have hs0 := hs i (by omega)
    let δ := groupHomology.δ hs0 (d+2) (d+1) rfl
    let : Mono δ := groupHomology.mono_δ_of_isZero hs0 (d+1) (ha i hin (d+1))
    exact @IsZero.of_mono _ _ _ _ _ δ ‹Mono δ› (ih (i+1) (by omega))
end AcyclicResolution

noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace AcyclicChain
variable {k G : Type} [CommRing k] [Group G]
variable (D : ℕ → Rep.{0} k G) (δ : ∀ i, D (i+1) ⟶ D i)
  (w : ∀ i, δ (i+1) ≫ δ i = 0)
def cycles : ℕ → Rep k G
  | 0 => D 0
  | i+1 => kernel (δ i)
def inclusion (i : ℕ) : cycles D δ (i+1) ⟶ D (i+1) := kernel.ι (δ i)
def projection : ∀ i, D (i+1) ⟶ cycles D δ i
  | 0 => δ 0
  | i+1 => kernel.lift (δ i) (δ (i+1)) (w i)
lemma row_zero (i : ℕ) : inclusion D δ i ≫ projection D δ w i = 0 := by
  cases i with
  | zero => exact kernel.condition _
  | succ i =>
    apply (cancel_mono (kernel.ι (δ i))).mp
    change (kernel.ι (δ (i+1)) ≫ kernel.lift (δ i) (δ (i+1)) (w i)) ≫
      kernel.ι (δ i) = _
    simp only [Category.assoc,kernel.lift_ι,kernel.condition]
    exact (zero_comp (f := kernel.ι (δ i))).symm
lemma differential (i : ℕ) : projection D δ w (i+1) ≫ inclusion D δ i = δ (i+1) :=
  kernel.lift_ι _ _ _

def row (i : ℕ) := ShortComplex.mk (inclusion D δ i) (projection D δ w i) (row_zero D δ w i)
def chainRow (i : ℕ) := ShortComplex.mk (δ (i+1)) (δ i) (w i)

lemma row_exact (i : ℕ) : (row D δ w i).Exact := by
  cases i with
  | zero => exact ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
  | succ i =>
    let E := ShortComplex.mk (kernel.ι (δ (i+1))) (δ (i+1)) (kernel.condition _)
    have hE : E.Exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
    let f : row D δ w (i+1) ⟶ E := {
      τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := kernel.ι (δ i)
      comm₁₂ := by
        simp only [row,inclusion,E]
        exact (Category.id_comp _).trans (Category.comp_id _).symm
      comm₂₃ := by
        simp only [row,projection,E]
        exact (Category.id_comp _).trans (kernel.lift_ι _ _ _).symm }
    let : Epi f.τ₁ := inferInstanceAs (Epi (𝟙 (kernel (δ (i+1)))))
    let : IsIso f.τ₂ := inferInstanceAs (IsIso (𝟙 (D (i+1+1))))
    let : Mono f.τ₃ := inferInstanceAs (Mono (kernel.ι (δ i)))
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono f).mpr hE

lemma row_shortExact (i : ℕ) [Epi (δ 0)]
    (he : ∀ j, j < i → (chainRow D δ w j).Exact) : (row D δ w i).ShortExact := by
  have hm : Mono (inclusion D δ i) := inferInstanceAs (Mono (kernel.ι (δ i)))
  have hp : Epi (projection D δ w i) := by
    cases i with
    | zero => exact inferInstanceAs (Epi (δ 0))
    | succ i => exact (he i (Nat.lt_succ_self i)).epi_kernelLift
  exact ShortComplex.ShortExact.mk' (row_exact D δ w i) hm hp

theorem vanishing (N : ℕ) [Epi (δ 0)]
    (he : ∀ i ≤ N, (chainRow D δ w i).Exact)
    (he0 : ∀ i ≤ N, ((chainRow D δ w (i+1)).map (groupHomology.functor k G 0)).Exact)
    (ha : ∀ i ≤ N, ∀ d : ℕ, IsZero (groupHomology (D (i+1)) (d+1))) :
    IsZero (groupHomology (D 0) (N+1)) := by
  apply AcyclicResolution.vanishing (cycles D δ) (fun i => D (i+1))
    (inclusion D δ) (projection D δ w) (row_zero D δ w) N ?_ ?_ ha N 0 (by omega)
  · intro i hi
    exact row_shortExact D δ w i (fun j hj => he j (by omega))
  · intro i hi
    convert he0 i hi using 1
    simp only [AcyclicResolution.complexRow,AcyclicResolution.differential,differential,chainRow]
end AcyclicChain

end

end OAI
